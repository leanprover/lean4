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
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_uv_tcp_new();
uint8_t lean_bool_to_int8(uint8_t);
lean_object* l_Int_toNat(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_uv_tcp_keepalive(lean_object*, uint8_t, uint32_t);
lean_object* lean_uv_tcp_getsockname(lean_object*);
lean_object* lean_uv_tcp_send(lean_object*, lean_object*);
lean_object* lean_uv_tcp_try_accept(lean_object*);
lean_object* l_IO_ofExcept___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_uv_tcp_cancel_recv(lean_object*);
lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_tcp_cancel_accept(lean_object*);
lean_object* lean_uv_tcp_shutdown(lean_object*);
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_accept(lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_tcp_getpeername(lean_object*);
lean_object* lean_uv_tcp_wait_readable(lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* lean_uv_tcp_connect(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_TCP_Socket_Client_recvSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___closed__0_value;
static const lean_closure_object l_Std_Async_TCP_Socket_Client_recvSelector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_mk(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_2_) == 0)
{
lean_object* v_a_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_10_; 
v_a_3_ = lean_ctor_get(v___x_2_, 0);
v_isSharedCheck_10_ = !lean_is_exclusive(v___x_2_);
if (v_isSharedCheck_10_ == 0)
{
v___x_5_ = v___x_2_;
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_a_3_);
lean_dec(v___x_2_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_8_; 
if (v_isShared_6_ == 0)
{
v___x_8_ = v___x_5_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_9_; 
v_reuseFailAlloc_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_9_, 0, v_a_3_);
v___x_8_ = v_reuseFailAlloc_9_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
return v___x_8_;
}
}
}
else
{
lean_object* v_a_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_18_; 
v_a_11_ = lean_ctor_get(v___x_2_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_2_);
if (v_isSharedCheck_18_ == 0)
{
v___x_13_ = v___x_2_;
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_a_11_);
lean_dec(v___x_2_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_16_; 
if (v_isShared_14_ == 0)
{
v___x_16_ = v___x_13_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_a_11_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_mk___boxed(lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Async_TCP_Socket_Server_mk();
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_bind(lean_object* v_s_21_, lean_object* v_addr_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_uv_tcp_bind(v_s_21_, v_addr_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_bind___boxed(lean_object* v_s_25_, lean_object* v_addr_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Std_Async_TCP_Socket_Server_bind(v_s_25_, v_addr_26_);
lean_dec_ref(v_addr_26_);
lean_dec(v_s_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_listen(lean_object* v_s_29_, uint32_t v_backlog_30_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_uv_tcp_listen(v_s_29_, v_backlog_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_listen___boxed(lean_object* v_s_33_, lean_object* v_backlog_34_, lean_object* v_a_35_){
_start:
{
uint32_t v_backlog_boxed_36_; lean_object* v_res_37_; 
v_backlog_boxed_36_ = lean_unbox_uint32(v_backlog_34_);
lean_dec(v_backlog_34_);
v_res_37_ = l_Std_Async_TCP_Socket_Server_listen(v_s_33_, v_backlog_boxed_36_);
lean_dec(v_s_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__0(lean_object* v_native_38_){
_start:
{
lean_inc(v_native_38_);
return v_native_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__0___boxed(lean_object* v_native_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Async_TCP_Socket_Server_accept___lam__0(v_native_39_);
lean_dec(v_native_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__1(lean_object* v___x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_mk_io_user_error(v___x_41_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
else
{
lean_object* v_val_45_; 
lean_dec_ref(v___x_41_);
v_val_45_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_val_45_);
return v_val_45_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__1___boxed(lean_object* v___x_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_Async_TCP_Socket_Server_accept___lam__1(v___x_46_, v_x_47_);
lean_dec(v_x_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__2(lean_object* v___f_49_, lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_60_; 
lean_dec_ref(v___f_49_);
v_a_52_ = lean_ctor_get(v_x_50_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_60_ == 0)
{
v___x_54_ = v_x_50_;
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v_x_50_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_59_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; 
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
}
else
{
lean_object* v_a_61_; 
v_a_61_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_a_61_);
lean_dec_ref(v_x_50_);
if (lean_obj_tag(v_a_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_70_; 
lean_dec_ref(v___f_49_);
v_a_62_ = lean_ctor_get(v_a_61_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_a_61_);
if (v_isSharedCheck_70_ == 0)
{
v___x_64_ = v_a_61_;
v_isShared_65_ = v_isSharedCheck_70_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v_a_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_70_;
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
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_69_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
}
else
{
lean_object* v_a_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_a_71_ = lean_ctor_get(v_a_61_, 0);
lean_inc(v_a_71_);
lean_dec_ref(v_a_61_);
v___x_72_ = lean_io_promise_result_opt(v_a_71_);
lean_dec(v_a_71_);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = 0;
v___x_75_ = lean_task_map(v___f_49_, v___x_72_, v___x_73_, v___x_74_);
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__2___boxed(lean_object* v___f_77_, lean_object* v_x_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_Async_TCP_Socket_Server_accept___lam__2(v___f_77_, v_x_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept(lean_object* v_s_89_){
_start:
{
lean_object* v___y_92_; lean_object* v___f_94_; lean_object* v_val_96_; lean_object* v___x_129_; 
v___f_94_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_accept___closed__3));
v___x_129_ = lean_uv_tcp_accept(v_s_89_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set_tag(v___x_132_, 1);
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
v_val_96_ = v___x_135_;
goto v___jp_95_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_129_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_129_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 0);
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
v_val_96_ = v___x_143_;
goto v___jp_95_;
}
}
}
v___jp_91_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___y_92_);
return v___x_93_;
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; 
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_val_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = 0;
v___x_101_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_99_, v___x_100_, v___x_98_, v___f_94_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref(v___x_101_);
if (lean_obj_tag(v_a_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
v_a_103_ = lean_ctor_get(v_a_102_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v_a_102_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v_a_102_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v_a_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
v___y_92_ = v___x_108_;
goto v___jp_91_;
}
}
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_111_ = lean_ctor_get(v_a_102_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_a_102_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v_a_102_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v_a_102_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
v___y_92_ = v___x_116_;
goto v___jp_91_;
}
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_128_; 
v_a_119_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_128_ == 0)
{
v___x_121_ = v___x_101_;
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_101_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_123_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_accept___closed__4));
v___x_124_ = lean_task_map(v___x_123_, v_a_119_, v___x_99_, v___x_100_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_124_);
v___x_126_ = v___x_121_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___boxed(lean_object* v_s_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_Async_TCP_Socket_Server_accept(v_s_146_);
lean_dec(v_s_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_tryAccept(lean_object* v_s_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_uv_tcp_try_accept(v_s_150_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
lean_dec_ref(v___x_152_);
v___x_154_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_tryAccept___closed__0));
v___x_155_ = l_IO_ofExcept___redArg(v___x_154_, v_a_153_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_175_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_175_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_175_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_175_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
if (lean_obj_tag(v_a_156_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_box(0);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
lean_object* v_val_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_174_; 
v_val_164_ = lean_ctor_get(v_a_156_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_a_156_);
if (v_isSharedCheck_174_ == 0)
{
v___x_166_ = v_a_156_;
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_val_164_);
lean_dec(v_a_156_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_val_164_);
v___x_169_ = v_reuseFailAlloc_173_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_169_);
v___x_171_ = v___x_158_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_a_176_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_155_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_155_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_152_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_152_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
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
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_tryAccept___boxed(lean_object* v_s_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Async_TCP_Socket_Server_tryAccept(v_s_192_);
lean_dec(v_s_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(lean_object* v_e_195_){
_start:
{
if (lean_obj_tag(v_e_195_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_206_; 
v_a_197_ = lean_ctor_get(v_e_195_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_e_195_);
if (v_isSharedCheck_206_ == 0)
{
v___x_199_ = v_e_195_;
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v_e_195_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_201_ = lean_io_error_to_string(v_a_197_);
v___x_202_ = lean_mk_io_user_error(v___x_201_);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 1);
lean_ctor_set(v___x_199_, 0, v___x_202_);
v___x_204_ = v___x_199_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_a_207_ = lean_ctor_get(v_e_195_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_e_195_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v_e_195_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v_e_195_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 0);
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg___boxed(lean_object* v_e_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_e_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(lean_object* v_00_u03b1_218_, lean_object* v_e_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_e_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___boxed(lean_object* v_00_u03b1_222_, lean_object* v_e_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(v_00_u03b1_222_, v_e_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(lean_object* v_val_226_, lean_object* v_w_227_, lean_object* v_lose_228_){
_start:
{
lean_object* v_finished_230_; lean_object* v_promise_231_; lean_object* v___x_232_; uint8_t v___y_234_; uint8_t v___x_260_; 
v_finished_230_ = lean_ctor_get(v_w_227_, 0);
v_promise_231_ = lean_ctor_get(v_w_227_, 1);
v___x_232_ = lean_st_ref_take(v_finished_230_);
v___x_260_ = lean_unbox(v___x_232_);
lean_dec(v___x_232_);
if (v___x_260_ == 0)
{
uint8_t v___x_261_; 
v___x_261_ = 1;
v___y_234_ = v___x_261_;
goto v___jp_233_;
}
else
{
uint8_t v___x_262_; 
v___x_262_ = 0;
v___y_234_ = v___x_262_;
goto v___jp_233_;
}
v___jp_233_:
{
uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = 1;
v___x_236_ = lean_box(v___x_235_);
v___x_237_ = lean_st_ref_set(v_finished_230_, v___x_236_);
if (v___y_234_ == 0)
{
lean_object* v___x_238_; 
lean_dec_ref(v_val_226_);
v___x_238_ = lean_apply_1(v_lose_228_, lean_box(0));
return v___x_238_;
}
else
{
lean_object* v___x_239_; 
lean_dec_ref(v_lose_228_);
v___x_239_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_val_226_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_249_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_249_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v_a_240_);
v___x_245_ = lean_io_promise_resolve(v___x_244_, v_promise_231_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_245_);
v___x_247_ = v___x_242_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_259_; 
v_a_250_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_259_ == 0)
{
v___x_252_ = v___x_239_;
v_isShared_253_ = v_isSharedCheck_259_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_239_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_259_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_a_250_);
v___x_255_ = lean_io_promise_resolve(v___x_254_, v_promise_231_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 0);
lean_ctor_set(v___x_252_, 0, v___x_255_);
v___x_257_ = v___x_252_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___boxed(lean_object* v_val_263_, lean_object* v_w_264_, lean_object* v_lose_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(v_val_263_, v_w_264_, v_lose_265_);
lean_dec_ref(v_w_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(lean_object* v_s_268_){
_start:
{
lean_object* v_val_271_; lean_object* v_a_274_; lean_object* v___x_276_; 
v___x_276_ = lean_uv_tcp_try_accept(v_s_268_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_276_);
v___x_278_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_a_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_297_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_297_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_297_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_297_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_a_284_; 
if (lean_obj_tag(v_a_279_) == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
v_a_284_ = v___x_288_;
goto v___jp_283_;
}
else
{
lean_object* v_val_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_val_289_ = lean_ctor_get(v_a_279_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_a_279_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v_a_279_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_val_289_);
lean_dec(v_a_279_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_val_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
v_a_284_ = v___x_294_;
goto v___jp_283_;
}
}
}
v___jp_283_:
{
lean_object* v___x_286_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 1);
lean_ctor_set(v___x_281_, 0, v_a_284_);
v___x_286_ = v___x_281_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
v_val_271_ = v___x_286_;
goto v___jp_270_;
}
}
}
}
else
{
lean_object* v_a_298_; 
v_a_298_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_298_);
lean_dec_ref(v___x_278_);
v_a_274_ = v_a_298_;
goto v___jp_273_;
}
}
else
{
lean_object* v_a_299_; 
v_a_299_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_299_);
lean_dec_ref(v___x_276_);
v_a_274_ = v_a_299_;
goto v___jp_273_;
}
v___jp_270_:
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v_val_271_);
return v___x_272_;
}
v___jp_273_:
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v_a_274_);
v_val_271_ = v___x_275_;
goto v___jp_270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed(lean_object* v_s_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(v_s_300_);
lean_dec(v_s_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(lean_object* v___x_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed(lean_object* v___x_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(v___x_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(lean_object* v_waiter_311_, lean_object* v_res_312_){
_start:
{
if (lean_obj_tag(v_res_312_) == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v_val_316_; lean_object* v___f_317_; lean_object* v___x_318_; 
v_val_316_ = lean_ctor_get(v_res_312_, 0);
lean_inc(v_val_316_);
lean_dec_ref(v_res_312_);
v___f_317_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0));
v___x_318_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(v_val_316_, v_waiter_311_, v___f_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed(lean_object* v_waiter_319_, lean_object* v_res_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(v_waiter_319_, v_res_320_);
lean_dec_ref(v_waiter_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(lean_object* v___f_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_val_327_; 
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v___f_323_);
v_a_329_ = lean_ctor_get(v_x_324_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_337_ == 0)
{
v___x_331_ = v_x_324_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v_x_324_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_336_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_354_; 
v_a_338_ = lean_ctor_get(v_x_324_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_354_ == 0)
{
v___x_340_ = v_x_324_;
v_isShared_341_ = v_isSharedCheck_354_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v_x_324_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_354_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; 
v___x_342_ = lean_io_promise_result_opt(v_a_338_);
lean_dec(v_a_338_);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = 0;
v___x_345_ = l_EIO_chainTask___redArg(v___x_342_, v___f_323_, v___x_343_, v___x_344_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref(v___x_345_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v_a_346_);
v___x_348_ = v___x_340_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
v_val_327_ = v___x_348_;
goto v___jp_326_;
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; 
v_a_350_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_350_);
lean_dec_ref(v___x_345_);
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 0);
lean_ctor_set(v___x_340_, 0, v_a_350_);
v___x_352_ = v___x_340_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
v_val_327_ = v___x_352_;
goto v___jp_326_;
}
}
}
}
v___jp_326_:
{
lean_object* v___x_328_; 
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v_val_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed(lean_object* v___f_355_, lean_object* v_x_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(v___f_355_, v_x_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(lean_object* v_s_359_, lean_object* v_waiter_360_){
_start:
{
lean_object* v___f_362_; lean_object* v___f_363_; lean_object* v_val_365_; lean_object* v___x_370_; 
v___f_362_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_362_, 0, v_waiter_360_);
v___f_363_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_363_, 0, v___f_362_);
v___x_370_ = lean_uv_tcp_accept(v_s_359_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 1);
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v_val_365_ = v___x_376_;
goto v___jp_364_;
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_a_379_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_370_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_370_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 0);
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
v_val_365_ = v___x_384_;
goto v___jp_364_;
}
}
}
v___jp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; 
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_val_365_);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = 0;
v___x_369_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_367_, v___x_368_, v___x_366_, v___f_363_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed(lean_object* v_s_387_, lean_object* v_waiter_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(v_s_387_, v_waiter_388_);
lean_dec(v_s_387_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(lean_object* v_s_391_){
_start:
{
lean_object* v_val_394_; lean_object* v___x_396_; 
v___x_396_ = lean_uv_tcp_cancel_accept(v_s_391_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 1);
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
v_val_394_ = v___x_402_;
goto v___jp_393_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_396_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_396_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
v_val_394_ = v___x_410_;
goto v___jp_393_;
}
}
}
v___jp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v_val_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed(lean_object* v_s_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(v_s_413_);
lean_dec(v_s_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector(lean_object* v_s_416_){
_start:
{
lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___x_420_; 
lean_inc_n(v_s_416_, 2);
v___f_417_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed), 2, 1);
lean_closure_set(v___f_417_, 0, v_s_416_);
v___f_418_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_418_, 0, v_s_416_);
v___f_419_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed), 2, 1);
lean_closure_set(v___f_419_, 0, v_s_416_);
v___x_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_420_, 0, v___f_417_);
lean_ctor_set(v___x_420_, 1, v___f_418_);
lean_ctor_set(v___x_420_, 2, v___f_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_getSockName(lean_object* v_s_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_uv_tcp_getsockname(v_s_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_getSockName___boxed(lean_object* v_s_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_Async_TCP_Socket_Server_getSockName(v_s_424_);
lean_dec(v_s_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_noDelay(lean_object* v_s_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_uv_tcp_nodelay(v_s_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_noDelay___boxed(lean_object* v_s_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_Async_TCP_Socket_Server_noDelay(v_s_430_);
lean_dec(v_s_430_);
return v_res_432_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10));
v___x_460_ = l_Lean_mkAtom(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12);
v___x_462_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_463_ = lean_array_push(v___x_462_, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16));
v___x_475_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_476_ = lean_array_push(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_477_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17);
v___x_478_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15));
v___x_479_ = lean_box(2);
v___x_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
lean_ctor_set(v___x_480_, 2, v___x_477_);
return v___x_480_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18);
v___x_482_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13);
v___x_483_ = lean_array_push(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_484_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19);
v___x_485_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11));
v___x_486_ = lean_box(2);
v___x_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_484_);
return v___x_487_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20);
v___x_489_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_490_ = lean_array_push(v___x_489_, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21);
v___x_492_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9));
v___x_493_ = lean_box(2);
v___x_494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_491_);
return v___x_494_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22);
v___x_496_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_497_ = lean_array_push(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23);
v___x_499_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7));
v___x_500_ = lean_box(2);
v___x_501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
lean_ctor_set(v___x_501_, 2, v___x_498_);
return v___x_501_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24);
v___x_503_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_504_ = lean_array_push(v___x_503_, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25);
v___x_506_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4));
v___x_507_ = lean_box(2);
v___x_508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v___x_506_);
lean_ctor_set(v___x_508_, 2, v___x_505_);
return v___x_508_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1(void){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg(lean_object* v_s_510_, uint8_t v_enable_511_, lean_object* v_delay_512_){
_start:
{
uint8_t v___x_514_; lean_object* v___x_515_; uint32_t v___x_516_; lean_object* v___x_517_; 
v___x_514_ = lean_bool_to_int8(v_enable_511_);
v___x_515_ = l_Int_toNat(v_delay_512_);
v___x_516_ = lean_uint32_of_nat(v___x_515_);
lean_dec(v___x_515_);
v___x_517_ = lean_uv_tcp_keepalive(v_s_510_, v___x_514_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object* v_s_518_, lean_object* v_enable_519_, lean_object* v_delay_520_, lean_object* v_a_521_){
_start:
{
uint8_t v_enable_boxed_522_; lean_object* v_res_523_; 
v_enable_boxed_522_ = lean_unbox(v_enable_519_);
v_res_523_ = l_Std_Async_TCP_Socket_Server_keepAlive___redArg(v_s_518_, v_enable_boxed_522_, v_delay_520_);
lean_dec(v_delay_520_);
lean_dec(v_s_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive(lean_object* v_s_524_, uint8_t v_enable_525_, lean_object* v_delay_526_, lean_object* v_x_527_){
_start:
{
uint8_t v___x_529_; lean_object* v___x_530_; uint32_t v___x_531_; lean_object* v___x_532_; 
v___x_529_ = lean_bool_to_int8(v_enable_525_);
v___x_530_ = l_Int_toNat(v_delay_526_);
v___x_531_ = lean_uint32_of_nat(v___x_530_);
lean_dec(v___x_530_);
v___x_532_ = lean_uv_tcp_keepalive(v_s_524_, v___x_529_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___boxed(lean_object* v_s_533_, lean_object* v_enable_534_, lean_object* v_delay_535_, lean_object* v_x_536_, lean_object* v_a_537_){
_start:
{
uint8_t v_enable_boxed_538_; lean_object* v_res_539_; 
v_enable_boxed_538_ = lean_unbox(v_enable_534_);
v_res_539_ = l_Std_Async_TCP_Socket_Server_keepAlive(v_s_533_, v_enable_boxed_538_, v_delay_535_, v_x_536_);
lean_dec(v_delay_535_);
lean_dec(v_s_533_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_mk(){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
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
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_541_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_541_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_mk___boxed(lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_Async_TCP_Socket_Client_mk();
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_bind(lean_object* v_s_560_, lean_object* v_addr_561_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_uv_tcp_bind(v_s_560_, v_addr_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_bind___boxed(lean_object* v_s_564_, lean_object* v_addr_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Async_TCP_Socket_Client_bind(v_s_564_, v_addr_565_);
lean_dec_ref(v_addr_565_);
lean_dec(v_s_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0(lean_object* v___x_568_, lean_object* v_x_569_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_mk_io_user_error(v___x_568_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
else
{
lean_object* v_val_572_; 
lean_dec_ref(v___x_568_);
v_val_572_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_val_572_);
return v_val_572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0___boxed(lean_object* v___x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_Async_TCP_Socket_Client_connect___lam__0(v___x_573_, v_x_574_);
lean_dec(v_x_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1(lean_object* v___f_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v___f_576_);
v_a_579_ = lean_ctor_get(v_x_577_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_577_);
if (v_isSharedCheck_587_ == 0)
{
v___x_581_ = v_x_577_;
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v_x_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_587_;
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
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_586_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
}
else
{
lean_object* v_a_588_; 
v_a_588_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v_x_577_);
if (lean_obj_tag(v_a_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v___f_576_);
v_a_589_ = lean_ctor_get(v_a_588_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_588_);
if (v_isSharedCheck_597_ == 0)
{
v___x_591_ = v_a_588_;
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v_a_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_596_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_a_598_ = lean_ctor_get(v_a_588_, 0);
lean_inc(v_a_598_);
lean_dec_ref(v_a_588_);
v___x_599_ = lean_io_promise_result_opt(v_a_598_);
lean_dec(v_a_598_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = 0;
v___x_602_ = lean_task_map(v___f_576_, v___x_599_, v___x_600_, v___x_601_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1___boxed(lean_object* v___f_604_, lean_object* v_x_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_Async_TCP_Socket_Client_connect___lam__1(v___f_604_, v_x_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect(lean_object* v_s_612_, lean_object* v_addr_613_){
_start:
{
lean_object* v___f_615_; lean_object* v_val_617_; lean_object* v___x_623_; 
v___f_615_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_623_ = lean_uv_tcp_connect(v_s_612_, v_addr_613_);
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
v_val_617_ = v___x_629_;
goto v___jp_616_;
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
v_val_617_ = v___x_637_;
goto v___jp_616_;
}
}
}
v___jp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; 
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_val_617_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = 0;
v___x_622_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_620_, v___x_621_, v___x_619_, v___f_615_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___boxed(lean_object* v_s_640_, lean_object* v_addr_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_Async_TCP_Socket_Client_connect(v_s_640_, v_addr_641_);
lean_dec_ref(v_addr_641_);
lean_dec(v_s_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_sendAll(lean_object* v_s_644_, lean_object* v_data_645_){
_start:
{
lean_object* v___f_647_; lean_object* v_val_649_; lean_object* v___x_655_; 
v___f_647_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_655_ = lean_uv_tcp_send(v_s_644_, v_data_645_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v_val_649_ = v___x_661_;
goto v___jp_648_;
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_a_664_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_655_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_655_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 0);
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
v_val_649_ = v___x_669_;
goto v___jp_648_;
}
}
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; 
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v_val_649_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = 0;
v___x_654_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_652_, v___x_653_, v___x_651_, v___f_647_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_sendAll___boxed(lean_object* v_s_672_, lean_object* v_data_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_Async_TCP_Socket_Client_sendAll(v_s_672_, v_data_673_);
lean_dec(v_s_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_send(lean_object* v_s_676_, lean_object* v_data_677_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___f_682_; lean_object* v_val_684_; lean_object* v___x_690_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_mk_empty_array_with_capacity(v___x_679_);
v___x_681_ = lean_array_push(v___x_680_, v_data_677_);
v___f_682_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_690_ = lean_uv_tcp_send(v_s_676_, v___x_681_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 1);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v_val_684_ = v___x_696_;
goto v___jp_683_;
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_699_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_690_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_690_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
v_val_684_ = v___x_704_;
goto v___jp_683_;
}
}
}
v___jp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; lean_object* v___x_689_; 
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v_val_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = 0;
v___x_689_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_687_, v___x_688_, v___x_686_, v___f_682_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_send___boxed(lean_object* v_s_707_, lean_object* v_data_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_Async_TCP_Socket_Client_send(v_s_707_, v_data_708_);
lean_dec(v_s_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(lean_object* v___x_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_mk_io_user_error(v___x_711_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
else
{
lean_object* v_val_715_; 
lean_dec_ref(v___x_711_);
v_val_715_ = lean_ctor_get(v_x_712_, 0);
lean_inc(v_val_715_);
return v_val_715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed(lean_object* v___x_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(v___x_716_, v_x_717_);
lean_dec(v_x_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(lean_object* v___f_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v___f_719_);
v_a_722_ = lean_ctor_get(v_x_720_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_730_ == 0)
{
v___x_724_ = v_x_720_;
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v_x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
}
else
{
lean_object* v_a_731_; 
v_a_731_ = lean_ctor_get(v_x_720_, 0);
lean_inc(v_a_731_);
lean_dec_ref(v_x_720_);
if (lean_obj_tag(v_a_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v___f_719_);
v_a_732_ = lean_ctor_get(v_a_731_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v_a_731_);
if (v_isSharedCheck_740_ == 0)
{
v___x_734_ = v_a_731_;
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v_a_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_739_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; 
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_a_741_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_a_741_);
lean_dec_ref(v_a_731_);
v___x_742_ = lean_io_promise_result_opt(v_a_741_);
lean_dec(v_a_741_);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = 0;
v___x_745_ = lean_task_map(v___f_719_, v___x_742_, v___x_743_, v___x_744_);
v___x_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed(lean_object* v___f_747_, lean_object* v_x_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(v___f_747_, v_x_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f(lean_object* v_s_755_, uint64_t v_size_756_){
_start:
{
lean_object* v___f_758_; lean_object* v_val_760_; lean_object* v___x_766_; 
v___f_758_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1));
v___x_766_ = lean_uv_tcp_recv(v_s_755_, v_size_756_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 1);
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
v_val_760_ = v___x_772_;
goto v___jp_759_;
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_766_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_766_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 0);
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
v_val_760_ = v___x_780_;
goto v___jp_759_;
}
}
}
v___jp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; 
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v_val_760_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = 0;
v___x_765_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_763_, v___x_764_, v___x_762_, v___f_758_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object* v_s_783_, lean_object* v_size_784_, lean_object* v_a_785_){
_start:
{
uint64_t v_size_boxed_786_; lean_object* v_res_787_; 
v_size_boxed_786_ = lean_unbox_uint64(v_size_784_);
lean_dec_ref(v_size_784_);
v_res_787_ = l_Std_Async_TCP_Socket_Client_recv_x3f(v_s_783_, v_size_boxed_786_);
lean_dec(v_s_783_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(lean_object* v_x_788_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v_x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v_x_788_);
v___x_790_ = lean_task_pure(v_a_789_);
return v___x_790_;
}
else
{
lean_object* v_a_791_; 
v_a_791_ = lean_ctor_get(v_x_788_, 0);
lean_inc_ref(v_a_791_);
lean_dec_ref(v_x_788_);
return v_a_791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2(lean_object* v___f_792_, lean_object* v___x_793_, lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_794_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_804_; 
lean_dec(v___x_793_);
lean_dec_ref(v___f_792_);
v_a_796_ = lean_ctor_get(v_x_794_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_804_ == 0)
{
v___x_798_ = v_x_794_;
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v_x_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_803_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; 
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
else
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v_x_794_, 0);
lean_inc(v_a_805_);
lean_dec_ref(v_x_794_);
if (lean_obj_tag(v_a_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
lean_dec(v___x_793_);
lean_dec_ref(v___f_792_);
v_a_806_ = lean_ctor_get(v_a_805_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_814_ == 0)
{
v___x_808_ = v_a_805_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v_a_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_813_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_a_815_ = lean_ctor_get(v_a_805_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v_a_805_);
v___x_816_ = lean_io_promise_result_opt(v_a_815_);
lean_dec(v_a_815_);
v___x_817_ = 0;
v___x_818_ = lean_task_map(v___f_792_, v___x_816_, v___x_793_, v___x_817_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2___boxed(lean_object* v___f_820_, lean_object* v___x_821_, lean_object* v_x_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2(v___f_820_, v___x_821_, v_x_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1(lean_object* v___x_825_, lean_object* v_s_826_, uint64_t v_size_827_){
_start:
{
lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v_val_832_; lean_object* v___x_837_; 
v___f_829_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0));
lean_inc(v___x_825_);
v___f_830_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2___boxed), 4, 2);
lean_closure_set(v___f_830_, 0, v___f_829_);
lean_closure_set(v___f_830_, 1, v___x_825_);
v___x_837_ = lean_uv_tcp_recv(v_s_826_, v_size_827_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 1);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
v_val_832_ = v___x_843_;
goto v___jp_831_;
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_a_846_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_837_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_837_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 0);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
v_val_832_ = v___x_851_;
goto v___jp_831_;
}
}
}
v___jp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; 
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_val_832_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
v___x_835_ = 0;
v___x_836_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_825_, v___x_835_, v___x_834_, v___f_830_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed(lean_object* v___x_854_, lean_object* v_s_855_, lean_object* v_size_856_, lean_object* v___y_857_){
_start:
{
uint64_t v_size_boxed_858_; lean_object* v_res_859_; 
v_size_boxed_858_ = lean_unbox_uint64(v_size_856_);
lean_dec_ref(v_size_856_);
v_res_859_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1(v___x_854_, v_s_855_, v_size_boxed_858_);
lean_dec(v_s_855_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object* v_val_861_, lean_object* v_s_862_, uint64_t v_size_863_, lean_object* v_w_864_, lean_object* v_lose_865_){
_start:
{
lean_object* v_finished_867_; lean_object* v_promise_868_; lean_object* v_a_870_; lean_object* v___x_874_; lean_object* v___f_875_; uint8_t v___y_877_; uint8_t v___x_900_; 
v_finished_867_ = lean_ctor_get(v_w_864_, 0);
v_promise_868_ = lean_ctor_get(v_w_864_, 1);
v___x_874_ = lean_st_ref_take(v_finished_867_);
v___f_875_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0));
v___x_900_ = lean_unbox(v___x_874_);
lean_dec(v___x_874_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; 
v___x_901_ = 1;
v___y_877_ = v___x_901_;
goto v___jp_876_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = 0;
v___y_877_ = v___x_902_;
goto v___jp_876_;
}
v___jp_869_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_a_870_);
v___x_872_ = lean_io_promise_resolve(v___x_871_, v_promise_868_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
v___jp_876_:
{
uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = 1;
v___x_879_ = lean_box(v___x_878_);
v___x_880_ = lean_st_ref_set(v_finished_867_, v___x_879_);
if (v___y_877_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_s_862_);
lean_dec_ref(v_val_861_);
v___x_881_ = lean_apply_1(v_lose_865_, lean_box(0));
return v___x_881_;
}
else
{
lean_object* v___x_882_; 
lean_dec_ref(v_lose_865_);
v___x_882_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_val_861_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_897_; 
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v___x_882_, 0);
lean_dec(v_unused_898_);
v___x_884_ = v___x_882_;
v_isShared_885_ = v_isSharedCheck_897_;
goto v_resetjp_883_;
}
else
{
lean_dec(v___x_882_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_897_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_box_uint64(v_size_863_);
v___f_888_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed), 4, 3);
lean_closure_set(v___f_888_, 0, v___x_886_);
lean_closure_set(v___f_888_, 1, v_s_862_);
lean_closure_set(v___f_888_, 2, v___x_887_);
v___x_889_ = lean_io_as_task(v___f_888_, v___x_886_);
v___x_890_ = lean_task_bind(v___x_889_, v___f_875_, v___x_886_, v___y_877_);
v___x_891_ = lean_task_get_own(v___x_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; 
lean_del_object(v___x_884_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref(v___x_891_);
v_a_870_ = v_a_892_;
goto v___jp_869_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_io_promise_resolve(v___x_891_, v_promise_868_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_893_);
v___x_895_ = v___x_884_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_899_; 
lean_dec(v_s_862_);
v_a_899_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_882_);
v_a_870_ = v_a_899_;
goto v___jp_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___boxed(lean_object* v_val_903_, lean_object* v_s_904_, lean_object* v_size_905_, lean_object* v_w_906_, lean_object* v_lose_907_, lean_object* v___y_908_){
_start:
{
uint64_t v_size_boxed_909_; lean_object* v_res_910_; 
v_size_boxed_909_ = lean_unbox_uint64(v_size_905_);
lean_dec_ref(v_size_905_);
v_res_910_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_903_, v_s_904_, v_size_boxed_909_, v_w_906_, v_lose_907_);
lean_dec_ref(v_w_906_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object* v_x_911_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_921_; 
v_a_913_ = lean_ctor_get(v_x_911_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_911_);
if (v_isSharedCheck_921_ == 0)
{
v___x_915_ = v_x_911_;
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v_x_911_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_920_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_931_; 
v_a_922_ = lean_ctor_get(v_x_911_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_911_);
if (v_isSharedCheck_931_ == 0)
{
v___x_924_ = v_x_911_;
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v_x_911_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v_a_922_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_930_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object* v_x_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(v_x_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object* v_x_939_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_949_; 
v_a_941_ = lean_ctor_get(v_x_939_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_x_939_);
if (v_isSharedCheck_949_ == 0)
{
v___x_943_ = v_x_939_;
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v_x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
}
else
{
lean_object* v___x_950_; 
lean_dec_ref(v_x_939_);
v___x_950_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1));
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object* v_x_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(v_x_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object* v_s_954_){
_start:
{
lean_object* v_val_957_; lean_object* v___x_959_; 
v___x_959_ = lean_uv_tcp_cancel_recv(v_s_954_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 1);
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v_val_957_ = v___x_965_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_959_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_959_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 0);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
v_val_957_ = v___x_973_;
goto v___jp_956_;
}
}
}
v___jp_956_:
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_val_957_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object* v_s_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(v_s_976_);
lean_dec(v_s_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(lean_object* v_s_979_, uint64_t v_size_980_, lean_object* v_waiter_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_a_985_; 
if (lean_obj_tag(v_a_982_) == 0)
{
lean_object* v___x_987_; 
lean_dec(v_s_979_);
v___x_987_ = lean_box(0);
v_a_985_ = v___x_987_;
goto v___jp_984_;
}
else
{
lean_object* v_val_988_; lean_object* v___f_989_; lean_object* v___x_990_; 
v_val_988_ = lean_ctor_get(v_a_982_, 0);
lean_inc(v_val_988_);
lean_dec_ref(v_a_982_);
v___f_989_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0));
v___x_990_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_988_, v_s_979_, v_size_980_, v_waiter_981_, v___f_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref(v___x_990_);
v_a_985_ = v_a_991_;
goto v___jp_984_;
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_a_992_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_990_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_990_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set_tag(v___x_994_, 0);
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
v___jp_984_:
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_a_985_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(lean_object* v_s_1000_, lean_object* v_size_1001_, lean_object* v_waiter_1002_, lean_object* v_a_1003_, lean_object* v___y_1004_){
_start:
{
uint64_t v_size_boxed_1005_; lean_object* v_res_1006_; 
v_size_boxed_1005_ = lean_unbox_uint64(v_size_1001_);
lean_dec_ref(v_size_1001_);
v_res_1006_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(v_s_1000_, v_size_boxed_1005_, v_waiter_1002_, v_a_1003_);
lean_dec_ref(v_waiter_1002_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object* v___f_1011_, lean_object* v_x_1012_){
_start:
{
if (lean_obj_tag(v_x_1012_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v___f_1011_);
v_a_1014_ = lean_ctor_get(v_x_1012_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_1012_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v_x_1012_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v_x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_a_1023_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_a_1023_);
lean_dec_ref(v_x_1012_);
v___x_1024_ = lean_io_promise_result_opt(v_a_1023_);
lean_dec(v_a_1023_);
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = 0;
v___x_1027_ = lean_io_map_task(v___f_1011_, v___x_1024_, v___x_1025_, v___x_1026_);
lean_dec_ref(v___x_1027_);
v___x_1028_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1));
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(lean_object* v___f_1029_, lean_object* v_x_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(v___f_1029_, v_x_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(lean_object* v_s_1033_, uint64_t v_size_1034_, lean_object* v_waiter_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v_val_1041_; lean_object* v___x_1046_; 
v___x_1037_ = lean_box_uint64(v_size_1034_);
lean_inc(v_s_1033_);
v___f_1038_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1038_, 0, v_s_1033_);
lean_closure_set(v___f_1038_, 1, v___x_1037_);
lean_closure_set(v___f_1038_, 2, v_waiter_1035_);
v___f_1039_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1039_, 0, v___f_1038_);
v___x_1046_ = lean_uv_tcp_wait_readable(v_s_1033_);
lean_dec(v_s_1033_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 1);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
v_val_1041_ = v___x_1052_;
goto v___jp_1040_;
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1046_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1046_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 0);
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
v_val_1041_ = v___x_1060_;
goto v___jp_1040_;
}
}
}
v___jp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_val_1041_);
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = 0;
v___x_1045_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1043_, v___x_1044_, v___x_1042_, v___f_1039_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(lean_object* v_s_1063_, lean_object* v_size_1064_, lean_object* v_waiter_1065_, lean_object* v___y_1066_){
_start:
{
uint64_t v_size_boxed_1067_; lean_object* v_res_1068_; 
v_size_boxed_1067_ = lean_unbox_uint64(v_size_1064_);
lean_dec_ref(v_size_1064_);
v_res_1068_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(v_s_1063_, v_size_boxed_1067_, v_waiter_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(lean_object* v___f_1069_, lean_object* v_s_1070_, uint64_t v_size_1071_, lean_object* v___f_1072_, lean_object* v___f_1073_, lean_object* v_x_1074_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v___f_1073_);
lean_dec_ref(v___f_1072_);
lean_dec(v_s_1070_);
lean_dec_ref(v___f_1069_);
v_a_1076_ = lean_ctor_get(v_x_1074_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_x_1074_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1078_ = v_x_1074_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v_x_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1115_; 
v_a_1085_ = lean_ctor_get(v_x_1074_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1074_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1087_ = v_x_1074_;
v_isShared_1088_ = v_isSharedCheck_1115_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v_x_1074_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1115_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_val_1090_; uint8_t v___x_1095_; 
v___x_1095_ = lean_unbox(v_a_1085_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref(v___f_1073_);
lean_dec_ref(v___f_1072_);
v___x_1096_ = lean_uv_tcp_cancel_recv(v_s_1070_);
lean_dec(v_s_1070_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref(v___x_1096_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_a_1097_);
v___x_1099_ = v___x_1087_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
v_val_1090_ = v___x_1099_;
goto v___jp_1089_;
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; 
v_a_1101_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1101_);
lean_dec_ref(v___x_1096_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 0);
lean_ctor_set(v___x_1087_, 0, v_a_1101_);
v___x_1103_ = v___x_1087_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
v_val_1090_ = v___x_1103_;
goto v___jp_1089_;
}
}
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
lean_del_object(v___x_1087_);
lean_dec_ref(v___f_1069_);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_box_uint64(v_size_1071_);
v___f_1107_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1107_, 0, v___x_1105_);
lean_closure_set(v___f_1107_, 1, v_s_1070_);
lean_closure_set(v___f_1107_, 2, v___x_1106_);
v___x_1108_ = lean_io_as_task(v___f_1107_, v___x_1105_);
v___x_1109_ = lean_unbox(v_a_1085_);
lean_dec(v_a_1085_);
v___x_1110_ = lean_task_bind(v___x_1108_, v___f_1072_, v___x_1105_, v___x_1109_);
v___x_1111_ = lean_task_get_own(v___x_1110_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
v___x_1113_ = 0;
v___x_1114_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1105_, v___x_1113_, v___x_1112_, v___f_1073_);
return v___x_1114_;
}
v___jp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; 
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_val_1090_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_unbox(v_a_1085_);
lean_dec(v_a_1085_);
v___x_1094_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1092_, v___x_1093_, v___x_1091_, v___f_1069_);
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed(lean_object* v___f_1116_, lean_object* v_s_1117_, lean_object* v_size_1118_, lean_object* v___f_1119_, lean_object* v___f_1120_, lean_object* v_x_1121_, lean_object* v___y_1122_){
_start:
{
uint64_t v_size_boxed_1123_; lean_object* v_res_1124_; 
v_size_boxed_1123_ = lean_unbox_uint64(v_size_1118_);
lean_dec_ref(v_size_1118_);
v_res_1124_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(v___f_1116_, v_s_1117_, v_size_boxed_1123_, v___f_1119_, v___f_1120_, v_x_1121_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object* v___f_1125_, lean_object* v_x_1126_){
_start:
{
if (lean_obj_tag(v_x_1126_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v___f_1125_);
v_a_1128_ = lean_ctor_get(v_x_1126_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1126_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1130_ = v_x_1126_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v_x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1150_; 
v_a_1137_ = lean_ctor_get(v_x_1126_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_x_1126_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1139_ = v_x_1126_;
v_isShared_1140_ = v_isSharedCheck_1150_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v_x_1126_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1150_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
uint8_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1141_ = l_IO_Promise_isResolved___redArg(v_a_1137_);
lean_dec(v_a_1137_);
v___x_1142_ = lean_box(v___x_1141_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1142_);
v___x_1144_ = v___x_1139_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = 0;
v___x_1148_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1146_, v___x_1147_, v___x_1145_, v___f_1125_);
return v___x_1148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object* v___f_1151_, lean_object* v_x_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(v___f_1151_, v_x_1152_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object* v___f_1155_, lean_object* v_s_1156_){
_start:
{
lean_object* v_val_1159_; lean_object* v___x_1164_; 
v___x_1164_ = lean_uv_tcp_wait_readable(v_s_1156_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 1);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
v_val_1159_ = v___x_1170_;
goto v___jp_1158_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1164_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1164_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 0);
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
v_val_1159_ = v___x_1178_;
goto v___jp_1158_;
}
}
}
v___jp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; 
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_val_1159_);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = 0;
v___x_1163_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1161_, v___x_1162_, v___x_1160_, v___f_1155_);
return v___x_1163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object* v___f_1181_, lean_object* v_s_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(v___f_1181_, v_s_1182_);
lean_dec(v_s_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector(lean_object* v_s_1187_, uint64_t v_size_1188_){
_start:
{
lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___f_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___x_1199_; 
v___f_1189_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0));
v___f_1190_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___closed__0));
v___f_1191_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___closed__1));
lean_inc_n(v_s_1187_, 3);
v___f_1192_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1192_, 0, v_s_1187_);
v___x_1193_ = lean_box_uint64(v_size_1188_);
v___f_1194_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1194_, 0, v_s_1187_);
lean_closure_set(v___f_1194_, 1, v___x_1193_);
v___x_1195_ = lean_box_uint64(v_size_1188_);
v___f_1196_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed), 7, 5);
lean_closure_set(v___f_1196_, 0, v___f_1191_);
lean_closure_set(v___f_1196_, 1, v_s_1187_);
lean_closure_set(v___f_1196_, 2, v___x_1195_);
lean_closure_set(v___f_1196_, 3, v___f_1189_);
lean_closure_set(v___f_1196_, 4, v___f_1190_);
v___f_1197_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1197_, 0, v___f_1196_);
v___f_1198_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed), 3, 2);
lean_closure_set(v___f_1198_, 0, v___f_1197_);
lean_closure_set(v___f_1198_, 1, v_s_1187_);
v___x_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1199_, 0, v___f_1198_);
lean_ctor_set(v___x_1199_, 1, v___f_1194_);
lean_ctor_set(v___x_1199_, 2, v___f_1192_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___boxed(lean_object* v_s_1200_, lean_object* v_size_1201_){
_start:
{
uint64_t v_size_boxed_1202_; lean_object* v_res_1203_; 
v_size_boxed_1202_ = lean_unbox_uint64(v_size_1201_);
lean_dec_ref(v_size_1201_);
v_res_1203_ = l_Std_Async_TCP_Socket_Client_recvSelector(v_s_1200_, v_size_boxed_1202_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_shutdown(lean_object* v_s_1204_){
_start:
{
lean_object* v___f_1206_; lean_object* v_val_1208_; lean_object* v___x_1214_; 
v___f_1206_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_1214_ = lean_uv_tcp_shutdown(v_s_1204_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 1);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
v_val_1208_ = v___x_1220_;
goto v___jp_1207_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_a_1223_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1214_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1214_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 0);
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
v_val_1208_ = v___x_1228_;
goto v___jp_1207_;
}
}
}
v___jp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_val_1208_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = 0;
v___x_1213_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1211_, v___x_1212_, v___x_1210_, v___f_1206_);
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_shutdown___boxed(lean_object* v_s_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_Async_TCP_Socket_Client_shutdown(v_s_1231_);
lean_dec(v_s_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getPeerName(lean_object* v_s_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_uv_tcp_getpeername(v_s_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getPeerName___boxed(lean_object* v_s_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_Async_TCP_Socket_Client_getPeerName(v_s_1237_);
lean_dec(v_s_1237_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getSockName(lean_object* v_s_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_uv_tcp_getsockname(v_s_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getSockName___boxed(lean_object* v_s_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Std_Async_TCP_Socket_Client_getSockName(v_s_1243_);
lean_dec(v_s_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_noDelay(lean_object* v_s_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_uv_tcp_nodelay(v_s_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_noDelay___boxed(lean_object* v_s_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_Async_TCP_Socket_Client_noDelay(v_s_1249_);
lean_dec(v_s_1249_);
return v_res_1251_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Client_keepAlive___auto__1(void){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg(lean_object* v_s_1253_, uint8_t v_enable_1254_, lean_object* v_delay_1255_){
_start:
{
uint8_t v___x_1257_; lean_object* v___x_1258_; uint32_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1257_ = lean_bool_to_int8(v_enable_1254_);
v___x_1258_ = l_Int_toNat(v_delay_1255_);
v___x_1259_ = lean_uint32_of_nat(v___x_1258_);
lean_dec(v___x_1258_);
v___x_1260_ = lean_uv_tcp_keepalive(v_s_1253_, v___x_1257_, v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object* v_s_1261_, lean_object* v_enable_1262_, lean_object* v_delay_1263_, lean_object* v_a_1264_){
_start:
{
uint8_t v_enable_boxed_1265_; lean_object* v_res_1266_; 
v_enable_boxed_1265_ = lean_unbox(v_enable_1262_);
v_res_1266_ = l_Std_Async_TCP_Socket_Client_keepAlive___redArg(v_s_1261_, v_enable_boxed_1265_, v_delay_1263_);
lean_dec(v_delay_1263_);
lean_dec(v_s_1261_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive(lean_object* v_s_1267_, uint8_t v_enable_1268_, lean_object* v_delay_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v___x_1272_; lean_object* v___x_1273_; uint32_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = lean_bool_to_int8(v_enable_1268_);
v___x_1273_ = l_Int_toNat(v_delay_1269_);
v___x_1274_ = lean_uint32_of_nat(v___x_1273_);
lean_dec(v___x_1273_);
v___x_1275_ = lean_uv_tcp_keepalive(v_s_1267_, v___x_1272_, v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___boxed(lean_object* v_s_1276_, lean_object* v_enable_1277_, lean_object* v_delay_1278_, lean_object* v_x_1279_, lean_object* v_a_1280_){
_start:
{
uint8_t v_enable_boxed_1281_; lean_object* v_res_1282_; 
v_enable_boxed_1281_ = lean_unbox(v_enable_1277_);
v_res_1282_ = l_Std_Async_TCP_Socket_Client_keepAlive(v_s_1276_, v_enable_boxed_1281_, v_delay_1278_, v_x_1279_);
lean_dec(v_delay_1278_);
lean_dec(v_s_1276_);
return v_res_1282_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

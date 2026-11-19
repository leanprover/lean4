// Lean compiler output
// Module: Std.Http.Transport
// Imports: public import Std.Http.Protocol.H1
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
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_uint64_dec_le(uint64_t, uint64_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CloseableChannel_send___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object*);
lean_object* l_Std_CloseableChannel_close___redArg(lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_CloseableChannel_recv___redArg(lean_object*);
lean_object* l_Std_Internal_UV_TCP_Socket_close___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_send(lean_object*, lean_object*);
lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_get_own(lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t);
lean_object* lean_uv_tcp_shutdown(lean_object*);
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___boxed(lean_object*, lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_instTransportClient___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Http_instTransportClient___lam__2___closed__0 = (const lean_object*)&l_Std_Http_instTransportClient___lam__2___closed__0_value;
static const lean_closure_object l_Std_Http_instTransportClient___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___lam__2___closed__0_value)} };
static const lean_object* l_Std_Http_instTransportClient___lam__2___closed__1 = (const lean_object*)&l_Std_Http_instTransportClient___lam__2___closed__1_value;
static const lean_closure_object l_Std_Http_instTransportClient___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___lam__2___closed__1_value)} };
static const lean_object* l_Std_Http_instTransportClient___lam__2___closed__2 = (const lean_object*)&l_Std_Http_instTransportClient___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__2(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_instTransportClient___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instTransportClient___lam__3___closed__0;
static lean_once_cell_t l_Std_Http_instTransportClient___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instTransportClient___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_instTransportClient___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instTransportClient___lam__4___closed__0;
static const lean_ctor_object l_Std_Http_instTransportClient___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_instTransportClient___lam__4___closed__1 = (const lean_object*)&l_Std_Http_instTransportClient___lam__4___closed__1_value;
static const lean_ctor_object l_Std_Http_instTransportClient___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___lam__4___closed__1_value)}};
static const lean_object* l_Std_Http_instTransportClient___lam__4___closed__2 = (const lean_object*)&l_Std_Http_instTransportClient___lam__4___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_instTransportClient___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_instTransportClient___lam__7___closed__0 = (const lean_object*)&l_Std_Http_instTransportClient___lam__7___closed__0_value;
static const lean_ctor_object l_Std_Http_instTransportClient___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___lam__7___closed__0_value)}};
static const lean_object* l_Std_Http_instTransportClient___lam__7___closed__1 = (const lean_object*)&l_Std_Http_instTransportClient___lam__7___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__7(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__9(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instTransportClient___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__8___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___lam__2___closed__0_value)} };
static const lean_object* l_Std_Http_instTransportClient___lam__10___closed__0 = (const lean_object*)&l_Std_Http_instTransportClient___lam__10___closed__0_value;
static const lean_closure_object l_Std_Http_instTransportClient___lam__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__9___boxed, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___lam__10___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_instTransportClient___lam__10___closed__1 = (const lean_object*)&l_Std_Http_instTransportClient___lam__10___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__10___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instTransportClient___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instTransportClient___closed__0 = (const lean_object*)&l_Std_Http_instTransportClient___closed__0_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instTransportClient___closed__1 = (const lean_object*)&l_Std_Http_instTransportClient___closed__1_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__5___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___closed__1_value)} };
static const lean_object* l_Std_Http_instTransportClient___closed__2 = (const lean_object*)&l_Std_Http_instTransportClient___closed__2_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__6___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___closed__2_value)} };
static const lean_object* l_Std_Http_instTransportClient___closed__3 = (const lean_object*)&l_Std_Http_instTransportClient___closed__3_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recvSelector___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instTransportClient___closed__4 = (const lean_object*)&l_Std_Http_instTransportClient___closed__4_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_UV_TCP_Socket_close___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instTransportClient___closed__5 = (const lean_object*)&l_Std_Http_instTransportClient___closed__5_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__7___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instTransportClient___closed__6 = (const lean_object*)&l_Std_Http_instTransportClient___closed__6_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__10___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___closed__6_value)} };
static const lean_object* l_Std_Http_instTransportClient___closed__7 = (const lean_object*)&l_Std_Http_instTransportClient___closed__7_value;
static const lean_ctor_object l_Std_Http_instTransportClient___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___closed__0_value),((lean_object*)&l_Std_Http_instTransportClient___closed__3_value),((lean_object*)&l_Std_Http_instTransportClient___closed__4_value),((lean_object*)&l_Std_Http_instTransportClient___closed__5_value),((lean_object*)&l_Std_Http_instTransportClient___closed__7_value)}};
static const lean_object* l_Std_Http_instTransportClient___closed__8 = (const lean_object*)&l_Std_Http_instTransportClient___closed__8_value;
LEAN_EXPORT const lean_object* l_Std_Http_instTransportClient = (const lean_object*)&l_Std_Http_instTransportClient___closed__8_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_new();
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_Mock_recvJoined___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Mock_recvJoined___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_Mock_recvJoined___closed__0 = (const lean_object*)&l_Std_Http_Internal_Mock_recvJoined___closed__0_value;
static const lean_closure_object l_Std_Http_Internal_Mock_recvJoined___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Mock_recvJoined___lam__4, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_Mock_recvJoined___closed__1 = (const lean_object*)&l_Std_Http_Internal_Mock_recvJoined___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Internal_Mock_send___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "trying to send on an already closed channel"};
static const lean_object* l_Std_Http_Internal_Mock_send___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Internal_Mock_send___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_Internal_Mock_send___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "trying to close an already closed channel"};
static const lean_object* l_Std_Http_Internal_Mock_send___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Internal_Mock_send___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_Mock_send___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Mock_send___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_Mock_send___closed__0 = (const lean_object*)&l_Std_Http_Internal_Mock_send___closed__0_value;
static const lean_closure_object l_Std_Http_Internal_Mock_send___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Mock_send___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Internal_Mock_send___closed__0_value)} };
static const lean_object* l_Std_Http_Internal_Mock_send___closed__1 = (const lean_object*)&l_Std_Http_Internal_Mock_send___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(size_t, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_Mock_sendAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Mock_sendAll___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_Mock_sendAll___closed__0 = (const lean_object*)&l_Std_Http_Internal_Mock_sendAll___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_send(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_send___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Internal_Mock_Client_close___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Http_Internal_Mock_send___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Internal_Mock_Client_close___closed__0 = (const lean_object*)&l_Std_Http_Internal_Mock_Client_close___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_Mock_Client_close___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Http_Internal_Mock_send___lam__0___closed__1_value)}};
static const lean_object* l_Std_Http_Internal_Mock_Client_close___closed__1 = (const lean_object*)&l_Std_Http_Internal_Mock_Client_close___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_close(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_close___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_send(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_send___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_close(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_close___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__0(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__2(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Internal_instTransportClient___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Internal_instTransportClient___lam__3___closed__0 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___lam__3___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_instTransportClient___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_instTransportClient___lam__3___closed__0_value)}};
static const lean_object* l_Std_Http_Internal_instTransportClient___lam__3___closed__1 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_instTransportClient___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportClient___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__0 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__0_value;
static const lean_closure_object l_Std_Http_Internal_instTransportClient___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportClient___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__1 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__1_value;
static const lean_closure_object l_Std_Http_Internal_instTransportClient___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportClient___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__2 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__2_value;
static const lean_closure_object l_Std_Http_Internal_instTransportClient___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Mock_Client_close___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__3 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__3_value;
static const lean_closure_object l_Std_Http_Internal_instTransportClient___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportClient___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__4 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__4_value;
static const lean_ctor_object l_Std_Http_Internal_instTransportClient___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__0_value),((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__1_value),((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__2_value),((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__3_value),((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__4_value)}};
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__5 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_instTransportClient = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__0(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__2(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_instTransportServer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportServer___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportServer___closed__0 = (const lean_object*)&l_Std_Http_Internal_instTransportServer___closed__0_value;
static const lean_closure_object l_Std_Http_Internal_instTransportServer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportServer___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportServer___closed__1 = (const lean_object*)&l_Std_Http_Internal_instTransportServer___closed__1_value;
static const lean_closure_object l_Std_Http_Internal_instTransportServer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportServer___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportServer___closed__2 = (const lean_object*)&l_Std_Http_Internal_instTransportServer___closed__2_value;
static const lean_closure_object l_Std_Http_Internal_instTransportServer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Mock_Server_close___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportServer___closed__3 = (const lean_object*)&l_Std_Http_Internal_instTransportServer___closed__3_value;
static const lean_ctor_object l_Std_Http_Internal_instTransportServer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_instTransportServer___closed__0_value),((lean_object*)&l_Std_Http_Internal_instTransportServer___closed__1_value),((lean_object*)&l_Std_Http_Internal_instTransportServer___closed__2_value),((lean_object*)&l_Std_Http_Internal_instTransportServer___closed__3_value),((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__4_value)}};
static const lean_object* l_Std_Http_Internal_instTransportServer___closed__4 = (const lean_object*)&l_Std_Http_Internal_instTransportServer___closed__4_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_instTransportServer = (const lean_object*)&l_Std_Http_Internal_instTransportServer___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__0(lean_object* v___x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_mk_io_user_error(v___x_1_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
else
{
lean_object* v_val_5_; 
lean_dec_ref(v___x_1_);
v_val_5_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_5_);
return v_val_5_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__0___boxed(lean_object* v___x_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Std_Http_instTransportClient___lam__0(v___x_6_, v_x_7_);
lean_dec(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__1(lean_object* v___f_9_, lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_20_; 
lean_dec_ref(v___f_9_);
v_a_12_ = lean_ctor_get(v_x_10_, 0);
v_isSharedCheck_20_ = !lean_is_exclusive(v_x_10_);
if (v_isSharedCheck_20_ == 0)
{
v___x_14_ = v_x_10_;
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v_x_10_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_19_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; 
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
}
else
{
lean_object* v_a_21_; 
v_a_21_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v_x_10_, 1);
if (lean_obj_tag(v_a_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
lean_dec_ref(v___f_9_);
v_a_22_ = lean_ctor_get(v_a_21_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_a_21_);
if (v_isSharedCheck_30_ == 0)
{
v___x_24_ = v_a_21_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v_a_21_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
}
else
{
lean_object* v_a_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_a_31_ = lean_ctor_get(v_a_21_, 0);
lean_inc(v_a_31_);
lean_dec_ref_known(v_a_21_, 1);
v___x_32_ = lean_io_promise_result_opt(v_a_31_);
lean_dec(v_a_31_);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = 0;
v___x_35_ = lean_task_map(v___f_9_, v___x_32_, v___x_33_, v___x_34_);
v___x_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__1___boxed(lean_object* v___f_37_, lean_object* v_x_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Http_instTransportClient___lam__1(v___f_37_, v_x_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__2(lean_object* v_client_46_, uint64_t v_expect_47_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v_val_53_; lean_object* v___x_57_; 
v___f_49_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__2___closed__2));
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = 0;
v___x_57_ = lean_uv_tcp_recv(v_client_46_, v_expect_47_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set_tag(v___x_60_, 1);
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
v_val_53_ = v___x_63_;
goto v___jp_52_;
}
}
}
else
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
v_a_66_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v___x_57_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_57_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set_tag(v___x_68_, 0);
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_a_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
v_val_53_ = v___x_71_;
goto v___jp_52_;
}
}
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v_val_53_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
v___x_56_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_50_, v___x_51_, v___x_55_, v___f_49_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__2___boxed(lean_object* v_client_74_, lean_object* v_expect_75_, lean_object* v___y_76_){
_start:
{
uint64_t v_expect_boxed_77_; lean_object* v_res_78_; 
v_expect_boxed_77_ = lean_unbox_uint64(v_expect_75_);
lean_dec_ref(v_expect_75_);
v_res_78_ = l_Std_Http_instTransportClient___lam__2(v_client_74_, v_expect_boxed_77_);
lean_dec(v_client_74_);
return v_res_78_;
}
}
static lean_object* _init_l_Std_Http_instTransportClient___lam__3___closed__0(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__2___closed__0));
v___x_80_ = lean_mk_io_user_error(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Std_Http_instTransportClient___lam__3___closed__1(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_obj_once(&l_Std_Http_instTransportClient___lam__3___closed__0, &l_Std_Http_instTransportClient___lam__3___closed__0_once, _init_l_Std_Http_instTransportClient___lam__3___closed__0);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3(lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_obj_once(&l_Std_Http_instTransportClient___lam__3___closed__1, &l_Std_Http_instTransportClient___lam__3___closed__1_once, _init_l_Std_Http_instTransportClient___lam__3___closed__1);
return v___x_84_;
}
else
{
lean_object* v_val_85_; 
v_val_85_ = lean_ctor_get(v_x_83_, 0);
lean_inc(v_val_85_);
return v_val_85_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3___boxed(lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Http_instTransportClient___lam__3(v_x_86_);
lean_dec(v_x_86_);
return v_res_87_;
}
}
static lean_object* _init_l_Std_Http_instTransportClient___lam__4___closed__0(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&l_Std_Http_instTransportClient___lam__3___closed__1, &l_Std_Http_instTransportClient___lam__3___closed__1_once, _init_l_Std_Http_instTransportClient___lam__3___closed__1);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__4(lean_object* v___f_94_, lean_object* v___x_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
lean_dec_ref(v___x_95_);
lean_dec_ref(v___f_94_);
v_a_98_ = lean_ctor_get(v_x_96_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_106_ == 0)
{
v___x_100_ = v_x_96_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v_x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_105_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
}
else
{
lean_object* v_a_107_; uint8_t v___x_108_; 
v_a_107_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v_x_96_, 1);
v___x_108_ = lean_unbox(v_a_107_);
lean_dec(v_a_107_);
if (v___x_108_ == 0)
{
uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = 1;
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_task_map(v___f_94_, v___x_95_, v___x_110_, v___x_109_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; 
lean_dec_ref(v___f_94_);
v___x_113_ = lean_task_get_own(v___x_95_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Std_Http_instTransportClient___lam__4___closed__0, &l_Std_Http_instTransportClient___lam__4___closed__0_once, _init_l_Std_Http_instTransportClient___lam__4___closed__0);
return v___x_114_;
}
else
{
lean_object* v_val_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_123_; 
v_val_115_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_123_ == 0)
{
v___x_117_ = v___x_113_;
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_val_115_);
lean_dec(v___x_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
if (lean_obj_tag(v_val_115_) == 0)
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 0);
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_val_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
else
{
lean_object* v___x_122_; 
lean_dec_ref_known(v_val_115_, 1);
lean_del_object(v___x_117_);
v___x_122_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__4___closed__2));
return v___x_122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__4___boxed(lean_object* v___f_124_, lean_object* v___x_125_, lean_object* v_x_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Http_instTransportClient___lam__4(v___f_124_, v___x_125_, v_x_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__5(lean_object* v___f_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
lean_dec_ref(v___f_129_);
v_a_132_ = lean_ctor_get(v_x_130_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_140_ == 0)
{
v___x_134_ = v_x_130_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v_x_130_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
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
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_139_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; 
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_159_; 
v_a_141_ = lean_ctor_get(v_x_130_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_159_ == 0)
{
v___x_143_ = v_x_130_;
v_isShared_144_ = v_isSharedCheck_159_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v_x_130_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_159_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___f_146_; lean_object* v___x_147_; uint8_t v___x_148_; uint8_t v_val_150_; uint8_t v___x_157_; 
v___x_145_ = lean_io_promise_result_opt(v_a_141_);
lean_dec(v_a_141_);
lean_inc_ref(v___x_145_);
v___f_146_ = lean_alloc_closure((void*)(l_Std_Http_instTransportClient___lam__4___boxed), 4, 2);
lean_closure_set(v___f_146_, 0, v___f_129_);
lean_closure_set(v___f_146_, 1, v___x_145_);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = 0;
v___x_157_ = lean_io_get_task_state(v___x_145_);
lean_dec_ref(v___x_145_);
if (v___x_157_ == 2)
{
uint8_t v___x_158_; 
v___x_158_ = 1;
v_val_150_ = v___x_158_;
goto v___jp_149_;
}
else
{
v_val_150_ = v___x_148_;
goto v___jp_149_;
}
v___jp_149_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_box(v_val_150_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_151_);
v___x_153_ = v___x_143_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_156_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
v___x_155_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_147_, v___x_148_, v___x_154_, v___f_146_);
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__5___boxed(lean_object* v___f_160_, lean_object* v_x_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_Http_instTransportClient___lam__5(v___f_160_, v_x_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__6(lean_object* v___f_164_, lean_object* v_client_165_, lean_object* v_data_166_){
_start:
{
lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v_val_171_; lean_object* v___x_174_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = 0;
v___x_174_ = lean_uv_tcp_send(v_client_165_, v_data_166_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set_tag(v___x_177_, 1);
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
v_val_171_ = v___x_180_;
goto v___jp_170_;
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_a_183_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_174_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_174_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 0);
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
v_val_171_ = v___x_188_;
goto v___jp_170_;
}
}
}
v___jp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v_val_171_);
v___x_173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_168_, v___x_169_, v___x_172_, v___f_164_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__6___boxed(lean_object* v___f_191_, lean_object* v_client_192_, lean_object* v_data_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_Http_instTransportClient___lam__6(v___f_191_, v_client_192_, v_data_193_);
lean_dec(v_client_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__7(lean_object* v_x_201_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
v_a_203_ = lean_ctor_get(v_x_201_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_201_);
if (v_isSharedCheck_211_ == 0)
{
v___x_205_ = v_x_201_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v_x_201_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_210_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; 
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
}
else
{
lean_object* v___x_212_; 
lean_dec_ref_known(v_x_201_, 1);
v___x_212_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__7___closed__1));
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__7___boxed(lean_object* v_x_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Http_instTransportClient___lam__7(v_x_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__8(lean_object* v___x_216_, lean_object* v_x_217_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_mk_io_user_error(v___x_216_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
else
{
lean_object* v_val_220_; 
lean_dec_ref(v___x_216_);
v_val_220_ = lean_ctor_get(v_x_217_, 0);
lean_inc(v_val_220_);
return v_val_220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__8___boxed(lean_object* v___x_221_, lean_object* v_x_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_Http_instTransportClient___lam__8(v___x_221_, v_x_222_);
lean_dec(v_x_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__9(lean_object* v___f_224_, lean_object* v___x_225_, uint8_t v___x_226_, lean_object* v_x_227_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
lean_dec(v___x_225_);
lean_dec_ref(v___f_224_);
v_a_229_ = lean_ctor_get(v_x_227_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v_x_227_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v_x_227_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_236_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
else
{
lean_object* v_a_238_; 
v_a_238_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v_x_227_, 1);
if (lean_obj_tag(v_a_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
lean_dec(v___x_225_);
lean_dec_ref(v___f_224_);
v_a_239_ = lean_ctor_get(v_a_238_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_a_238_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v_a_238_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v_a_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_a_248_ = lean_ctor_get(v_a_238_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v_a_238_, 1);
v___x_249_ = lean_io_promise_result_opt(v_a_248_);
lean_dec(v_a_248_);
v___x_250_ = lean_task_map(v___f_224_, v___x_249_, v___x_225_, v___x_226_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__9___boxed(lean_object* v___f_252_, lean_object* v___x_253_, lean_object* v___x_254_, lean_object* v_x_255_, lean_object* v___y_256_){
_start:
{
uint8_t v___x_1718__boxed_257_; lean_object* v_res_258_; 
v___x_1718__boxed_257_ = lean_unbox(v___x_254_);
v_res_258_ = l_Std_Http_instTransportClient___lam__9(v___f_252_, v___x_253_, v___x_1718__boxed_257_, v_x_255_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__10(lean_object* v___f_266_, lean_object* v_client_267_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___f_271_; lean_object* v_val_273_; lean_object* v___x_278_; 
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = 0;
v___f_271_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__10___closed__1));
v___x_278_ = lean_uv_tcp_shutdown(v_client_267_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 1);
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
v_val_273_ = v___x_284_;
goto v___jp_272_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_a_287_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_278_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_278_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 0);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
v_val_273_ = v___x_292_;
goto v___jp_272_;
}
}
}
v___jp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_val_273_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
v___x_276_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_269_, v___x_270_, v___x_275_, v___f_271_);
v___x_277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_269_, v___x_270_, v___x_276_, v___f_266_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__10___boxed(lean_object* v___f_295_, lean_object* v_client_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Http_instTransportClient___lam__10(v___f_295_, v_client_296_);
lean_dec(v_client_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_new(){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_318_ = lean_box(0);
v___x_319_ = l_Std_CloseableChannel_new___redArg(v___x_318_);
v___x_320_ = l_Std_CloseableChannel_new___redArg(v___x_318_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
lean_inc_ref(v___x_321_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_new___boxed(lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_Http_Internal_Mock_new();
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__0(lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_a_327_ = lean_ctor_get(v_x_325_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v_x_325_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v_x_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_334_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_345_; 
v_a_336_ = lean_ctor_get(v_x_325_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_345_ == 0)
{
v___x_338_ = v_x_325_;
v_isShared_339_ = v_isSharedCheck_345_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v_x_325_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_345_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v_a_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_344_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; 
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__0___boxed(lean_object* v_x_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Http_Internal_Mock_recvJoined___lam__0(v_x_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__1(lean_object* v_a_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
v_a_352_ = lean_ctor_get(v_x_350_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_360_ == 0)
{
v___x_354_ = v_x_350_;
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v_x_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref_known(v_x_350_, 1);
v___x_361_ = l_IO_Promise_result_x21___redArg(v_a_349_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed(lean_object* v_a_363_, lean_object* v_x_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_Http_Internal_Mock_recvJoined___lam__1(v_a_363_, v_x_364_);
lean_dec(v_a_363_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(lean_object* v_b_367_, lean_object* v_x_368_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_b_367_);
v_a_370_ = lean_ctor_get(v_x_368_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_378_ == 0)
{
v___x_372_ = v_x_368_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v_x_368_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_377_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_405_; 
v_a_379_ = lean_ctor_get(v_x_368_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_405_ == 0)
{
v___x_381_ = v_x_368_;
v_isShared_382_ = v_isSharedCheck_405_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v_x_368_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_405_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
if (lean_obj_tag(v_a_379_) == 0)
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_b_367_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_383_);
v___x_385_ = v___x_381_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_387_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
else
{
lean_object* v_val_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_404_; 
v_val_388_ = lean_ctor_get(v_a_379_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_a_379_);
if (v_isSharedCheck_404_ == 0)
{
v___x_390_ = v_a_379_;
v_isShared_391_ = v_isSharedCheck_404_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_val_388_);
lean_dec(v_a_379_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_404_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_byte_array_size(v_b_367_);
v___x_394_ = lean_byte_array_size(v_val_388_);
v___x_395_ = 0;
v___x_396_ = lean_byte_array_copy_slice(v_val_388_, v___x_392_, v_b_367_, v___x_393_, v___x_394_, v___x_395_);
lean_dec(v_val_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_396_);
v___x_398_ = v___x_390_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_403_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_398_);
v___x_400_ = v___x_381_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_402_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; 
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1___boxed(lean_object* v_b_406_, lean_object* v_x_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(v_b_406_, v_x_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0___boxed(lean_object* v_promise_410_, lean_object* v_recvChan_411_, lean_object* v_expect_412_, lean_object* v_prio_413_, lean_object* v_x_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(v_promise_410_, v_recvChan_411_, v_expect_412_, v_prio_413_, v_x_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(lean_object* v_recvChan_417_, lean_object* v_expect_418_, lean_object* v_prio_419_, lean_object* v_promise_420_, lean_object* v_b_421_){
_start:
{
lean_object* v_a_424_; lean_object* v___f_427_; lean_object* v___f_428_; 
lean_inc(v_prio_419_);
lean_inc(v_expect_418_);
lean_inc_ref(v_recvChan_417_);
lean_inc(v_promise_420_);
v___f_427_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_427_, 0, v_promise_420_);
lean_closure_set(v___f_427_, 1, v_recvChan_417_);
lean_closure_set(v___f_427_, 2, v_expect_418_);
lean_closure_set(v___f_427_, 3, v_prio_419_);
lean_inc_ref(v_b_421_);
v___f_428_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_428_, 0, v_b_421_);
if (lean_obj_tag(v_expect_418_) == 1)
{
lean_object* v_val_452_; lean_object* v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; uint8_t v___x_456_; 
v_val_452_ = lean_ctor_get(v_expect_418_, 0);
v___x_453_ = lean_byte_array_size(v_b_421_);
v___x_454_ = lean_uint64_of_nat(v___x_453_);
v___x_455_ = lean_unbox_uint64(v_val_452_);
v___x_456_ = lean_uint64_dec_le(v___x_455_, v___x_454_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_b_421_);
goto v___jp_429_;
}
else
{
lean_dec_ref_known(v_expect_418_, 1);
lean_dec_ref(v___f_428_);
lean_dec_ref(v___f_427_);
lean_dec(v_prio_419_);
lean_dec_ref(v_recvChan_417_);
v_a_424_ = v_b_421_;
goto v___jp_423_;
}
}
else
{
lean_dec_ref(v_b_421_);
goto v___jp_429_;
}
v___jp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v_a_424_);
v___x_426_ = lean_io_promise_resolve(v___x_425_, v_promise_420_);
lean_dec(v_promise_420_);
return v___x_426_;
}
v___jp_429_:
{
lean_object* v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = 0;
lean_inc_ref(v_recvChan_417_);
v___x_432_ = l_Std_CloseableChannel_tryRecv___redArg(v_recvChan_417_);
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
v___x_435_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_430_, v___x_431_, v___x_434_, v___f_428_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; 
lean_dec_ref(v___f_427_);
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
if (lean_obj_tag(v_a_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_prio_419_);
lean_dec(v_expect_418_);
lean_dec_ref(v_recvChan_417_);
v_a_437_ = lean_ctor_get(v_a_436_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_a_436_);
if (v_isSharedCheck_445_ == 0)
{
v___x_439_ = v_a_436_;
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v_a_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_444_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; 
v___x_443_ = lean_io_promise_resolve(v___x_442_, v_promise_420_);
lean_dec(v_promise_420_);
return v___x_443_;
}
}
}
else
{
lean_object* v_a_446_; 
v_a_446_ = lean_ctor_get(v_a_436_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v_a_436_, 1);
if (lean_obj_tag(v_a_446_) == 0)
{
lean_object* v_a_447_; 
lean_dec(v_prio_419_);
lean_dec(v_expect_418_);
lean_dec_ref(v_recvChan_417_);
v_a_447_ = lean_ctor_get(v_a_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v_a_446_, 1);
v_a_424_ = v_a_447_;
goto v___jp_423_;
}
else
{
lean_object* v_a_448_; 
v_a_448_ = lean_ctor_get(v_a_446_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v_a_446_, 1);
v_b_421_ = v_a_448_;
goto _start;
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_451_; 
lean_dec(v_promise_420_);
lean_dec(v_expect_418_);
lean_dec_ref(v_recvChan_417_);
v_a_450_ = lean_ctor_get(v___x_435_, 0);
lean_inc_ref(v_a_450_);
lean_dec_ref_known(v___x_435_, 1);
v___x_451_ = l_BaseIO_chainTask___redArg(v_a_450_, v___f_427_, v_prio_419_, v___x_431_);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(lean_object* v_promise_457_, lean_object* v_recvChan_458_, lean_object* v_expect_459_, lean_object* v_prio_460_, lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_prio_460_);
lean_dec(v_expect_459_);
lean_dec_ref(v_recvChan_458_);
v_a_463_ = lean_ctor_get(v_x_461_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_x_461_);
if (v_isSharedCheck_471_ == 0)
{
v___x_465_ = v_x_461_;
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v_x_461_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_470_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; 
v___x_469_ = lean_io_promise_resolve(v___x_468_, v_promise_457_);
lean_dec(v_promise_457_);
return v___x_469_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_483_; 
v_a_472_ = lean_ctor_get(v_x_461_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_x_461_);
if (v_isSharedCheck_483_ == 0)
{
v___x_474_ = v_x_461_;
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v_x_461_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
if (lean_obj_tag(v_a_472_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; 
lean_dec(v_prio_460_);
lean_dec(v_expect_459_);
lean_dec_ref(v_recvChan_458_);
v_a_476_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v_a_472_, 1);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v_a_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_476_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; 
v___x_479_ = lean_io_promise_resolve(v___x_478_, v_promise_457_);
lean_dec(v_promise_457_);
return v___x_479_;
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_482_; 
lean_del_object(v___x_474_);
v_a_481_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_a_472_, 1);
v___x_482_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_458_, v_expect_459_, v_prio_460_, v_promise_457_, v_a_481_);
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___boxed(lean_object* v_recvChan_484_, lean_object* v_expect_485_, lean_object* v_prio_486_, lean_object* v_promise_487_, lean_object* v_b_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_484_, v_expect_485_, v_prio_486_, v_promise_487_, v_b_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2(lean_object* v_recvChan_491_, lean_object* v_expect_492_, lean_object* v___x_493_, lean_object* v_val_494_, uint8_t v___x_495_, lean_object* v_x_496_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref(v_val_494_);
lean_dec(v___x_493_);
lean_dec(v_expect_492_);
lean_dec_ref(v_recvChan_491_);
v_a_498_ = lean_ctor_get(v_x_496_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_506_ == 0)
{
v___x_500_ = v_x_496_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v_x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_505_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_518_; 
v_a_507_ = lean_ctor_get(v_x_496_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_518_ == 0)
{
v___x_509_ = v_x_496_;
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v_x_496_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
lean_inc(v_a_507_);
v___f_511_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed), 3, 1);
lean_closure_set(v___f_511_, 0, v_a_507_);
lean_inc(v___x_493_);
v___x_512_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_491_, v_expect_492_, v___x_493_, v_a_507_, v_val_494_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_512_);
v___x_514_ = v___x_509_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_517_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_493_, v___x_495_, v___x_515_, v___f_511_);
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed(lean_object* v_recvChan_519_, lean_object* v_expect_520_, lean_object* v___x_521_, lean_object* v_val_522_, lean_object* v___x_523_, lean_object* v_x_524_, lean_object* v___y_525_){
_start:
{
uint8_t v___x_2249__boxed_526_; lean_object* v_res_527_; 
v___x_2249__boxed_526_ = lean_unbox(v___x_523_);
v_res_527_ = l_Std_Http_Internal_Mock_recvJoined___lam__2(v_recvChan_519_, v_expect_520_, v___x_521_, v_val_522_, v___x_2249__boxed_526_, v_x_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3(lean_object* v_recvChan_528_, lean_object* v_expect_529_, lean_object* v___f_530_, lean_object* v_x_531_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v___x_533_; 
lean_dec_ref(v___f_530_);
lean_dec(v_expect_529_);
lean_dec_ref(v_recvChan_528_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v_x_531_);
return v___x_533_;
}
else
{
lean_object* v_a_534_; 
v_a_534_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_a_534_);
if (lean_obj_tag(v_a_534_) == 0)
{
lean_object* v___x_535_; 
lean_dec_ref(v___f_530_);
lean_dec(v_expect_529_);
lean_dec_ref(v_recvChan_528_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v_x_531_);
return v___x_535_;
}
else
{
lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_557_; 
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v_x_531_, 0);
lean_dec(v_unused_558_);
v___x_537_ = v_x_531_;
v_isShared_538_ = v_isSharedCheck_557_;
goto v_resetjp_536_;
}
else
{
lean_dec(v_x_531_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_557_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_556_; 
v_val_539_ = lean_ctor_get(v_a_534_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_a_534_);
if (v_isSharedCheck_556_ == 0)
{
v___x_541_ = v_a_534_;
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v_a_534_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___f_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = 0;
v___x_545_ = lean_box(v___x_544_);
v___f_546_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed), 7, 5);
lean_closure_set(v___f_546_, 0, v_recvChan_528_);
lean_closure_set(v___f_546_, 1, v_expect_529_);
lean_closure_set(v___f_546_, 2, v___x_543_);
lean_closure_set(v___f_546_, 3, v_val_539_);
lean_closure_set(v___f_546_, 4, v___x_545_);
v___x_547_ = lean_io_promise_new();
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_547_);
v___x_549_ = v___x_537_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_555_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 0);
lean_ctor_set(v___x_541_, 0, v___x_549_);
v___x_551_ = v___x_541_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_554_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_543_, v___x_544_, v___x_551_, v___f_546_);
v___x_553_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_543_, v___x_544_, v___x_552_, v___f_530_);
return v___x_553_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed(lean_object* v_recvChan_559_, lean_object* v_expect_560_, lean_object* v___f_561_, lean_object* v_x_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Http_Internal_Mock_recvJoined___lam__3(v_recvChan_559_, v_expect_560_, v___f_561_, v_x_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__4(lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v_a_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5(lean_object* v___f_567_, lean_object* v___f_568_, lean_object* v_x_569_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
lean_dec_ref(v___f_568_);
lean_dec_ref(v___f_567_);
v_a_571_ = lean_ctor_get(v_x_569_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_569_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v_x_569_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v_x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_a_580_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v_x_569_, 1);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = 0;
v___x_583_ = lean_task_map(v___f_567_, v_a_580_, v___x_581_, v___x_582_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
v___x_585_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_581_, v___x_582_, v___x_584_, v___f_568_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed(lean_object* v___f_586_, lean_object* v___f_587_, lean_object* v_x_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_Http_Internal_Mock_recvJoined___lam__5(v___f_586_, v___f_587_, v_x_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined(lean_object* v_recvChan_593_, lean_object* v_expect_594_){
_start:
{
lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___f_596_ = ((lean_object*)(l_Std_Http_Internal_Mock_recvJoined___closed__0));
lean_inc_ref(v_recvChan_593_);
v___f_597_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed), 5, 3);
lean_closure_set(v___f_597_, 0, v_recvChan_593_);
lean_closure_set(v___f_597_, 1, v_expect_594_);
lean_closure_set(v___f_597_, 2, v___f_596_);
v___f_598_ = ((lean_object*)(l_Std_Http_Internal_Mock_recvJoined___closed__1));
v___f_599_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed), 4, 2);
lean_closure_set(v___f_599_, 0, v___f_598_);
lean_closure_set(v___f_599_, 1, v___f_597_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = 0;
v___x_602_ = l_Std_CloseableChannel_recv___redArg(v_recvChan_593_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
v___x_605_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_600_, v___x_601_, v___x_604_, v___f_599_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___boxed(lean_object* v_recvChan_606_, lean_object* v_expect_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Http_Internal_Mock_recvJoined(v_recvChan_606_, v_expect_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__0(lean_object* v___y_612_){
_start:
{
lean_object* v___y_614_; 
if (lean_obj_tag(v___y_612_) == 0)
{
lean_object* v_a_617_; uint8_t v___x_618_; 
v_a_617_ = lean_ctor_get(v___y_612_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___y_612_, 1);
v___x_618_ = lean_unbox(v_a_617_);
lean_dec(v_a_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___lam__0___closed__0));
v___y_614_ = v___x_619_;
goto v___jp_613_;
}
else
{
lean_object* v___x_620_; 
v___x_620_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___lam__0___closed__1));
v___y_614_ = v___x_620_;
goto v___jp_613_;
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
v_a_621_ = lean_ctor_get(v___y_612_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___y_612_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___y_612_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___y_612_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
v___jp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_inc_ref(v___y_614_);
v___x_615_ = lean_mk_io_user_error(v___y_614_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__1(lean_object* v___f_629_, lean_object* v_x_630_){
_start:
{
if (lean_obj_tag(v_x_630_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v___f_629_);
v_a_632_ = lean_ctor_get(v_x_630_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v_x_630_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v_x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_a_641_ = lean_ctor_get(v_x_630_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v_x_630_, 1);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = 0;
v___x_644_ = lean_task_map(v___f_629_, v_a_641_, v___x_642_, v___x_643_);
v___x_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__1___boxed(lean_object* v___f_646_, lean_object* v_x_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_Http_Internal_Mock_send___lam__1(v___f_646_, v_x_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send(lean_object* v_sendChan_653_, lean_object* v_data_654_){
_start:
{
lean_object* v___f_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___f_656_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___closed__1));
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = 0;
v___x_659_ = l_Std_CloseableChannel_send___redArg(v_sendChan_653_, v_data_654_);
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
v___x_662_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_657_, v___x_658_, v___x_661_, v___f_656_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___boxed(lean_object* v_sendChan_663_, lean_object* v_data_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_Http_Internal_Mock_send(v_sendChan_663_, v_data_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0(lean_object* v_x_667_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v_x_667_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
lean_dec_ref_known(v_x_667_, 1);
v___x_670_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__4___closed__2));
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___boxed(lean_object* v_x_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_Http_Internal_Mock_sendAll___lam__0(v_x_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(lean_object* v___x_674_, lean_object* v_x_675_){
_start:
{
if (lean_obj_tag(v_x_675_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_685_; 
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
lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_694_; 
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_x_675_, 0);
lean_dec(v_unused_695_);
v___x_687_ = v_x_675_;
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_x_675_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_674_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed(lean_object* v___x_696_, lean_object* v_x_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(v___x_696_, v_x_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed(lean_object* v_i_700_, lean_object* v_sendChan_701_, lean_object* v_as_702_, lean_object* v_sz_703_, lean_object* v_x_704_, lean_object* v___y_705_){
_start:
{
size_t v_i_boxed_706_; size_t v_sz_boxed_707_; lean_object* v_res_708_; 
v_i_boxed_706_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_sz_boxed_707_ = lean_unbox_usize(v_sz_703_);
lean_dec(v_sz_703_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(v_i_boxed_706_, v_sendChan_701_, v_as_702_, v_sz_boxed_707_, v_x_704_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(lean_object* v_sendChan_711_, lean_object* v_as_712_, size_t v_sz_713_, size_t v_i_714_, lean_object* v_b_715_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = lean_usize_dec_lt(v_i_714_, v_sz_713_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref(v_as_712_);
lean_dec_ref(v_sendChan_711_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v_b_715_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v_a_724_; lean_object* v___x_725_; uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_720_ = lean_box_usize(v_i_714_);
v___x_721_ = lean_box_usize(v_sz_713_);
lean_inc_ref(v_as_712_);
lean_inc_ref(v_sendChan_711_);
v___f_722_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_722_, 0, v___x_720_);
lean_closure_set(v___f_722_, 1, v_sendChan_711_);
lean_closure_set(v___f_722_, 2, v_as_712_);
lean_closure_set(v___f_722_, 3, v___x_721_);
v___f_723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0));
v_a_724_ = lean_array_uget(v_as_712_, v_i_714_);
lean_dec_ref(v_as_712_);
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = 0;
v___x_727_ = l_Std_Http_Internal_Mock_send(v_sendChan_711_, v_a_724_);
v___x_728_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_725_, v___x_726_, v___x_727_, v___f_723_);
v___x_729_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_725_, v___x_726_, v___x_728_, v___f_722_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(size_t v_i_730_, lean_object* v_sendChan_731_, lean_object* v_as_732_, size_t v_sz_733_, lean_object* v_x_734_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v_as_732_);
lean_dec_ref(v_sendChan_731_);
v_a_736_ = lean_ctor_get(v_x_734_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v_x_734_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v_x_734_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_743_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; 
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_764_; 
v_a_745_ = lean_ctor_get(v_x_734_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_764_ == 0)
{
v___x_747_ = v_x_734_;
v_isShared_748_ = v_isSharedCheck_764_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v_x_734_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_764_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
if (lean_obj_tag(v_a_745_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v_as_732_);
lean_dec_ref(v_sendChan_731_);
v_a_749_ = lean_ctor_get(v_a_745_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_745_);
if (v_isSharedCheck_759_ == 0)
{
v___x_751_ = v_a_745_;
v_isShared_752_ = v_isSharedCheck_759_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v_a_745_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_759_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v_a_749_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_754_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_760_; size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
lean_del_object(v___x_747_);
v_a_760_ = lean_ctor_get(v_a_745_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v_a_745_, 1);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_730_, v___x_761_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_731_, v_as_732_, v_sz_733_, v___x_762_, v_a_760_);
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___boxed(lean_object* v_sendChan_765_, lean_object* v_as_766_, lean_object* v_sz_767_, lean_object* v_i_768_, lean_object* v_b_769_, lean_object* v___y_770_){
_start:
{
size_t v_sz_boxed_771_; size_t v_i_boxed_772_; lean_object* v_res_773_; 
v_sz_boxed_771_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_772_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_765_, v_as_766_, v_sz_boxed_771_, v_i_boxed_772_, v_b_769_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll(lean_object* v_sendChan_775_, lean_object* v_data_776_){
_start:
{
lean_object* v___f_778_; lean_object* v___x_779_; size_t v_sz_780_; size_t v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___f_778_ = ((lean_object*)(l_Std_Http_Internal_Mock_sendAll___closed__0));
v___x_779_ = lean_box(0);
v_sz_780_ = lean_array_size(v_data_776_);
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = 0;
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_775_, v_data_776_, v_sz_780_, v___x_781_, v___x_779_);
v___x_785_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_782_, v___x_783_, v___x_784_, v___f_778_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___boxed(lean_object* v_sendChan_786_, lean_object* v_data_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_Http_Internal_Mock_sendAll(v_sendChan_786_, v_data_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvSelector(lean_object* v_recvChan_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_CloseableChannel_recvSelector___redArg(v_recvChan_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan(lean_object* v_client_792_){
_start:
{
lean_object* v_serverToClient_793_; 
v_serverToClient_793_ = lean_ctor_get(v_client_792_, 1);
lean_inc_ref(v_serverToClient_793_);
return v_serverToClient_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan___boxed(lean_object* v_client_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_Http_Internal_Mock_Client_getRecvChan(v_client_794_);
lean_dec_ref(v_client_794_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan(lean_object* v_client_796_){
_start:
{
lean_object* v_clientToServer_797_; 
v_clientToServer_797_ = lean_ctor_get(v_client_796_, 0);
lean_inc_ref(v_clientToServer_797_);
return v_clientToServer_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan___boxed(lean_object* v_client_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_Http_Internal_Mock_Client_getSendChan(v_client_798_);
lean_dec_ref(v_client_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_send(lean_object* v_client_800_, lean_object* v_data_801_){
_start:
{
lean_object* v_clientToServer_803_; lean_object* v___x_804_; 
v_clientToServer_803_ = lean_ctor_get(v_client_800_, 0);
lean_inc_ref(v_clientToServer_803_);
lean_dec_ref(v_client_800_);
v___x_804_ = l_Std_Http_Internal_Mock_send(v_clientToServer_803_, v_data_801_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_send___boxed(lean_object* v_client_805_, lean_object* v_data_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_Http_Internal_Mock_Client_send(v_client_805_, v_data_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f(lean_object* v_client_809_, lean_object* v_expect_810_){
_start:
{
lean_object* v_serverToClient_812_; lean_object* v___x_813_; 
v_serverToClient_812_ = lean_ctor_get(v_client_809_, 1);
lean_inc_ref(v_serverToClient_812_);
lean_dec_ref(v_client_809_);
v___x_813_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_812_, v_expect_810_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f___boxed(lean_object* v_client_814_, lean_object* v_expect_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_Http_Internal_Mock_Client_recv_x3f(v_client_814_, v_expect_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(lean_object* v___x_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_821_; 
lean_inc_ref(v___x_818_);
v___x_821_ = l_Std_CloseableChannel_tryRecv___redArg(v___x_818_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_dec_ref(v___x_818_);
return v_a_819_;
}
else
{
lean_object* v_val_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; 
v_val_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_byte_array_size(v_a_819_);
v___x_825_ = lean_byte_array_size(v_val_822_);
v___x_826_ = 0;
v___x_827_ = lean_byte_array_copy_slice(v_val_822_, v___x_823_, v_a_819_, v___x_824_, v___x_825_, v___x_826_);
lean_dec(v_val_822_);
v_a_819_ = v___x_827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg___boxed(lean_object* v___x_829_, lean_object* v_a_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v___x_829_, v_a_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(lean_object* v_client_833_){
_start:
{
lean_object* v_serverToClient_835_; lean_object* v___x_836_; 
v_serverToClient_835_ = lean_ctor_get(v_client_833_, 1);
lean_inc_ref_n(v_serverToClient_835_, 2);
lean_dec_ref(v_client_833_);
v___x_836_ = l_Std_CloseableChannel_tryRecv___redArg(v_serverToClient_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_dec_ref(v_serverToClient_835_);
return v___x_836_;
}
else
{
lean_object* v_val_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_845_; 
v_val_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_845_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_val_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v_serverToClient_835_, v_val_837_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg___boxed(lean_object* v_client_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f(lean_object* v_client_849_, uint64_t v___expect_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_849_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___boxed(lean_object* v_client_853_, lean_object* v___expect_854_, lean_object* v_a_855_){
_start:
{
uint64_t v___expect_boxed_856_; lean_object* v_res_857_; 
v___expect_boxed_856_ = lean_unbox_uint64(v___expect_854_);
lean_dec_ref(v___expect_854_);
v_res_857_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f(v_client_853_, v___expect_boxed_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(lean_object* v___x_858_, lean_object* v_inst_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v___x_858_, v_a_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___boxed(lean_object* v___x_863_, lean_object* v_inst_864_, lean_object* v_a_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(v___x_863_, v_inst_864_, v_a_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_close(lean_object* v_client_872_){
_start:
{
lean_object* v_clientToServer_874_; lean_object* v_serverToClient_875_; uint8_t v___x_903_; 
v_clientToServer_874_ = lean_ctor_get(v_client_872_, 0);
lean_inc_ref_n(v_clientToServer_874_, 2);
v_serverToClient_875_ = lean_ctor_get(v_client_872_, 1);
lean_inc_ref(v_serverToClient_875_);
lean_dec_ref(v_client_872_);
v___x_903_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_874_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
v___x_904_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_874_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_dec_ref_known(v___x_904_, 1);
goto v___jp_876_;
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_serverToClient_875_);
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_918_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_918_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_918_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
uint8_t v___x_909_; 
v___x_909_ = lean_unbox(v_a_905_);
lean_dec(v_a_905_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_910_);
v___x_912_ = v___x_907_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_914_);
v___x_916_ = v___x_907_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
else
{
lean_dec_ref(v_clientToServer_874_);
goto v___jp_876_;
}
v___jp_876_:
{
uint8_t v___x_877_; 
lean_inc_ref(v_serverToClient_875_);
v___x_877_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_875_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_875_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_900_; 
v_a_887_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_900_ == 0)
{
v___x_889_ = v___x_878_;
v_isShared_890_ = v_isSharedCheck_900_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_878_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_900_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v___x_891_; 
v___x_891_ = lean_unbox(v_a_887_);
lean_dec(v_a_887_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_896_);
v___x_898_ = v___x_889_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; 
lean_dec_ref(v_serverToClient_875_);
v___x_901_ = lean_box(0);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_close___boxed(lean_object* v_client_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_Http_Internal_Mock_Client_close(v_client_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan(lean_object* v_server_922_){
_start:
{
lean_object* v_clientToServer_923_; 
v_clientToServer_923_ = lean_ctor_get(v_server_922_, 0);
lean_inc_ref(v_clientToServer_923_);
return v_clientToServer_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan___boxed(lean_object* v_server_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_Http_Internal_Mock_Server_getRecvChan(v_server_924_);
lean_dec_ref(v_server_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan(lean_object* v_server_926_){
_start:
{
lean_object* v_serverToClient_927_; 
v_serverToClient_927_ = lean_ctor_get(v_server_926_, 1);
lean_inc_ref(v_serverToClient_927_);
return v_serverToClient_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan___boxed(lean_object* v_server_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_Http_Internal_Mock_Server_getSendChan(v_server_928_);
lean_dec_ref(v_server_928_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_send(lean_object* v_server_930_, lean_object* v_data_931_){
_start:
{
lean_object* v_serverToClient_933_; lean_object* v___x_934_; 
v_serverToClient_933_ = lean_ctor_get(v_server_930_, 1);
lean_inc_ref(v_serverToClient_933_);
lean_dec_ref(v_server_930_);
v___x_934_ = l_Std_Http_Internal_Mock_send(v_serverToClient_933_, v_data_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_send___boxed(lean_object* v_server_935_, lean_object* v_data_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_Http_Internal_Mock_Server_send(v_server_935_, v_data_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f(lean_object* v_server_939_, lean_object* v_expect_940_){
_start:
{
lean_object* v_clientToServer_942_; lean_object* v___x_943_; 
v_clientToServer_942_ = lean_ctor_get(v_server_939_, 0);
lean_inc_ref(v_clientToServer_942_);
lean_dec_ref(v_server_939_);
v___x_943_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_942_, v_expect_940_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f___boxed(lean_object* v_server_944_, lean_object* v_expect_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Std_Http_Internal_Mock_Server_recv_x3f(v_server_944_, v_expect_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(lean_object* v_server_948_){
_start:
{
lean_object* v_clientToServer_950_; lean_object* v___x_951_; 
v_clientToServer_950_ = lean_ctor_get(v_server_948_, 0);
lean_inc_ref_n(v_clientToServer_950_, 2);
lean_dec_ref(v_server_948_);
v___x_951_ = l_Std_CloseableChannel_tryRecv___redArg(v_clientToServer_950_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_dec_ref(v_clientToServer_950_);
return v___x_951_;
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_960_; 
v_val_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_960_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_val_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v_clientToServer_950_, v_val_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg___boxed(lean_object* v_server_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_961_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f(lean_object* v_server_964_, uint64_t v___expect_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___boxed(lean_object* v_server_968_, lean_object* v___expect_969_, lean_object* v_a_970_){
_start:
{
uint64_t v___expect_boxed_971_; lean_object* v_res_972_; 
v___expect_boxed_971_ = lean_unbox_uint64(v___expect_969_);
lean_dec_ref(v___expect_969_);
v_res_972_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f(v_server_968_, v___expect_boxed_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_close(lean_object* v_server_973_){
_start:
{
lean_object* v_clientToServer_975_; lean_object* v_serverToClient_976_; uint8_t v___x_1004_; 
v_clientToServer_975_ = lean_ctor_get(v_server_973_, 0);
lean_inc_ref_n(v_clientToServer_975_, 2);
v_serverToClient_976_ = lean_ctor_get(v_server_973_, 1);
lean_inc_ref(v_serverToClient_976_);
lean_dec_ref(v_server_973_);
v___x_1004_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_975_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_975_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_dec_ref_known(v___x_1005_, 1);
goto v___jp_977_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_serverToClient_976_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_unbox(v_a_1006_);
lean_dec(v_a_1006_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1011_);
v___x_1013_ = v___x_1008_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1015_);
v___x_1017_ = v___x_1008_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
else
{
lean_dec_ref(v_clientToServer_975_);
goto v___jp_977_;
}
v___jp_977_:
{
uint8_t v___x_978_; 
lean_inc_ref(v_serverToClient_976_);
v___x_978_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_976_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_976_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1001_; 
v_a_988_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_990_ = v___x_979_;
v_isShared_991_ = v_isSharedCheck_1001_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_979_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1001_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
uint8_t v___x_992_; 
v___x_992_ = lean_unbox(v_a_988_);
lean_dec(v_a_988_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_993_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_997_);
v___x_999_ = v___x_990_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec_ref(v_serverToClient_976_);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_close___boxed(lean_object* v_server_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_Http_Internal_Mock_Server_close(v_server_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__0(lean_object* v_client_1023_, uint64_t v_expect_1024_){
_start:
{
lean_object* v_serverToClient_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_serverToClient_1026_ = lean_ctor_get(v_client_1023_, 1);
lean_inc_ref(v_serverToClient_1026_);
lean_dec_ref(v_client_1023_);
v___x_1027_ = lean_box_uint64(v_expect_1024_);
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___x_1029_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_1026_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__0___boxed(lean_object* v_client_1030_, lean_object* v_expect_1031_, lean_object* v___y_1032_){
_start:
{
uint64_t v_expect_boxed_1033_; lean_object* v_res_1034_; 
v_expect_boxed_1033_ = lean_unbox_uint64(v_expect_1031_);
lean_dec_ref(v_expect_1031_);
v_res_1034_ = l_Std_Http_Internal_instTransportClient___lam__0(v_client_1030_, v_expect_boxed_1033_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__1(lean_object* v_client_1035_, lean_object* v_data_1036_){
_start:
{
lean_object* v_clientToServer_1038_; lean_object* v___x_1039_; 
v_clientToServer_1038_ = lean_ctor_get(v_client_1035_, 0);
lean_inc_ref(v_clientToServer_1038_);
lean_dec_ref(v_client_1035_);
v___x_1039_ = l_Std_Http_Internal_Mock_sendAll(v_clientToServer_1038_, v_data_1036_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__1___boxed(lean_object* v_client_1040_, lean_object* v_data_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_Http_Internal_instTransportClient___lam__1(v_client_1040_, v_data_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__2(lean_object* v_client_1044_, uint64_t v_x_1045_){
_start:
{
lean_object* v_serverToClient_1046_; lean_object* v___x_1047_; 
v_serverToClient_1046_ = lean_ctor_get(v_client_1044_, 1);
lean_inc_ref(v_serverToClient_1046_);
lean_dec_ref(v_client_1044_);
v___x_1047_ = l_Std_CloseableChannel_recvSelector___redArg(v_serverToClient_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__2___boxed(lean_object* v_client_1048_, lean_object* v_x_1049_){
_start:
{
uint64_t v_x_176__boxed_1050_; lean_object* v_res_1051_; 
v_x_176__boxed_1050_ = lean_unbox_uint64(v_x_1049_);
lean_dec_ref(v_x_1049_);
v_res_1051_ = l_Std_Http_Internal_instTransportClient___lam__2(v_client_1048_, v_x_176__boxed_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__3(lean_object* v_x_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Internal_instTransportClient___lam__3___closed__1));
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__3___boxed(lean_object* v_x_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Std_Http_Internal_instTransportClient___lam__3(v_x_1060_);
lean_dec_ref(v_x_1060_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__0(lean_object* v_server_1075_, uint64_t v_expect_1076_){
_start:
{
lean_object* v_clientToServer_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_clientToServer_1078_ = lean_ctor_get(v_server_1075_, 0);
lean_inc_ref(v_clientToServer_1078_);
lean_dec_ref(v_server_1075_);
v___x_1079_ = lean_box_uint64(v_expect_1076_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
v___x_1081_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_1078_, v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__0___boxed(lean_object* v_server_1082_, lean_object* v_expect_1083_, lean_object* v___y_1084_){
_start:
{
uint64_t v_expect_boxed_1085_; lean_object* v_res_1086_; 
v_expect_boxed_1085_ = lean_unbox_uint64(v_expect_1083_);
lean_dec_ref(v_expect_1083_);
v_res_1086_ = l_Std_Http_Internal_instTransportServer___lam__0(v_server_1082_, v_expect_boxed_1085_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__1(lean_object* v_server_1087_, lean_object* v_data_1088_){
_start:
{
lean_object* v_serverToClient_1090_; lean_object* v___x_1091_; 
v_serverToClient_1090_ = lean_ctor_get(v_server_1087_, 1);
lean_inc_ref(v_serverToClient_1090_);
lean_dec_ref(v_server_1087_);
v___x_1091_ = l_Std_Http_Internal_Mock_sendAll(v_serverToClient_1090_, v_data_1088_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__1___boxed(lean_object* v_server_1092_, lean_object* v_data_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Std_Http_Internal_instTransportServer___lam__1(v_server_1092_, v_data_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__2(lean_object* v_server_1096_, uint64_t v_x_1097_){
_start:
{
lean_object* v_clientToServer_1098_; lean_object* v___x_1099_; 
v_clientToServer_1098_ = lean_ctor_get(v_server_1096_, 0);
lean_inc_ref(v_clientToServer_1098_);
lean_dec_ref(v_server_1096_);
v___x_1099_ = l_Std_CloseableChannel_recvSelector___redArg(v_clientToServer_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__2___boxed(lean_object* v_server_1100_, lean_object* v_x_1101_){
_start:
{
uint64_t v_x_176__boxed_1102_; lean_object* v_res_1103_; 
v_x_176__boxed_1102_ = lean_unbox_uint64(v_x_1101_);
lean_dec_ref(v_x_1101_);
v_res_1103_ = l_Std_Http_Internal_instTransportServer___lam__2(v_server_1100_, v_x_176__boxed_1102_);
return v_res_1103_;
}
}
lean_object* runtime_initialize_Std_Http_Protocol_H1(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Transport(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Http_Protocol_H1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Transport(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Protocol_H1(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Transport(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Protocol_H1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Transport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Transport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Transport(builtin);
}
#ifdef __cplusplus
}
#endif

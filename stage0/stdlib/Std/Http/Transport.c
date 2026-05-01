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
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_uint64_dec_le(uint64_t, uint64_t);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CloseableChannel_send___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object*);
lean_object* l_Std_CloseableChannel_close___redArg(lean_object*);
lean_object* l_Std_CloseableChannel_recv___redArg(lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t);
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_send(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instTransportClient___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___lam__2___closed__0_value)} };
static const lean_object* l_Std_Http_instTransportClient___lam__5___closed__0 = (const lean_object*)&l_Std_Http_instTransportClient___lam__5___closed__0_value;
static const lean_closure_object l_Std_Http_instTransportClient___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__4___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___lam__5___closed__0_value)} };
static const lean_object* l_Std_Http_instTransportClient___lam__5___closed__1 = (const lean_object*)&l_Std_Http_instTransportClient___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__6___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instTransportClient___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instTransportClient___closed__0 = (const lean_object*)&l_Std_Http_instTransportClient___closed__0_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__5___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instTransportClient___closed__1 = (const lean_object*)&l_Std_Http_instTransportClient___closed__1_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recvSelector___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instTransportClient___closed__2 = (const lean_object*)&l_Std_Http_instTransportClient___closed__2_value;
static const lean_closure_object l_Std_Http_instTransportClient___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instTransportClient___lam__6___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instTransportClient___closed__3 = (const lean_object*)&l_Std_Http_instTransportClient___closed__3_value;
static const lean_ctor_object l_Std_Http_instTransportClient___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_instTransportClient___closed__0_value),((lean_object*)&l_Std_Http_instTransportClient___closed__1_value),((lean_object*)&l_Std_Http_instTransportClient___closed__2_value),((lean_object*)&l_Std_Http_instTransportClient___closed__3_value)}};
static const lean_object* l_Std_Http_instTransportClient___closed__4 = (const lean_object*)&l_Std_Http_instTransportClient___closed__4_value;
LEAN_EXPORT const lean_object* l_Std_Http_instTransportClient = (const lean_object*)&l_Std_Http_instTransportClient___closed__4_value;
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(size_t, lean_object*, lean_object*, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Internal_instTransportClient___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportClient___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__0 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__0_value;
static const lean_closure_object l_Std_Http_Internal_instTransportClient___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportClient___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__1 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__1_value;
static const lean_closure_object l_Std_Http_Internal_instTransportClient___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instTransportClient___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__2 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__2_value;
static const lean_closure_object l_Std_Http_Internal_instTransportClient___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Mock_Client_close___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__3 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__3_value;
static const lean_ctor_object l_Std_Http_Internal_instTransportClient___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__0_value),((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__1_value),((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__2_value),((lean_object*)&l_Std_Http_Internal_instTransportClient___closed__3_value)}};
static const lean_object* l_Std_Http_Internal_instTransportClient___closed__4 = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__4_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_instTransportClient = (const lean_object*)&l_Std_Http_Internal_instTransportClient___closed__4_value;
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
static const lean_ctor_object l_Std_Http_Internal_instTransportServer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_instTransportServer___closed__0_value),((lean_object*)&l_Std_Http_Internal_instTransportServer___closed__1_value),((lean_object*)&l_Std_Http_Internal_instTransportServer___closed__2_value),((lean_object*)&l_Std_Http_Internal_instTransportServer___closed__3_value)}};
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
lean_dec_ref(v_x_10_);
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
lean_dec_ref(v_a_21_);
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
lean_object* v___f_49_; lean_object* v_val_51_; lean_object* v___x_57_; 
v___f_49_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__2___closed__2));
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
v_val_51_ = v___x_63_;
goto v___jp_50_;
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
v_val_51_ = v___x_71_;
goto v___jp_50_;
}
}
}
v___jp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; lean_object* v___x_56_; 
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_val_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = 0;
v___x_56_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_54_, v___x_55_, v___x_53_, v___f_49_);
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
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3(lean_object* v___x_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_mk_io_user_error(v___x_79_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v_val_83_; 
lean_dec_ref(v___x_79_);
v_val_83_ = lean_ctor_get(v_x_80_, 0);
lean_inc(v_val_83_);
return v_val_83_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3___boxed(lean_object* v___x_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Http_instTransportClient___lam__3(v___x_84_, v_x_85_);
lean_dec(v_x_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__4(lean_object* v___f_87_, lean_object* v_x_88_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_98_; 
lean_dec_ref(v___f_87_);
v_a_90_ = lean_ctor_get(v_x_88_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_88_);
if (v_isSharedCheck_98_ == 0)
{
v___x_92_ = v_x_88_;
v_isShared_93_ = v_isSharedCheck_98_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v_x_88_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_98_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_97_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; 
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
}
else
{
lean_object* v_a_99_; 
v_a_99_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_a_99_);
lean_dec_ref(v_x_88_);
if (lean_obj_tag(v_a_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v___f_87_);
v_a_100_ = lean_ctor_get(v_a_99_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_108_ == 0)
{
v___x_102_ = v_a_99_;
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v_a_99_);
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
lean_object* v_a_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_a_109_ = lean_ctor_get(v_a_99_, 0);
lean_inc(v_a_109_);
lean_dec_ref(v_a_99_);
v___x_110_ = lean_io_promise_result_opt(v_a_109_);
lean_dec(v_a_109_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = 0;
v___x_113_ = lean_task_map(v___f_87_, v___x_110_, v___x_111_, v___x_112_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__4___boxed(lean_object* v___f_115_, lean_object* v_x_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_Http_instTransportClient___lam__4(v___f_115_, v_x_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__5(lean_object* v_client_123_, lean_object* v_data_124_){
_start:
{
lean_object* v___f_126_; lean_object* v_val_128_; lean_object* v___x_134_; 
v___f_126_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__5___closed__1));
v___x_134_ = lean_uv_tcp_send(v_client_123_, v_data_124_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 1);
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
v_val_128_ = v___x_140_;
goto v___jp_127_;
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_134_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_134_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 0);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
v_val_128_ = v___x_148_;
goto v___jp_127_;
}
}
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; 
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_val_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = 0;
v___x_133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_131_, v___x_132_, v___x_130_, v___f_126_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__5___boxed(lean_object* v_client_151_, lean_object* v_data_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_Http_instTransportClient___lam__5(v_client_151_, v_data_152_);
lean_dec(v_client_151_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__6(lean_object* v_x_155_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__6___boxed(lean_object* v_x_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Http_instTransportClient___lam__6(v_x_159_);
lean_dec(v_x_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_new(){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_173_ = lean_box(0);
v___x_174_ = l_Std_CloseableChannel_new___redArg(v___x_173_);
v___x_175_ = l_Std_CloseableChannel_new___redArg(v___x_173_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
lean_inc_ref(v___x_176_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_new___boxed(lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_Http_Internal_Mock_new();
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__0(lean_object* v_x_180_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
v_a_182_ = lean_ctor_get(v_x_180_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_180_);
if (v_isSharedCheck_190_ == 0)
{
v___x_184_ = v_x_180_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v_x_180_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_189_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_200_; 
v_a_191_ = lean_ctor_get(v_x_180_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_x_180_);
if (v_isSharedCheck_200_ == 0)
{
v___x_193_ = v_x_180_;
v_isShared_194_ = v_isSharedCheck_200_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v_x_180_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_200_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v_a_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_195_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_199_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__0___boxed(lean_object* v_x_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_Http_Internal_Mock_recvJoined___lam__0(v_x_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__1(lean_object* v_a_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v_a_207_ = lean_ctor_get(v_x_205_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v_x_205_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v_x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref(v_x_205_);
v___x_216_ = l_IO_Promise_result_x21___redArg(v_a_204_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed(lean_object* v_a_218_, lean_object* v_x_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_Http_Internal_Mock_recvJoined___lam__1(v_a_218_, v_x_219_);
lean_dec(v_a_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(lean_object* v_b_222_, lean_object* v_x_223_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
lean_dec_ref(v_b_222_);
v_a_225_ = lean_ctor_get(v_x_223_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_233_ == 0)
{
v___x_227_ = v_x_223_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v_x_223_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_260_; 
v_a_234_ = lean_ctor_get(v_x_223_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_260_ == 0)
{
v___x_236_ = v_x_223_;
v_isShared_237_ = v_isSharedCheck_260_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v_x_223_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_260_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
if (lean_obj_tag(v_a_234_) == 0)
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_b_222_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_238_);
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
else
{
lean_object* v_val_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_259_; 
v_val_243_ = lean_ctor_get(v_a_234_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v_a_234_);
if (v_isSharedCheck_259_ == 0)
{
v___x_245_ = v_a_234_;
v_isShared_246_ = v_isSharedCheck_259_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_val_243_);
lean_dec(v_a_234_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_259_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_byte_array_size(v_b_222_);
v___x_249_ = lean_byte_array_size(v_val_243_);
v___x_250_ = 0;
v___x_251_ = lean_byte_array_copy_slice(v_val_243_, v___x_247_, v_b_222_, v___x_248_, v___x_249_, v___x_250_);
lean_dec(v_val_243_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_251_);
v___x_253_ = v___x_245_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_258_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_255_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_253_);
v___x_255_ = v___x_236_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1___boxed(lean_object* v_b_261_, lean_object* v_x_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(v_b_261_, v_x_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0___boxed(lean_object* v_promise_265_, lean_object* v_recvChan_266_, lean_object* v_expect_267_, lean_object* v_prio_268_, lean_object* v_x_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(v_promise_265_, v_recvChan_266_, v_expect_267_, v_prio_268_, v_x_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(lean_object* v_recvChan_272_, lean_object* v_expect_273_, lean_object* v_prio_274_, lean_object* v_promise_275_, lean_object* v_b_276_){
_start:
{
lean_object* v_a_279_; lean_object* v___f_282_; lean_object* v___f_283_; 
lean_inc(v_prio_274_);
lean_inc(v_expect_273_);
lean_inc_ref(v_recvChan_272_);
lean_inc(v_promise_275_);
v___f_282_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_282_, 0, v_promise_275_);
lean_closure_set(v___f_282_, 1, v_recvChan_272_);
lean_closure_set(v___f_282_, 2, v_expect_273_);
lean_closure_set(v___f_282_, 3, v_prio_274_);
lean_inc_ref(v_b_276_);
v___f_283_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_283_, 0, v_b_276_);
if (lean_obj_tag(v_expect_273_) == 1)
{
lean_object* v_val_307_; lean_object* v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; uint8_t v___x_311_; 
v_val_307_ = lean_ctor_get(v_expect_273_, 0);
v___x_308_ = lean_byte_array_size(v_b_276_);
v___x_309_ = lean_uint64_of_nat(v___x_308_);
v___x_310_ = lean_unbox_uint64(v_val_307_);
v___x_311_ = lean_uint64_dec_le(v___x_310_, v___x_309_);
if (v___x_311_ == 0)
{
lean_dec_ref(v_b_276_);
goto v___jp_284_;
}
else
{
lean_dec_ref(v_expect_273_);
lean_dec_ref(v___f_283_);
lean_dec_ref(v___f_282_);
lean_dec(v_prio_274_);
lean_dec_ref(v_recvChan_272_);
v_a_279_ = v_b_276_;
goto v___jp_278_;
}
}
else
{
lean_dec_ref(v_b_276_);
goto v___jp_284_;
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v_a_279_);
v___x_281_ = lean_io_promise_resolve(v___x_280_, v_promise_275_);
lean_dec(v_promise_275_);
return v___x_281_;
}
v___jp_284_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; 
lean_inc_ref(v_recvChan_272_);
v___x_285_ = l_Std_CloseableChannel_tryRecv___redArg(v_recvChan_272_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = 0;
v___x_290_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_288_, v___x_289_, v___x_287_, v___f_283_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; 
lean_dec_ref(v___f_282_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref(v___x_290_);
if (lean_obj_tag(v_a_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_300_; 
lean_dec(v_prio_274_);
lean_dec(v_expect_273_);
lean_dec_ref(v_recvChan_272_);
v_a_292_ = lean_ctor_get(v_a_291_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_300_ == 0)
{
v___x_294_ = v_a_291_;
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v_a_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_300_;
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
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_299_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; 
v___x_298_ = lean_io_promise_resolve(v___x_297_, v_promise_275_);
lean_dec(v_promise_275_);
return v___x_298_;
}
}
}
else
{
lean_object* v_a_301_; 
v_a_301_ = lean_ctor_get(v_a_291_, 0);
lean_inc(v_a_301_);
lean_dec_ref(v_a_291_);
if (lean_obj_tag(v_a_301_) == 0)
{
lean_object* v_a_302_; 
lean_dec(v_prio_274_);
lean_dec(v_expect_273_);
lean_dec_ref(v_recvChan_272_);
v_a_302_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref(v_a_301_);
v_a_279_ = v_a_302_;
goto v___jp_278_;
}
else
{
lean_object* v_a_303_; 
v_a_303_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_a_303_);
lean_dec_ref(v_a_301_);
v_b_276_ = v_a_303_;
goto _start;
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_306_; 
lean_dec(v_promise_275_);
lean_dec(v_expect_273_);
lean_dec_ref(v_recvChan_272_);
v_a_305_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_a_305_);
lean_dec_ref(v___x_290_);
v___x_306_ = l_BaseIO_chainTask___redArg(v_a_305_, v___f_282_, v_prio_274_, v___x_289_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(lean_object* v_promise_312_, lean_object* v_recvChan_313_, lean_object* v_expect_314_, lean_object* v_prio_315_, lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_prio_315_);
lean_dec(v_expect_314_);
lean_dec_ref(v_recvChan_313_);
v_a_318_ = lean_ctor_get(v_x_316_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_326_ == 0)
{
v___x_320_ = v_x_316_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v_x_316_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_325_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; 
v___x_324_ = lean_io_promise_resolve(v___x_323_, v_promise_312_);
lean_dec(v_promise_312_);
return v___x_324_;
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_338_; 
v_a_327_ = lean_ctor_get(v_x_316_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_338_ == 0)
{
v___x_329_ = v_x_316_;
v_isShared_330_ = v_isSharedCheck_338_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v_x_316_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_338_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
if (lean_obj_tag(v_a_327_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; 
lean_dec(v_prio_315_);
lean_dec(v_expect_314_);
lean_dec_ref(v_recvChan_313_);
v_a_331_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_a_331_);
lean_dec_ref(v_a_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v_a_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_331_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_io_promise_resolve(v___x_333_, v_promise_312_);
lean_dec(v_promise_312_);
return v___x_334_;
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_337_; 
lean_del_object(v___x_329_);
v_a_336_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_a_336_);
lean_dec_ref(v_a_327_);
v___x_337_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_313_, v_expect_314_, v_prio_315_, v_promise_312_, v_a_336_);
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___boxed(lean_object* v_recvChan_339_, lean_object* v_expect_340_, lean_object* v_prio_341_, lean_object* v_promise_342_, lean_object* v_b_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_339_, v_expect_340_, v_prio_341_, v_promise_342_, v_b_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2(lean_object* v_recvChan_346_, lean_object* v_expect_347_, lean_object* v___x_348_, lean_object* v_val_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v_val_349_);
lean_dec(v___x_348_);
lean_dec(v_expect_347_);
lean_dec_ref(v_recvChan_346_);
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
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_373_; 
v_a_361_ = lean_ctor_get(v_x_350_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_373_ == 0)
{
v___x_363_ = v_x_350_;
v_isShared_364_ = v_isSharedCheck_373_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v_x_350_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_373_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___f_366_; lean_object* v___x_368_; 
lean_inc(v_a_361_);
lean_inc(v___x_348_);
v___x_365_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_346_, v_expect_347_, v___x_348_, v_a_361_, v_val_349_);
v___f_366_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed), 3, 1);
lean_closure_set(v___f_366_, 0, v_a_361_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_365_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
v___x_370_ = 0;
v___x_371_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_348_, v___x_370_, v___x_369_, v___f_366_);
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed(lean_object* v_recvChan_374_, lean_object* v_expect_375_, lean_object* v___x_376_, lean_object* v_val_377_, lean_object* v_x_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Http_Internal_Mock_recvJoined___lam__2(v_recvChan_374_, v_expect_375_, v___x_376_, v_val_377_, v_x_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3(lean_object* v_recvChan_381_, lean_object* v_expect_382_, lean_object* v___f_383_, lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v___f_383_);
lean_dec(v_expect_382_);
lean_dec_ref(v_recvChan_381_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_x_384_);
return v___x_386_;
}
else
{
lean_object* v_a_387_; 
v_a_387_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_a_387_);
if (lean_obj_tag(v_a_387_) == 0)
{
lean_object* v___x_388_; 
lean_dec_ref(v___f_383_);
lean_dec(v_expect_382_);
lean_dec_ref(v_recvChan_381_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v_x_384_);
return v___x_388_;
}
else
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_409_; 
v_isSharedCheck_409_ = !lean_is_exclusive(v_x_384_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v_x_384_, 0);
lean_dec(v_unused_410_);
v___x_390_ = v_x_384_;
v_isShared_391_ = v_isSharedCheck_409_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_x_384_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_409_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_val_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_408_; 
v_val_392_ = lean_ctor_get(v_a_387_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v_a_387_);
if (v_isSharedCheck_408_ == 0)
{
v___x_394_ = v_a_387_;
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_val_392_);
lean_dec(v_a_387_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___f_398_; lean_object* v___x_400_; 
v___x_396_ = lean_io_promise_new();
v___x_397_ = lean_unsigned_to_nat(0u);
v___f_398_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed), 6, 4);
lean_closure_set(v___f_398_, 0, v_recvChan_381_);
lean_closure_set(v___f_398_, 1, v_expect_382_);
lean_closure_set(v___f_398_, 2, v___x_397_);
lean_closure_set(v___f_398_, 3, v_val_392_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_396_);
v___x_400_ = v___x_390_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_396_);
v___x_400_ = v_reuseFailAlloc_407_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 0);
lean_ctor_set(v___x_394_, 0, v___x_400_);
v___x_402_ = v___x_394_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_406_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = 0;
v___x_404_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_397_, v___x_403_, v___x_402_, v___f_398_);
v___x_405_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_397_, v___x_403_, v___x_404_, v___f_383_);
return v___x_405_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed(lean_object* v_recvChan_411_, lean_object* v_expect_412_, lean_object* v___f_413_, lean_object* v_x_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_Http_Internal_Mock_recvJoined___lam__3(v_recvChan_411_, v_expect_412_, v___f_413_, v_x_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__4(lean_object* v_a_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v_a_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5(lean_object* v___f_419_, lean_object* v___f_420_, lean_object* v_x_421_){
_start:
{
if (lean_obj_tag(v_x_421_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_431_; 
lean_dec_ref(v___f_420_);
lean_dec_ref(v___f_419_);
v_a_423_ = lean_ctor_get(v_x_421_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_421_);
if (v_isSharedCheck_431_ == 0)
{
v___x_425_ = v_x_421_;
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v_x_421_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_430_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_432_ = lean_ctor_get(v_x_421_, 0);
lean_inc(v_a_432_);
lean_dec_ref(v_x_421_);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = 0;
v___x_435_ = lean_task_map(v___f_419_, v_a_432_, v___x_433_, v___x_434_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
v___x_437_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_433_, v___x_434_, v___x_436_, v___f_420_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed(lean_object* v___f_438_, lean_object* v___f_439_, lean_object* v_x_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_Http_Internal_Mock_recvJoined___lam__5(v___f_438_, v___f_439_, v_x_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined(lean_object* v_recvChan_445_, lean_object* v_expect_446_){
_start:
{
lean_object* v___x_448_; lean_object* v___f_449_; lean_object* v___f_450_; lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; 
lean_inc_ref(v_recvChan_445_);
v___x_448_ = l_Std_CloseableChannel_recv___redArg(v_recvChan_445_);
v___f_449_ = ((lean_object*)(l_Std_Http_Internal_Mock_recvJoined___closed__0));
v___f_450_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed), 5, 3);
lean_closure_set(v___f_450_, 0, v_recvChan_445_);
lean_closure_set(v___f_450_, 1, v_expect_446_);
lean_closure_set(v___f_450_, 2, v___f_449_);
v___f_451_ = ((lean_object*)(l_Std_Http_Internal_Mock_recvJoined___closed__1));
v___f_452_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed), 4, 2);
lean_closure_set(v___f_452_, 0, v___f_451_);
lean_closure_set(v___f_452_, 1, v___f_450_);
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_448_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = 0;
v___x_457_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_455_, v___x_456_, v___x_454_, v___f_452_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___boxed(lean_object* v_recvChan_458_, lean_object* v_expect_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_Http_Internal_Mock_recvJoined(v_recvChan_458_, v_expect_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__0(lean_object* v___y_464_){
_start:
{
lean_object* v___y_466_; 
if (lean_obj_tag(v___y_464_) == 0)
{
lean_object* v_a_469_; uint8_t v___x_470_; 
v_a_469_ = lean_ctor_get(v___y_464_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___y_464_);
v___x_470_ = lean_unbox(v_a_469_);
lean_dec(v_a_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___lam__0___closed__0));
v___y_466_ = v___x_471_;
goto v___jp_465_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___lam__0___closed__1));
v___y_466_ = v___x_472_;
goto v___jp_465_;
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
v_a_473_ = lean_ctor_get(v___y_464_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___y_464_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___y_464_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___y_464_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
v___jp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc_ref(v___y_466_);
v___x_467_ = lean_mk_io_user_error(v___y_466_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__1(lean_object* v___f_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v___f_481_);
v_a_484_ = lean_ctor_get(v_x_482_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_492_ == 0)
{
v___x_486_ = v_x_482_;
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v_x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_491_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_a_493_ = lean_ctor_get(v_x_482_, 0);
lean_inc(v_a_493_);
lean_dec_ref(v_x_482_);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = 0;
v___x_496_ = lean_task_map(v___f_481_, v_a_493_, v___x_494_, v___x_495_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__1___boxed(lean_object* v___f_498_, lean_object* v_x_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_Http_Internal_Mock_send___lam__1(v___f_498_, v_x_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send(lean_object* v_sendChan_505_, lean_object* v_data_506_){
_start:
{
lean_object* v___x_508_; lean_object* v___f_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; 
v___x_508_ = l_Std_CloseableChannel_send___redArg(v_sendChan_505_, v_data_506_);
v___f_509_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___closed__1));
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = 0;
v___x_514_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_512_, v___x_513_, v___x_511_, v___f_509_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___boxed(lean_object* v_sendChan_515_, lean_object* v_data_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Http_Internal_Mock_send(v_sendChan_515_, v_data_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0(lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_x_523_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
lean_dec_ref(v_x_523_);
v___x_526_ = ((lean_object*)(l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1));
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___boxed(lean_object* v_x_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_Http_Internal_Mock_sendAll___lam__0(v_x_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(lean_object* v___x_530_, lean_object* v_x_531_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_541_; 
v_a_533_ = lean_ctor_get(v_x_531_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_541_ == 0)
{
v___x_535_ = v_x_531_;
v_isShared_536_ = v_isSharedCheck_541_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v_x_531_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_541_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_540_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
}
else
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_550_; 
v_isSharedCheck_550_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_x_531_, 0);
lean_dec(v_unused_551_);
v___x_543_ = v_x_531_;
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
else
{
lean_dec(v_x_531_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_530_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_545_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed(lean_object* v___x_552_, lean_object* v_x_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(v___x_552_, v_x_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed(lean_object* v_i_558_, lean_object* v_sendChan_559_, lean_object* v_as_560_, lean_object* v_sz_561_, lean_object* v_x_562_, lean_object* v___y_563_){
_start:
{
size_t v_i_boxed_564_; size_t v_sz_boxed_565_; lean_object* v_res_566_; 
v_i_boxed_564_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_sz_boxed_565_ = lean_unbox_usize(v_sz_561_);
lean_dec(v_sz_561_);
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(v_i_boxed_564_, v_sendChan_559_, v_as_560_, v_sz_boxed_565_, v_x_562_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(lean_object* v_sendChan_567_, lean_object* v_as_568_, size_t v_sz_569_, size_t v_i_570_, lean_object* v_b_571_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_lt(v_i_570_, v_sz_569_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec_ref(v_as_568_);
lean_dec_ref(v_sendChan_567_);
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v_b_571_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
else
{
lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v___f_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
v_a_576_ = lean_array_uget_borrowed(v_as_568_, v_i_570_);
lean_inc(v_a_576_);
lean_inc_ref(v_sendChan_567_);
v___x_577_ = l_Std_Http_Internal_Mock_send(v_sendChan_567_, v_a_576_);
v___f_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0));
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = 0;
v___x_581_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_579_, v___x_580_, v___x_577_, v___f_578_);
v___x_582_ = lean_box_usize(v_i_570_);
v___x_583_ = lean_box_usize(v_sz_569_);
v___f_584_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed), 6, 4);
lean_closure_set(v___f_584_, 0, v___x_582_);
lean_closure_set(v___f_584_, 1, v_sendChan_567_);
lean_closure_set(v___f_584_, 2, v_as_568_);
lean_closure_set(v___f_584_, 3, v___x_583_);
v___x_585_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_579_, v___x_580_, v___x_581_, v___f_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(size_t v_i_586_, lean_object* v_sendChan_587_, lean_object* v_as_588_, size_t v_sz_589_, lean_object* v_x_590_){
_start:
{
if (lean_obj_tag(v_x_590_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_as_588_);
lean_dec_ref(v_sendChan_587_);
v_a_592_ = lean_ctor_get(v_x_590_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_590_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v_x_590_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v_x_590_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_599_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_620_; 
v_a_601_ = lean_ctor_get(v_x_590_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_590_);
if (v_isSharedCheck_620_ == 0)
{
v___x_603_ = v_x_590_;
v_isShared_604_ = v_isSharedCheck_620_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v_x_590_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_620_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
if (lean_obj_tag(v_a_601_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_as_588_);
lean_dec_ref(v_sendChan_587_);
v_a_605_ = lean_ctor_get(v_a_601_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_615_ == 0)
{
v___x_607_ = v_a_601_;
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v_a_601_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v_a_605_);
v___x_610_ = v___x_603_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_614_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_610_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v_a_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
lean_del_object(v___x_603_);
v_a_616_ = lean_ctor_get(v_a_601_, 0);
lean_inc(v_a_616_);
lean_dec_ref(v_a_601_);
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_add(v_i_586_, v___x_617_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_587_, v_as_588_, v_sz_589_, v___x_618_, v_a_616_);
return v___x_619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___boxed(lean_object* v_sendChan_621_, lean_object* v_as_622_, lean_object* v_sz_623_, lean_object* v_i_624_, lean_object* v_b_625_, lean_object* v___y_626_){
_start:
{
size_t v_sz_boxed_627_; size_t v_i_boxed_628_; lean_object* v_res_629_; 
v_sz_boxed_627_ = lean_unbox_usize(v_sz_623_);
lean_dec(v_sz_623_);
v_i_boxed_628_ = lean_unbox_usize(v_i_624_);
lean_dec(v_i_624_);
v_res_629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_621_, v_as_622_, v_sz_boxed_627_, v_i_boxed_628_, v_b_625_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll(lean_object* v_sendChan_631_, lean_object* v_data_632_){
_start:
{
lean_object* v___x_634_; size_t v_sz_635_; size_t v___x_636_; lean_object* v___x_637_; lean_object* v___f_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; 
v___x_634_ = lean_box(0);
v_sz_635_ = lean_array_size(v_data_632_);
v___x_636_ = ((size_t)0ULL);
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_631_, v_data_632_, v_sz_635_, v___x_636_, v___x_634_);
v___f_638_ = ((lean_object*)(l_Std_Http_Internal_Mock_sendAll___closed__0));
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = 0;
v___x_641_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_639_, v___x_640_, v___x_637_, v___f_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___boxed(lean_object* v_sendChan_642_, lean_object* v_data_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_Http_Internal_Mock_sendAll(v_sendChan_642_, v_data_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvSelector(lean_object* v_recvChan_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_CloseableChannel_recvSelector___redArg(v_recvChan_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan(lean_object* v_client_648_){
_start:
{
lean_object* v_serverToClient_649_; 
v_serverToClient_649_ = lean_ctor_get(v_client_648_, 1);
lean_inc_ref(v_serverToClient_649_);
return v_serverToClient_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan___boxed(lean_object* v_client_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Http_Internal_Mock_Client_getRecvChan(v_client_650_);
lean_dec_ref(v_client_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan(lean_object* v_client_652_){
_start:
{
lean_object* v_clientToServer_653_; 
v_clientToServer_653_ = lean_ctor_get(v_client_652_, 0);
lean_inc_ref(v_clientToServer_653_);
return v_clientToServer_653_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan___boxed(lean_object* v_client_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_Http_Internal_Mock_Client_getSendChan(v_client_654_);
lean_dec_ref(v_client_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_send(lean_object* v_client_656_, lean_object* v_data_657_){
_start:
{
lean_object* v_clientToServer_659_; lean_object* v___x_660_; 
v_clientToServer_659_ = lean_ctor_get(v_client_656_, 0);
lean_inc_ref(v_clientToServer_659_);
lean_dec_ref(v_client_656_);
v___x_660_ = l_Std_Http_Internal_Mock_send(v_clientToServer_659_, v_data_657_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_send___boxed(lean_object* v_client_661_, lean_object* v_data_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_Http_Internal_Mock_Client_send(v_client_661_, v_data_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f(lean_object* v_client_665_, lean_object* v_expect_666_){
_start:
{
lean_object* v_serverToClient_668_; lean_object* v___x_669_; 
v_serverToClient_668_ = lean_ctor_get(v_client_665_, 1);
lean_inc_ref(v_serverToClient_668_);
lean_dec_ref(v_client_665_);
v___x_669_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_668_, v_expect_666_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f___boxed(lean_object* v_client_670_, lean_object* v_expect_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_Http_Internal_Mock_Client_recv_x3f(v_client_670_, v_expect_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(lean_object* v___x_674_, lean_object* v_b_675_){
_start:
{
lean_object* v___x_677_; 
lean_inc_ref(v___x_674_);
v___x_677_ = l_Std_CloseableChannel_tryRecv___redArg(v___x_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_dec_ref(v___x_674_);
return v_b_675_;
}
else
{
lean_object* v_val_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; 
v_val_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_val_678_);
lean_dec_ref(v___x_677_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_byte_array_size(v_b_675_);
v___x_681_ = lean_byte_array_size(v_val_678_);
v___x_682_ = 0;
v___x_683_ = lean_byte_array_copy_slice(v_val_678_, v___x_679_, v_b_675_, v___x_680_, v___x_681_, v___x_682_);
lean_dec(v_val_678_);
v_b_675_ = v___x_683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___boxed(lean_object* v___x_685_, lean_object* v_b_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(v___x_685_, v_b_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(lean_object* v_client_689_){
_start:
{
lean_object* v_serverToClient_691_; lean_object* v___x_692_; 
v_serverToClient_691_ = lean_ctor_get(v_client_689_, 1);
lean_inc_ref_n(v_serverToClient_691_, 2);
lean_dec_ref(v_client_689_);
v___x_692_ = l_Std_CloseableChannel_tryRecv___redArg(v_serverToClient_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_dec_ref(v_serverToClient_691_);
return v___x_692_;
}
else
{
lean_object* v_val_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_val_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_val_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(v_serverToClient_691_, v_val_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg___boxed(lean_object* v_client_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f(lean_object* v_client_705_, uint64_t v___expect_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_705_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___boxed(lean_object* v_client_709_, lean_object* v___expect_710_, lean_object* v_a_711_){
_start:
{
uint64_t v___expect_boxed_712_; lean_object* v_res_713_; 
v___expect_boxed_712_ = lean_unbox_uint64(v___expect_710_);
lean_dec_ref(v___expect_710_);
v_res_713_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f(v_client_709_, v___expect_boxed_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_close(lean_object* v_client_718_){
_start:
{
lean_object* v_clientToServer_720_; lean_object* v_serverToClient_721_; uint8_t v___x_749_; 
v_clientToServer_720_ = lean_ctor_get(v_client_718_, 0);
lean_inc_ref_n(v_clientToServer_720_, 2);
v_serverToClient_721_ = lean_ctor_get(v_client_718_, 1);
lean_inc_ref(v_serverToClient_721_);
lean_dec_ref(v_client_718_);
v___x_749_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_720_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_720_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_dec_ref(v___x_750_);
goto v___jp_722_;
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v_serverToClient_721_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_764_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_764_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_764_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
uint8_t v___x_755_; 
v___x_755_ = lean_unbox(v_a_751_);
lean_dec(v_a_751_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_756_);
v___x_758_ = v___x_753_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_760_);
v___x_762_ = v___x_753_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
else
{
lean_dec_ref(v_clientToServer_720_);
goto v___jp_722_;
}
v___jp_722_:
{
uint8_t v___x_723_; 
lean_inc_ref(v_serverToClient_721_);
v___x_723_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_721_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_721_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_746_; 
v_a_733_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_746_ == 0)
{
v___x_735_ = v___x_724_;
v_isShared_736_ = v_isSharedCheck_746_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_724_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_746_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
uint8_t v___x_737_; 
v___x_737_ = lean_unbox(v_a_733_);
lean_dec(v_a_733_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_738_);
v___x_740_ = v___x_735_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_742_);
v___x_744_ = v___x_735_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec_ref(v_serverToClient_721_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_close___boxed(lean_object* v_client_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_Http_Internal_Mock_Client_close(v_client_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan(lean_object* v_server_768_){
_start:
{
lean_object* v_clientToServer_769_; 
v_clientToServer_769_ = lean_ctor_get(v_server_768_, 0);
lean_inc_ref(v_clientToServer_769_);
return v_clientToServer_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan___boxed(lean_object* v_server_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_Http_Internal_Mock_Server_getRecvChan(v_server_770_);
lean_dec_ref(v_server_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan(lean_object* v_server_772_){
_start:
{
lean_object* v_serverToClient_773_; 
v_serverToClient_773_ = lean_ctor_get(v_server_772_, 1);
lean_inc_ref(v_serverToClient_773_);
return v_serverToClient_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan___boxed(lean_object* v_server_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_Http_Internal_Mock_Server_getSendChan(v_server_774_);
lean_dec_ref(v_server_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_send(lean_object* v_server_776_, lean_object* v_data_777_){
_start:
{
lean_object* v_serverToClient_779_; lean_object* v___x_780_; 
v_serverToClient_779_ = lean_ctor_get(v_server_776_, 1);
lean_inc_ref(v_serverToClient_779_);
lean_dec_ref(v_server_776_);
v___x_780_ = l_Std_Http_Internal_Mock_send(v_serverToClient_779_, v_data_777_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_send___boxed(lean_object* v_server_781_, lean_object* v_data_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_Http_Internal_Mock_Server_send(v_server_781_, v_data_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f(lean_object* v_server_785_, lean_object* v_expect_786_){
_start:
{
lean_object* v_clientToServer_788_; lean_object* v___x_789_; 
v_clientToServer_788_ = lean_ctor_get(v_server_785_, 0);
lean_inc_ref(v_clientToServer_788_);
lean_dec_ref(v_server_785_);
v___x_789_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_788_, v_expect_786_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f___boxed(lean_object* v_server_790_, lean_object* v_expect_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_Http_Internal_Mock_Server_recv_x3f(v_server_790_, v_expect_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(lean_object* v_server_794_){
_start:
{
lean_object* v_clientToServer_796_; lean_object* v___x_797_; 
v_clientToServer_796_ = lean_ctor_get(v_server_794_, 0);
lean_inc_ref_n(v_clientToServer_796_, 2);
lean_dec_ref(v_server_794_);
v___x_797_ = l_Std_CloseableChannel_tryRecv___redArg(v_clientToServer_796_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_dec_ref(v_clientToServer_796_);
return v___x_797_;
}
else
{
lean_object* v_val_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_val_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_val_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(v_clientToServer_796_, v_val_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg___boxed(lean_object* v_server_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f(lean_object* v_server_810_, uint64_t v___expect_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_810_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___boxed(lean_object* v_server_814_, lean_object* v___expect_815_, lean_object* v_a_816_){
_start:
{
uint64_t v___expect_boxed_817_; lean_object* v_res_818_; 
v___expect_boxed_817_ = lean_unbox_uint64(v___expect_815_);
lean_dec_ref(v___expect_815_);
v_res_818_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f(v_server_814_, v___expect_boxed_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_close(lean_object* v_server_819_){
_start:
{
lean_object* v_clientToServer_821_; lean_object* v_serverToClient_822_; uint8_t v___x_850_; 
v_clientToServer_821_ = lean_ctor_get(v_server_819_, 0);
lean_inc_ref_n(v_clientToServer_821_, 2);
v_serverToClient_822_ = lean_ctor_get(v_server_819_, 1);
lean_inc_ref(v_serverToClient_822_);
lean_dec_ref(v_server_819_);
v___x_850_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_821_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_821_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_dec_ref(v___x_851_);
goto v___jp_823_;
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v_serverToClient_822_);
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_865_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_865_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_865_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v___x_856_; 
v___x_856_ = lean_unbox(v_a_852_);
lean_dec(v_a_852_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_861_);
v___x_863_ = v___x_854_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
else
{
lean_dec_ref(v_clientToServer_821_);
goto v___jp_823_;
}
v___jp_823_:
{
uint8_t v___x_824_; 
lean_inc_ref(v_serverToClient_822_);
v___x_824_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_822_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_822_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_847_; 
v_a_834_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_847_ == 0)
{
v___x_836_ = v___x_825_;
v_isShared_837_ = v_isSharedCheck_847_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_825_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_847_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
uint8_t v___x_838_; 
v___x_838_ = lean_unbox(v_a_834_);
lean_dec(v_a_834_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_843_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_serverToClient_822_);
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_close___boxed(lean_object* v_server_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_Http_Internal_Mock_Server_close(v_server_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__0(lean_object* v_client_869_, uint64_t v_expect_870_){
_start:
{
lean_object* v_serverToClient_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_serverToClient_872_ = lean_ctor_get(v_client_869_, 1);
lean_inc_ref(v_serverToClient_872_);
lean_dec_ref(v_client_869_);
v___x_873_ = lean_box_uint64(v_expect_870_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
v___x_875_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_872_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__0___boxed(lean_object* v_client_876_, lean_object* v_expect_877_, lean_object* v___y_878_){
_start:
{
uint64_t v_expect_boxed_879_; lean_object* v_res_880_; 
v_expect_boxed_879_ = lean_unbox_uint64(v_expect_877_);
lean_dec_ref(v_expect_877_);
v_res_880_ = l_Std_Http_Internal_instTransportClient___lam__0(v_client_876_, v_expect_boxed_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__1(lean_object* v_client_881_, lean_object* v_data_882_){
_start:
{
lean_object* v_clientToServer_884_; lean_object* v___x_885_; 
v_clientToServer_884_ = lean_ctor_get(v_client_881_, 0);
lean_inc_ref(v_clientToServer_884_);
lean_dec_ref(v_client_881_);
v___x_885_ = l_Std_Http_Internal_Mock_sendAll(v_clientToServer_884_, v_data_882_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__1___boxed(lean_object* v_client_886_, lean_object* v_data_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_Http_Internal_instTransportClient___lam__1(v_client_886_, v_data_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__2(lean_object* v_client_890_, uint64_t v_x_891_){
_start:
{
lean_object* v_serverToClient_892_; lean_object* v___x_893_; 
v_serverToClient_892_ = lean_ctor_get(v_client_890_, 1);
lean_inc_ref(v_serverToClient_892_);
lean_dec_ref(v_client_890_);
v___x_893_ = l_Std_CloseableChannel_recvSelector___redArg(v_serverToClient_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__2___boxed(lean_object* v_client_894_, lean_object* v_x_895_){
_start:
{
uint64_t v_x_43__boxed_896_; lean_object* v_res_897_; 
v_x_43__boxed_896_ = lean_unbox_uint64(v_x_895_);
lean_dec_ref(v_x_895_);
v_res_897_ = l_Std_Http_Internal_instTransportClient___lam__2(v_client_894_, v_x_43__boxed_896_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__0(lean_object* v_server_908_, uint64_t v_expect_909_){
_start:
{
lean_object* v_clientToServer_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_clientToServer_911_ = lean_ctor_get(v_server_908_, 0);
lean_inc_ref(v_clientToServer_911_);
lean_dec_ref(v_server_908_);
v___x_912_ = lean_box_uint64(v_expect_909_);
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
v___x_914_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_911_, v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__0___boxed(lean_object* v_server_915_, lean_object* v_expect_916_, lean_object* v___y_917_){
_start:
{
uint64_t v_expect_boxed_918_; lean_object* v_res_919_; 
v_expect_boxed_918_ = lean_unbox_uint64(v_expect_916_);
lean_dec_ref(v_expect_916_);
v_res_919_ = l_Std_Http_Internal_instTransportServer___lam__0(v_server_915_, v_expect_boxed_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__1(lean_object* v_server_920_, lean_object* v_data_921_){
_start:
{
lean_object* v_serverToClient_923_; lean_object* v___x_924_; 
v_serverToClient_923_ = lean_ctor_get(v_server_920_, 1);
lean_inc_ref(v_serverToClient_923_);
lean_dec_ref(v_server_920_);
v___x_924_ = l_Std_Http_Internal_Mock_sendAll(v_serverToClient_923_, v_data_921_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__1___boxed(lean_object* v_server_925_, lean_object* v_data_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Std_Http_Internal_instTransportServer___lam__1(v_server_925_, v_data_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__2(lean_object* v_server_929_, uint64_t v_x_930_){
_start:
{
lean_object* v_clientToServer_931_; lean_object* v___x_932_; 
v_clientToServer_931_ = lean_ctor_get(v_server_929_, 0);
lean_inc_ref(v_clientToServer_931_);
lean_dec_ref(v_server_929_);
v___x_932_ = l_Std_CloseableChannel_recvSelector___redArg(v_clientToServer_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__2___boxed(lean_object* v_server_933_, lean_object* v_x_934_){
_start:
{
uint64_t v_x_43__boxed_935_; lean_object* v_res_936_; 
v_x_43__boxed_935_ = lean_unbox_uint64(v_x_934_);
lean_dec_ref(v_x_934_);
v_res_936_ = l_Std_Http_Internal_instTransportServer___lam__2(v_server_933_, v_x_43__boxed_935_);
return v_res_936_;
}
}
lean_object* runtime_initialize_Std_Http_Protocol_H1(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Transport(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

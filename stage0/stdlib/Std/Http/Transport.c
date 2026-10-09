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
static const lean_ctor_object l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1_value;
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
lean_object* l_Std_Http_instTransportClient___lam__1(lean_object* v___f_9_, lean_object* v_x_10_){
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
LEAN_EXPORT void l_Std_Http_instTransportClient___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_9_ = stack[0].m_obj;
lean_object* v_x_10_ = stack[1].m_obj;
lean_object* v_res_37_;
v_res_37_ = l_Std_Http_instTransportClient___lam__1(v___f_9_, v_x_10_);
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__1___boxed(lean_object* v___f_38_, lean_object* v_x_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_Http_instTransportClient___lam__1(v___f_38_, v_x_39_);
return v_res_41_;
}
}
lean_object* l_Std_Http_instTransportClient___lam__2(lean_object* v_client_47_, uint64_t v_expect_48_){
_start:
{
lean_object* v___f_50_; lean_object* v___x_51_; uint8_t v___x_52_; lean_object* v_val_54_; lean_object* v___x_58_; 
v___f_50_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__2___closed__2));
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = 0;
v___x_58_ = lean_uv_tcp_recv(v_client_47_, v_expect_48_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 1);
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
v_val_54_ = v___x_64_;
goto v___jp_53_;
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
v_a_67_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_58_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_58_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set_tag(v___x_69_, 0);
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
v_val_54_ = v___x_72_;
goto v___jp_53_;
}
}
}
v___jp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v_val_54_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
v___x_57_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_51_, v___x_52_, v___x_56_, v___f_50_);
return v___x_57_;
}
}
}
LEAN_EXPORT void l_Std_Http_instTransportClient___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_47_ = stack[0].m_obj;
uint64_t v_expect_48_ = stack[1].m_num;
lean_object* v_res_75_;
v_res_75_ = l_Std_Http_instTransportClient___lam__2(v_client_47_, v_expect_48_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__2___boxed(lean_object* v_client_76_, lean_object* v_expect_77_, lean_object* v___y_78_){
_start:
{
uint64_t v_expect_boxed_79_; lean_object* v_res_80_; 
v_expect_boxed_79_ = lean_unbox_uint64(v_expect_77_);
lean_dec_ref(v_expect_77_);
v_res_80_ = l_Std_Http_instTransportClient___lam__2(v_client_76_, v_expect_boxed_79_);
lean_dec(v_client_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3(lean_object* v___x_81_, lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_mk_io_user_error(v___x_81_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
else
{
lean_object* v_val_85_; 
lean_dec_ref(v___x_81_);
v_val_85_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_val_85_);
return v_val_85_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__3___boxed(lean_object* v___x_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_Http_instTransportClient___lam__3(v___x_86_, v_x_87_);
lean_dec(v_x_87_);
return v_res_88_;
}
}
lean_object* l_Std_Http_instTransportClient___lam__4(lean_object* v___f_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
lean_dec_ref(v___f_89_);
v_a_92_ = lean_ctor_get(v_x_90_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v_x_90_);
if (v_isSharedCheck_100_ == 0)
{
v___x_94_ = v_x_90_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v_x_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_99_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
else
{
lean_object* v_a_101_; 
v_a_101_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_a_101_);
lean_dec_ref_known(v_x_90_, 1);
if (lean_obj_tag(v_a_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_110_; 
lean_dec_ref(v___f_89_);
v_a_102_ = lean_ctor_get(v_a_101_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v_a_101_);
if (v_isSharedCheck_110_ == 0)
{
v___x_104_ = v_a_101_;
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v_a_101_);
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
lean_object* v_a_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_a_111_ = lean_ctor_get(v_a_101_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v_a_101_, 1);
v___x_112_ = lean_io_promise_result_opt(v_a_111_);
lean_dec(v_a_111_);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = 0;
v___x_115_ = lean_task_map(v___f_89_, v___x_112_, v___x_113_, v___x_114_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_instTransportClient___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_89_ = stack[0].m_obj;
lean_object* v_x_90_ = stack[1].m_obj;
lean_object* v_res_117_;
v_res_117_ = l_Std_Http_instTransportClient___lam__4(v___f_89_, v_x_90_);
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__4___boxed(lean_object* v___f_118_, lean_object* v_x_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_Http_instTransportClient___lam__4(v___f_118_, v_x_119_);
return v_res_121_;
}
}
lean_object* l_Std_Http_instTransportClient___lam__5(lean_object* v_client_126_, lean_object* v_data_127_){
_start:
{
lean_object* v___f_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v_val_133_; lean_object* v___x_137_; 
v___f_129_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__5___closed__1));
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = 0;
v___x_137_ = lean_uv_tcp_send(v_client_126_, v_data_127_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 1);
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
v_val_133_ = v___x_143_;
goto v___jp_132_;
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_a_146_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_137_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_137_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set_tag(v___x_148_, 0);
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
v_val_133_ = v___x_151_;
goto v___jp_132_;
}
}
}
v___jp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v_val_133_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
v___x_136_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_130_, v___x_131_, v___x_135_, v___f_129_);
return v___x_136_;
}
}
}
LEAN_EXPORT void l_Std_Http_instTransportClient___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_126_ = stack[0].m_obj;
lean_object* v_data_127_ = stack[1].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Std_Http_instTransportClient___lam__5(v_client_126_, v_data_127_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__5___boxed(lean_object* v_client_155_, lean_object* v_data_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Std_Http_instTransportClient___lam__5(v_client_155_, v_data_156_);
lean_dec(v_client_155_);
return v_res_158_;
}
}
lean_object* l_Std_Http_instTransportClient___lam__6(lean_object* v_x_159_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(0);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT void l_Std_Http_instTransportClient___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_159_ = stack[0].m_obj;
lean_object* v_res_163_;
v_res_163_ = l_Std_Http_instTransportClient___lam__6(v_x_159_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_Std_Http_instTransportClient___lam__6___boxed(lean_object* v_x_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Http_instTransportClient___lam__6(v_x_164_);
lean_dec(v_x_164_);
return v_res_166_;
}
}
lean_object* l_Std_Http_Internal_Mock_new(){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_178_ = lean_box(0);
v___x_179_ = l_Std_CloseableChannel_new___redArg(v___x_178_);
v___x_180_ = l_Std_CloseableChannel_new___redArg(v___x_178_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
lean_inc_ref(v___x_181_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_183_;
v_res_183_ = l_Std_Http_Internal_Mock_new();
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_new___boxed(lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_Http_Internal_Mock_new();
return v_res_185_;
}
}
lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__0(lean_object* v_x_186_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_196_; 
v_a_188_ = lean_ctor_get(v_x_186_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_186_);
if (v_isSharedCheck_196_ == 0)
{
v___x_190_ = v_x_186_;
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v_x_186_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_195_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; 
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_206_; 
v_a_197_ = lean_ctor_get(v_x_186_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_x_186_);
if (v_isSharedCheck_206_ == 0)
{
v___x_199_ = v_x_186_;
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v_x_186_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v_a_197_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_201_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_205_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_recvJoined___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_186_ = stack[0].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Std_Http_Internal_Mock_recvJoined___lam__0(v_x_186_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__0___boxed(lean_object* v_x_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Http_Internal_Mock_recvJoined___lam__0(v_x_208_);
return v_res_210_;
}
}
lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__1(lean_object* v_a_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_222_; 
v_a_214_ = lean_ctor_get(v_x_212_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_x_212_);
if (v_isSharedCheck_222_ == 0)
{
v___x_216_ = v_x_212_;
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v_x_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_221_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec_ref_known(v_x_212_, 1);
v___x_223_ = l_IO_Promise_result_x21___redArg(v_a_211_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_recvJoined___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_211_ = stack[0].m_obj;
lean_object* v_x_212_ = stack[1].m_obj;
lean_object* v_res_225_;
v_res_225_ = l_Std_Http_Internal_Mock_recvJoined___lam__1(v_a_211_, v_x_212_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed(lean_object* v_a_226_, lean_object* v_x_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_Http_Internal_Mock_recvJoined___lam__1(v_a_226_, v_x_227_);
lean_dec(v_a_226_);
return v_res_229_;
}
}
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(lean_object* v_b_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_b_230_);
v_a_233_ = lean_ctor_get(v_x_231_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v_x_231_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v_x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_240_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_268_; 
v_a_242_ = lean_ctor_get(v_x_231_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_268_ == 0)
{
v___x_244_ = v_x_231_;
v_isShared_245_ = v_isSharedCheck_268_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v_x_231_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_268_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
if (lean_obj_tag(v_a_242_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_b_230_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_246_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_250_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
else
{
lean_object* v_val_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_267_; 
v_val_251_ = lean_ctor_get(v_a_242_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v_a_242_);
if (v_isSharedCheck_267_ == 0)
{
v___x_253_ = v_a_242_;
v_isShared_254_ = v_isSharedCheck_267_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_val_251_);
lean_dec(v_a_242_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_267_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_byte_array_size(v_b_230_);
v___x_257_ = lean_byte_array_size(v_val_251_);
v___x_258_ = 0;
v___x_259_ = lean_byte_array_copy_slice(v_val_251_, v___x_255_, v_b_230_, v___x_256_, v___x_257_, v___x_258_);
lean_dec(v_val_251_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_259_);
v___x_261_ = v___x_253_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_266_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_261_);
v___x_263_ = v___x_244_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_230_ = stack[0].m_obj;
lean_object* v_x_231_ = stack[1].m_obj;
lean_object* v_res_269_;
v_res_269_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(v_b_230_, v_x_231_);
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1___boxed(lean_object* v_b_270_, lean_object* v_x_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(v_b_270_, v_x_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0___boxed(lean_object* v_promise_274_, lean_object* v_recvChan_275_, lean_object* v_expect_276_, lean_object* v_prio_277_, lean_object* v_x_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(v_promise_274_, v_recvChan_275_, v_expect_276_, v_prio_277_, v_x_278_);
return v_res_280_;
}
}
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(lean_object* v_recvChan_281_, lean_object* v_expect_282_, lean_object* v_prio_283_, lean_object* v_promise_284_, lean_object* v_b_285_){
_start:
{
lean_object* v_a_288_; lean_object* v___f_291_; lean_object* v___f_292_; 
lean_inc(v_prio_283_);
lean_inc(v_expect_282_);
lean_inc_ref(v_recvChan_281_);
lean_inc(v_promise_284_);
v___f_291_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_291_, 0, v_promise_284_);
lean_closure_set(v___f_291_, 1, v_recvChan_281_);
lean_closure_set(v___f_291_, 2, v_expect_282_);
lean_closure_set(v___f_291_, 3, v_prio_283_);
lean_inc_ref(v_b_285_);
v___f_292_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_292_, 0, v_b_285_);
if (lean_obj_tag(v_expect_282_) == 1)
{
lean_object* v_val_316_; lean_object* v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint8_t v___x_320_; 
v_val_316_ = lean_ctor_get(v_expect_282_, 0);
v___x_317_ = lean_byte_array_size(v_b_285_);
v___x_318_ = lean_uint64_of_nat(v___x_317_);
v___x_319_ = lean_unbox_uint64(v_val_316_);
v___x_320_ = lean_uint64_dec_le(v___x_319_, v___x_318_);
if (v___x_320_ == 0)
{
lean_dec_ref(v_b_285_);
goto v___jp_293_;
}
else
{
lean_dec_ref_known(v_expect_282_, 1);
lean_dec_ref(v___f_292_);
lean_dec_ref(v___f_291_);
lean_dec(v_prio_283_);
lean_dec_ref(v_recvChan_281_);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
}
else
{
lean_dec_ref(v_b_285_);
goto v___jp_293_;
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_a_288_);
v___x_290_ = lean_io_promise_resolve(v___x_289_, v_promise_284_);
lean_dec(v_promise_284_);
return v___x_290_;
}
v___jp_293_:
{
lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = 0;
lean_inc_ref(v_recvChan_281_);
v___x_296_ = l_Std_CloseableChannel_tryRecv___redArg(v_recvChan_281_);
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
v___x_299_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_294_, v___x_295_, v___x_298_, v___f_292_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; 
lean_dec_ref(v___f_291_);
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_299_, 1);
if (lean_obj_tag(v_a_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_prio_283_);
lean_dec(v_expect_282_);
lean_dec_ref(v_recvChan_281_);
v_a_301_ = lean_ctor_get(v_a_300_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_a_300_);
if (v_isSharedCheck_309_ == 0)
{
v___x_303_ = v_a_300_;
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v_a_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_308_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
v___x_307_ = lean_io_promise_resolve(v___x_306_, v_promise_284_);
lean_dec(v_promise_284_);
return v___x_307_;
}
}
}
else
{
lean_object* v_a_310_; 
v_a_310_ = lean_ctor_get(v_a_300_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v_a_300_, 1);
if (lean_obj_tag(v_a_310_) == 0)
{
lean_object* v_a_311_; 
lean_dec(v_prio_283_);
lean_dec(v_expect_282_);
lean_dec_ref(v_recvChan_281_);
v_a_311_ = lean_ctor_get(v_a_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v_a_310_, 1);
v_a_288_ = v_a_311_;
goto v___jp_287_;
}
else
{
lean_object* v_a_312_; 
v_a_312_ = lean_ctor_get(v_a_310_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v_a_310_, 1);
v_b_285_ = v_a_312_;
goto _start;
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_315_; 
lean_dec(v_promise_284_);
lean_dec(v_expect_282_);
lean_dec_ref(v_recvChan_281_);
v_a_314_ = lean_ctor_get(v___x_299_, 0);
lean_inc_ref(v_a_314_);
lean_dec_ref_known(v___x_299_, 1);
v___x_315_ = l_BaseIO_chainTask___redArg(v_a_314_, v___f_291_, v_prio_283_, v___x_295_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_recvChan_281_ = stack[0].m_obj;
lean_object* v_expect_282_ = stack[1].m_obj;
lean_object* v_prio_283_ = stack[2].m_obj;
lean_object* v_promise_284_ = stack[3].m_obj;
lean_object* v_b_285_ = stack[4].m_obj;
lean_object* v_res_321_;
v_res_321_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_281_, v_expect_282_, v_prio_283_, v_promise_284_, v_b_285_);
stack->m_obj
 = v_res_321_;
}
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(lean_object* v_promise_322_, lean_object* v_recvChan_323_, lean_object* v_expect_324_, lean_object* v_prio_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
lean_dec(v_prio_325_);
lean_dec(v_expect_324_);
lean_dec_ref(v_recvChan_323_);
v_a_328_ = lean_ctor_get(v_x_326_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v_x_326_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v_x_326_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_io_promise_resolve(v___x_333_, v_promise_322_);
lean_dec(v_promise_322_);
return v___x_334_;
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_348_; 
v_a_337_ = lean_ctor_get(v_x_326_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_348_ == 0)
{
v___x_339_ = v_x_326_;
v_isShared_340_ = v_isSharedCheck_348_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v_x_326_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_348_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
if (lean_obj_tag(v_a_337_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; 
lean_dec(v_prio_325_);
lean_dec(v_expect_324_);
lean_dec_ref(v_recvChan_323_);
v_a_341_ = lean_ctor_get(v_a_337_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v_a_337_, 1);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v_a_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_341_);
v___x_343_ = v_reuseFailAlloc_345_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; 
v___x_344_ = lean_io_promise_resolve(v___x_343_, v_promise_322_);
lean_dec(v_promise_322_);
return v___x_344_;
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_347_; 
lean_del_object(v___x_339_);
v_a_346_ = lean_ctor_get(v_a_337_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v_a_337_, 1);
v___x_347_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_323_, v_expect_324_, v_prio_325_, v_promise_322_, v_a_346_);
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_322_ = stack[0].m_obj;
lean_object* v_recvChan_323_ = stack[1].m_obj;
lean_object* v_expect_324_ = stack[2].m_obj;
lean_object* v_prio_325_ = stack[3].m_obj;
lean_object* v_x_326_ = stack[4].m_obj;
lean_object* v_res_349_;
v_res_349_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(v_promise_322_, v_recvChan_323_, v_expect_324_, v_prio_325_, v_x_326_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___boxed(lean_object* v_recvChan_350_, lean_object* v_expect_351_, lean_object* v_prio_352_, lean_object* v_promise_353_, lean_object* v_b_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_350_, v_expect_351_, v_prio_352_, v_promise_353_, v_b_354_);
return v_res_356_;
}
}
lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2(lean_object* v_recvChan_357_, lean_object* v_expect_358_, lean_object* v___x_359_, lean_object* v_val_360_, uint8_t v___x_361_, lean_object* v_x_362_){
_start:
{
if (lean_obj_tag(v_x_362_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref(v_val_360_);
lean_dec(v___x_359_);
lean_dec(v_expect_358_);
lean_dec_ref(v_recvChan_357_);
v_a_364_ = lean_ctor_get(v_x_362_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_372_ == 0)
{
v___x_366_ = v_x_362_;
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v_x_362_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_371_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_384_; 
v_a_373_ = lean_ctor_get(v_x_362_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_384_ == 0)
{
v___x_375_ = v_x_362_;
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v_x_362_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
lean_inc(v_a_373_);
v___f_377_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed), 3, 1);
lean_closure_set(v___f_377_, 0, v_a_373_);
lean_inc(v___x_359_);
v___x_378_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_357_, v_expect_358_, v___x_359_, v_a_373_, v_val_360_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_378_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_383_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_359_, v___x_361_, v___x_381_, v___f_377_);
return v___x_382_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_recvJoined___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_recvChan_357_ = stack[0].m_obj;
lean_object* v_expect_358_ = stack[1].m_obj;
lean_object* v___x_359_ = stack[2].m_obj;
lean_object* v_val_360_ = stack[3].m_obj;
uint8_t v___x_361_ = stack[4].m_num;
lean_object* v_x_362_ = stack[5].m_obj;
lean_object* v_res_385_;
v_res_385_ = l_Std_Http_Internal_Mock_recvJoined___lam__2(v_recvChan_357_, v_expect_358_, v___x_359_, v_val_360_, v___x_361_, v_x_362_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed(lean_object* v_recvChan_386_, lean_object* v_expect_387_, lean_object* v___x_388_, lean_object* v_val_389_, lean_object* v___x_390_, lean_object* v_x_391_, lean_object* v___y_392_){
_start:
{
uint8_t v___x_2390__boxed_393_; lean_object* v_res_394_; 
v___x_2390__boxed_393_ = lean_unbox(v___x_390_);
v_res_394_ = l_Std_Http_Internal_Mock_recvJoined___lam__2(v_recvChan_386_, v_expect_387_, v___x_388_, v_val_389_, v___x_2390__boxed_393_, v_x_391_);
return v_res_394_;
}
}
lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3(lean_object* v_recvChan_395_, lean_object* v_expect_396_, lean_object* v___f_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v___x_400_; 
lean_dec_ref(v___f_397_);
lean_dec(v_expect_396_);
lean_dec_ref(v_recvChan_395_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_x_398_);
return v___x_400_;
}
else
{
lean_object* v_a_401_; 
v_a_401_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_a_401_);
if (lean_obj_tag(v_a_401_) == 0)
{
lean_object* v___x_402_; 
lean_dec_ref(v___f_397_);
lean_dec(v_expect_396_);
lean_dec_ref(v_recvChan_395_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v_x_398_);
return v___x_402_;
}
else
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_424_; 
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_x_398_, 0);
lean_dec(v_unused_425_);
v___x_404_ = v_x_398_;
v_isShared_405_ = v_isSharedCheck_424_;
goto v_resetjp_403_;
}
else
{
lean_dec(v_x_398_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_424_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_val_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_423_; 
v_val_406_ = lean_ctor_get(v_a_401_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_401_);
if (v_isSharedCheck_423_ == 0)
{
v___x_408_ = v_a_401_;
v_isShared_409_ = v_isSharedCheck_423_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_val_406_);
lean_dec(v_a_401_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_423_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = 0;
v___x_412_ = lean_box(v___x_411_);
v___f_413_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed), 7, 5);
lean_closure_set(v___f_413_, 0, v_recvChan_395_);
lean_closure_set(v___f_413_, 1, v_expect_396_);
lean_closure_set(v___f_413_, 2, v___x_410_);
lean_closure_set(v___f_413_, 3, v_val_406_);
lean_closure_set(v___f_413_, 4, v___x_412_);
v___x_414_ = lean_io_promise_new();
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_414_);
v___x_416_ = v___x_404_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_422_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 0);
lean_ctor_set(v___x_408_, 0, v___x_416_);
v___x_418_ = v___x_408_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_421_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_410_, v___x_411_, v___x_418_, v___f_413_);
v___x_420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_410_, v___x_411_, v___x_419_, v___f_397_);
return v___x_420_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_recvJoined___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_recvChan_395_ = stack[0].m_obj;
lean_object* v_expect_396_ = stack[1].m_obj;
lean_object* v___f_397_ = stack[2].m_obj;
lean_object* v_x_398_ = stack[3].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Std_Http_Internal_Mock_recvJoined___lam__3(v_recvChan_395_, v_expect_396_, v___f_397_, v_x_398_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed(lean_object* v_recvChan_427_, lean_object* v_expect_428_, lean_object* v___f_429_, lean_object* v_x_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_Http_Internal_Mock_recvJoined___lam__3(v_recvChan_427_, v_expect_428_, v___f_429_, v_x_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__4(lean_object* v_a_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_a_433_);
return v___x_434_;
}
}
lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5(lean_object* v___f_435_, lean_object* v___f_436_, lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v___f_436_);
lean_dec_ref(v___f_435_);
v_a_439_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_441_ = v_x_437_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v_x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_446_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_a_448_ = lean_ctor_get(v_x_437_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v_x_437_, 1);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = 0;
v___x_451_ = lean_task_map(v___f_435_, v_a_448_, v___x_449_, v___x_450_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_449_, v___x_450_, v___x_452_, v___f_436_);
return v___x_453_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_recvJoined___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_435_ = stack[0].m_obj;
lean_object* v___f_436_ = stack[1].m_obj;
lean_object* v_x_437_ = stack[2].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_Std_Http_Internal_Mock_recvJoined___lam__5(v___f_435_, v___f_436_, v_x_437_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed(lean_object* v___f_455_, lean_object* v___f_456_, lean_object* v_x_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_Http_Internal_Mock_recvJoined___lam__5(v___f_455_, v___f_456_, v_x_457_);
return v_res_459_;
}
}
lean_object* l_Std_Http_Internal_Mock_recvJoined(lean_object* v_recvChan_462_, lean_object* v_expect_463_){
_start:
{
lean_object* v___f_465_; lean_object* v___f_466_; lean_object* v___f_467_; lean_object* v___f_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___f_465_ = ((lean_object*)(l_Std_Http_Internal_Mock_recvJoined___closed__0));
lean_inc_ref(v_recvChan_462_);
v___f_466_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed), 5, 3);
lean_closure_set(v___f_466_, 0, v_recvChan_462_);
lean_closure_set(v___f_466_, 1, v_expect_463_);
lean_closure_set(v___f_466_, 2, v___f_465_);
v___f_467_ = ((lean_object*)(l_Std_Http_Internal_Mock_recvJoined___closed__1));
v___f_468_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed), 4, 2);
lean_closure_set(v___f_468_, 0, v___f_467_);
lean_closure_set(v___f_468_, 1, v___f_466_);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = 0;
v___x_471_ = l_Std_CloseableChannel_recv___redArg(v_recvChan_462_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
v___x_474_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_469_, v___x_470_, v___x_473_, v___f_468_);
return v___x_474_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_recvJoined_0interp(lean_interpreter_value* stack)
{
lean_object* v_recvChan_462_ = stack[0].m_obj;
lean_object* v_expect_463_ = stack[1].m_obj;
lean_object* v_res_475_;
v_res_475_ = l_Std_Http_Internal_Mock_recvJoined(v_recvChan_462_, v_expect_463_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___boxed(lean_object* v_recvChan_476_, lean_object* v_expect_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_Http_Internal_Mock_recvJoined(v_recvChan_476_, v_expect_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__0(lean_object* v___y_482_){
_start:
{
lean_object* v___y_484_; 
if (lean_obj_tag(v___y_482_) == 0)
{
lean_object* v_a_487_; uint8_t v___x_488_; 
v_a_487_ = lean_ctor_get(v___y_482_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___y_482_, 1);
v___x_488_ = lean_unbox(v_a_487_);
lean_dec(v_a_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___lam__0___closed__0));
v___y_484_ = v___x_489_;
goto v___jp_483_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___lam__0___closed__1));
v___y_484_ = v___x_490_;
goto v___jp_483_;
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_a_491_ = lean_ctor_get(v___y_482_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___y_482_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___y_482_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___y_482_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_inc_ref(v___y_484_);
v___x_485_ = lean_mk_io_user_error(v___y_484_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
}
lean_object* l_Std_Http_Internal_Mock_send___lam__1(lean_object* v___f_499_, lean_object* v_x_500_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
lean_dec_ref(v___f_499_);
v_a_502_ = lean_ctor_get(v_x_500_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v_x_500_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v_x_500_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_a_511_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v_x_500_, 1);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = 0;
v___x_514_ = lean_task_map(v___f_499_, v_a_511_, v___x_512_, v___x_513_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_send___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_499_ = stack[0].m_obj;
lean_object* v_x_500_ = stack[1].m_obj;
lean_object* v_res_516_;
v_res_516_ = l_Std_Http_Internal_Mock_send___lam__1(v___f_499_, v_x_500_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__1___boxed(lean_object* v___f_517_, lean_object* v_x_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_Http_Internal_Mock_send___lam__1(v___f_517_, v_x_518_);
return v_res_520_;
}
}
lean_object* l_Std_Http_Internal_Mock_send(lean_object* v_sendChan_524_, lean_object* v_data_525_){
_start:
{
lean_object* v___f_527_; lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___f_527_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___closed__1));
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = 0;
v___x_530_ = l_Std_CloseableChannel_send___redArg(v_sendChan_524_, v_data_525_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
v___x_533_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_528_, v___x_529_, v___x_532_, v___f_527_);
return v___x_533_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_sendChan_524_ = stack[0].m_obj;
lean_object* v_data_525_ = stack[1].m_obj;
lean_object* v_res_534_;
v_res_534_ = l_Std_Http_Internal_Mock_send(v_sendChan_524_, v_data_525_);
stack->m_obj
 = v_res_534_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___boxed(lean_object* v_sendChan_535_, lean_object* v_data_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Http_Internal_Mock_send(v_sendChan_535_, v_data_536_);
return v_res_538_;
}
}
lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0(lean_object* v_x_543_){
_start:
{
if (lean_obj_tag(v_x_543_) == 0)
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v_x_543_);
return v___x_545_;
}
else
{
lean_object* v___x_546_; 
lean_dec_ref_known(v_x_543_, 1);
v___x_546_ = ((lean_object*)(l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1));
return v___x_546_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_sendAll___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_543_ = stack[0].m_obj;
lean_object* v_res_547_;
v_res_547_ = l_Std_Http_Internal_Mock_sendAll___lam__0(v_x_543_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___boxed(lean_object* v_x_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Http_Internal_Mock_sendAll___lam__0(v_x_548_);
return v_res_550_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(lean_object* v___x_551_, lean_object* v_x_552_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_a_554_ = lean_ctor_get(v_x_552_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_562_ == 0)
{
v___x_556_ = v_x_552_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v_x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
else
{
lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_571_; 
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v_x_552_, 0);
lean_dec(v_unused_572_);
v___x_564_ = v_x_552_;
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
else
{
lean_dec(v_x_552_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_551_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; 
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_551_ = stack[0].m_obj;
lean_object* v_x_552_ = stack[1].m_obj;
lean_object* v_res_573_;
v_res_573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(v___x_551_, v_x_552_);
stack->m_obj
 = v_res_573_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed(lean_object* v___x_574_, lean_object* v_x_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(v___x_574_, v_x_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed(lean_object* v_i_578_, lean_object* v_sendChan_579_, lean_object* v_as_580_, lean_object* v_sz_581_, lean_object* v_x_582_, lean_object* v___y_583_){
_start:
{
size_t v_i_boxed_584_; size_t v_sz_boxed_585_; lean_object* v_res_586_; 
v_i_boxed_584_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_sz_boxed_585_ = lean_unbox_usize(v_sz_581_);
lean_dec(v_sz_581_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(v_i_boxed_584_, v_sendChan_579_, v_as_580_, v_sz_boxed_585_, v_x_582_);
return v_res_586_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(lean_object* v_sendChan_589_, lean_object* v_as_590_, size_t v_sz_591_, size_t v_i_592_, lean_object* v_b_593_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_lt(v_i_592_, v_sz_591_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec_ref(v_as_590_);
lean_dec_ref(v_sendChan_589_);
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v_b_593_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v_a_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_598_ = lean_box_usize(v_i_592_);
v___x_599_ = lean_box_usize(v_sz_591_);
lean_inc_ref(v_as_590_);
lean_inc_ref(v_sendChan_589_);
v___f_600_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_600_, 0, v___x_598_);
lean_closure_set(v___f_600_, 1, v_sendChan_589_);
lean_closure_set(v___f_600_, 2, v_as_590_);
lean_closure_set(v___f_600_, 3, v___x_599_);
v___f_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0));
v_a_602_ = lean_array_uget(v_as_590_, v_i_592_);
lean_dec_ref(v_as_590_);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = 0;
v___x_605_ = l_Std_Http_Internal_Mock_send(v_sendChan_589_, v_a_602_);
v___x_606_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_603_, v___x_604_, v___x_605_, v___f_601_);
v___x_607_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_603_, v___x_604_, v___x_606_, v___f_600_);
return v___x_607_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sendChan_589_ = stack[0].m_obj;
lean_object* v_as_590_ = stack[1].m_obj;
size_t v_sz_591_ = stack[2].m_num;
size_t v_i_592_ = stack[3].m_num;
lean_object* v_b_593_ = stack[4].m_obj;
lean_object* v_res_608_;
v_res_608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_589_, v_as_590_, v_sz_591_, v_i_592_, v_b_593_);
stack->m_obj
 = v_res_608_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(size_t v_i_609_, lean_object* v_sendChan_610_, lean_object* v_as_611_, size_t v_sz_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_as_611_);
lean_dec_ref(v_sendChan_610_);
v_a_615_ = lean_ctor_get(v_x_613_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_623_ == 0)
{
v___x_617_ = v_x_613_;
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v_x_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_643_; 
v_a_624_ = lean_ctor_get(v_x_613_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_643_ == 0)
{
v___x_626_ = v_x_613_;
v_isShared_627_ = v_isSharedCheck_643_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v_x_613_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_643_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
if (lean_obj_tag(v_a_624_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_638_; 
lean_dec_ref(v_as_611_);
lean_dec_ref(v_sendChan_610_);
v_a_628_ = lean_ctor_get(v_a_624_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v_a_624_);
if (v_isSharedCheck_638_ == 0)
{
v___x_630_ = v_a_624_;
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v_a_624_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v_a_628_);
v___x_633_ = v___x_626_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_633_);
v___x_635_ = v___x_630_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_639_; size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
lean_del_object(v___x_626_);
v_a_639_ = lean_ctor_get(v_a_624_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v_a_624_, 1);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_add(v_i_609_, v___x_640_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_610_, v_as_611_, v_sz_612_, v___x_641_, v_a_639_);
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_609_ = stack[0].m_num;
lean_object* v_sendChan_610_ = stack[1].m_obj;
lean_object* v_as_611_ = stack[2].m_obj;
size_t v_sz_612_ = stack[3].m_num;
lean_object* v_x_613_ = stack[4].m_obj;
lean_object* v_res_644_;
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(v_i_609_, v_sendChan_610_, v_as_611_, v_sz_612_, v_x_613_);
stack->m_obj
 = v_res_644_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___boxed(lean_object* v_sendChan_645_, lean_object* v_as_646_, lean_object* v_sz_647_, lean_object* v_i_648_, lean_object* v_b_649_, lean_object* v___y_650_){
_start:
{
size_t v_sz_boxed_651_; size_t v_i_boxed_652_; lean_object* v_res_653_; 
v_sz_boxed_651_ = lean_unbox_usize(v_sz_647_);
lean_dec(v_sz_647_);
v_i_boxed_652_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_645_, v_as_646_, v_sz_boxed_651_, v_i_boxed_652_, v_b_649_);
return v_res_653_;
}
}
lean_object* l_Std_Http_Internal_Mock_sendAll(lean_object* v_sendChan_655_, lean_object* v_data_656_){
_start:
{
lean_object* v___f_658_; lean_object* v___x_659_; size_t v_sz_660_; size_t v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___f_658_ = ((lean_object*)(l_Std_Http_Internal_Mock_sendAll___closed__0));
v___x_659_ = lean_box(0);
v_sz_660_ = lean_array_size(v_data_656_);
v___x_661_ = ((size_t)0ULL);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = 0;
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_655_, v_data_656_, v_sz_660_, v___x_661_, v___x_659_);
v___x_665_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_662_, v___x_663_, v___x_664_, v___f_658_);
return v___x_665_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_sendAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_sendChan_655_ = stack[0].m_obj;
lean_object* v_data_656_ = stack[1].m_obj;
lean_object* v_res_666_;
v_res_666_ = l_Std_Http_Internal_Mock_sendAll(v_sendChan_655_, v_data_656_);
stack->m_obj
 = v_res_666_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___boxed(lean_object* v_sendChan_667_, lean_object* v_data_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_Http_Internal_Mock_sendAll(v_sendChan_667_, v_data_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvSelector(lean_object* v_recvChan_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_CloseableChannel_recvSelector___redArg(v_recvChan_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan(lean_object* v_client_673_){
_start:
{
lean_object* v_serverToClient_674_; 
v_serverToClient_674_ = lean_ctor_get(v_client_673_, 1);
lean_inc_ref(v_serverToClient_674_);
return v_serverToClient_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan___boxed(lean_object* v_client_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_Http_Internal_Mock_Client_getRecvChan(v_client_675_);
lean_dec_ref(v_client_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan(lean_object* v_client_677_){
_start:
{
lean_object* v_clientToServer_678_; 
v_clientToServer_678_ = lean_ctor_get(v_client_677_, 0);
lean_inc_ref(v_clientToServer_678_);
return v_clientToServer_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan___boxed(lean_object* v_client_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_Http_Internal_Mock_Client_getSendChan(v_client_679_);
lean_dec_ref(v_client_679_);
return v_res_680_;
}
}
lean_object* l_Std_Http_Internal_Mock_Client_send(lean_object* v_client_681_, lean_object* v_data_682_){
_start:
{
lean_object* v_clientToServer_684_; lean_object* v___x_685_; 
v_clientToServer_684_ = lean_ctor_get(v_client_681_, 0);
lean_inc_ref(v_clientToServer_684_);
lean_dec_ref(v_client_681_);
v___x_685_ = l_Std_Http_Internal_Mock_send(v_clientToServer_684_, v_data_682_);
return v___x_685_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Client_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_681_ = stack[0].m_obj;
lean_object* v_data_682_ = stack[1].m_obj;
lean_object* v_res_686_;
v_res_686_ = l_Std_Http_Internal_Mock_Client_send(v_client_681_, v_data_682_);
stack->m_obj
 = v_res_686_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_send___boxed(lean_object* v_client_687_, lean_object* v_data_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_Http_Internal_Mock_Client_send(v_client_687_, v_data_688_);
return v_res_690_;
}
}
lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f(lean_object* v_client_691_, lean_object* v_expect_692_){
_start:
{
lean_object* v_serverToClient_694_; lean_object* v___x_695_; 
v_serverToClient_694_ = lean_ctor_get(v_client_691_, 1);
lean_inc_ref(v_serverToClient_694_);
lean_dec_ref(v_client_691_);
v___x_695_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_694_, v_expect_692_);
return v___x_695_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Client_recv_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_691_ = stack[0].m_obj;
lean_object* v_expect_692_ = stack[1].m_obj;
lean_object* v_res_696_;
v_res_696_ = l_Std_Http_Internal_Mock_Client_recv_x3f(v_client_691_, v_expect_692_);
stack->m_obj
 = v_res_696_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f___boxed(lean_object* v_client_697_, lean_object* v_expect_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_Http_Internal_Mock_Client_recv_x3f(v_client_697_, v_expect_698_);
return v_res_700_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(lean_object* v___x_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; 
lean_inc_ref(v___x_701_);
v___x_704_ = l_Std_CloseableChannel_tryRecv___redArg(v___x_701_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_dec_ref(v___x_701_);
return v_a_702_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; 
v_val_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_byte_array_size(v_a_702_);
v___x_708_ = lean_byte_array_size(v_val_705_);
v___x_709_ = 0;
v___x_710_ = lean_byte_array_copy_slice(v_val_705_, v___x_706_, v_a_702_, v___x_707_, v___x_708_, v___x_709_);
lean_dec(v_val_705_);
v_a_702_ = v___x_710_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_701_ = stack[0].m_obj;
lean_object* v_a_702_ = stack[1].m_obj;
lean_object* v_res_712_;
v_res_712_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v___x_701_, v_a_702_);
stack->m_obj
 = v_res_712_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg___boxed(lean_object* v___x_713_, lean_object* v_a_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v___x_713_, v_a_714_);
return v_res_716_;
}
}
lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(lean_object* v_client_717_){
_start:
{
lean_object* v_serverToClient_719_; lean_object* v___x_720_; 
v_serverToClient_719_ = lean_ctor_get(v_client_717_, 1);
lean_inc_ref_n(v_serverToClient_719_, 2);
lean_dec_ref(v_client_717_);
v___x_720_ = l_Std_CloseableChannel_tryRecv___redArg(v_serverToClient_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_dec_ref(v_serverToClient_719_);
return v___x_720_;
}
else
{
lean_object* v_val_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_729_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_729_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_val_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v_serverToClient_719_, v_val_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_717_ = stack[0].m_obj;
lean_object* v_res_730_;
v_res_730_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_717_);
stack->m_obj
 = v_res_730_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg___boxed(lean_object* v_client_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_731_);
return v_res_733_;
}
}
lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f(lean_object* v_client_734_, uint64_t v___expect_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_734_);
return v___x_737_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Client_tryRecv_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_734_ = stack[0].m_obj;
uint64_t v___expect_735_ = stack[1].m_num;
lean_object* v_res_738_;
v_res_738_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f(v_client_734_, v___expect_735_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___boxed(lean_object* v_client_739_, lean_object* v___expect_740_, lean_object* v_a_741_){
_start:
{
uint64_t v___expect_boxed_742_; lean_object* v_res_743_; 
v___expect_boxed_742_ = lean_unbox_uint64(v___expect_740_);
lean_dec_ref(v___expect_740_);
v_res_743_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f(v_client_739_, v___expect_boxed_742_);
return v_res_743_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(lean_object* v___x_744_, lean_object* v_inst_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v___x_744_, v_a_746_);
return v___x_748_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_744_ = stack[0].m_obj;
lean_object* v_a_746_ = stack[2].m_obj;
lean_object* v_res_749_;
v_res_749_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(v___x_744_, lean_box(0), v_a_746_);
stack->m_obj
 = v_res_749_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___boxed(lean_object* v___x_750_, lean_object* v_inst_751_, lean_object* v_a_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(v___x_750_, v_inst_751_, v_a_752_);
return v_res_754_;
}
}
lean_object* l_Std_Http_Internal_Mock_Client_close(lean_object* v_client_759_){
_start:
{
lean_object* v_clientToServer_761_; lean_object* v_serverToClient_762_; uint8_t v___x_790_; 
v_clientToServer_761_ = lean_ctor_get(v_client_759_, 0);
lean_inc_ref_n(v_clientToServer_761_, 2);
v_serverToClient_762_ = lean_ctor_get(v_client_759_, 1);
lean_inc_ref(v_serverToClient_762_);
lean_dec_ref(v_client_759_);
v___x_790_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_761_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_761_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_dec_ref_known(v___x_791_, 1);
goto v___jp_763_;
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v_serverToClient_762_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_805_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
uint8_t v___x_796_; 
v___x_796_ = lean_unbox(v_a_792_);
lean_dec(v_a_792_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_797_);
v___x_799_ = v___x_794_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_801_);
v___x_803_ = v___x_794_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
else
{
lean_dec_ref(v_clientToServer_761_);
goto v___jp_763_;
}
v___jp_763_:
{
uint8_t v___x_764_; 
lean_inc_ref(v_serverToClient_762_);
v___x_764_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_762_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_787_; 
v_a_774_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_787_ == 0)
{
v___x_776_ = v___x_765_;
v_isShared_777_ = v_isSharedCheck_787_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_765_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_787_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
uint8_t v___x_778_; 
v___x_778_ = lean_unbox(v_a_774_);
lean_dec(v_a_774_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_779_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_783_);
v___x_785_ = v___x_776_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref(v_serverToClient_762_);
v___x_788_ = lean_box(0);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Client_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_759_ = stack[0].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_Std_Http_Internal_Mock_Client_close(v_client_759_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_close___boxed(lean_object* v_client_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_Http_Internal_Mock_Client_close(v_client_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan(lean_object* v_server_810_){
_start:
{
lean_object* v_clientToServer_811_; 
v_clientToServer_811_ = lean_ctor_get(v_server_810_, 0);
lean_inc_ref(v_clientToServer_811_);
return v_clientToServer_811_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan___boxed(lean_object* v_server_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_Http_Internal_Mock_Server_getRecvChan(v_server_812_);
lean_dec_ref(v_server_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan(lean_object* v_server_814_){
_start:
{
lean_object* v_serverToClient_815_; 
v_serverToClient_815_ = lean_ctor_get(v_server_814_, 1);
lean_inc_ref(v_serverToClient_815_);
return v_serverToClient_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan___boxed(lean_object* v_server_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_Http_Internal_Mock_Server_getSendChan(v_server_816_);
lean_dec_ref(v_server_816_);
return v_res_817_;
}
}
lean_object* l_Std_Http_Internal_Mock_Server_send(lean_object* v_server_818_, lean_object* v_data_819_){
_start:
{
lean_object* v_serverToClient_821_; lean_object* v___x_822_; 
v_serverToClient_821_ = lean_ctor_get(v_server_818_, 1);
lean_inc_ref(v_serverToClient_821_);
lean_dec_ref(v_server_818_);
v___x_822_ = l_Std_Http_Internal_Mock_send(v_serverToClient_821_, v_data_819_);
return v___x_822_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Server_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_server_818_ = stack[0].m_obj;
lean_object* v_data_819_ = stack[1].m_obj;
lean_object* v_res_823_;
v_res_823_ = l_Std_Http_Internal_Mock_Server_send(v_server_818_, v_data_819_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_send___boxed(lean_object* v_server_824_, lean_object* v_data_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_Http_Internal_Mock_Server_send(v_server_824_, v_data_825_);
return v_res_827_;
}
}
lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f(lean_object* v_server_828_, lean_object* v_expect_829_){
_start:
{
lean_object* v_clientToServer_831_; lean_object* v___x_832_; 
v_clientToServer_831_ = lean_ctor_get(v_server_828_, 0);
lean_inc_ref(v_clientToServer_831_);
lean_dec_ref(v_server_828_);
v___x_832_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_831_, v_expect_829_);
return v___x_832_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Server_recv_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_server_828_ = stack[0].m_obj;
lean_object* v_expect_829_ = stack[1].m_obj;
lean_object* v_res_833_;
v_res_833_ = l_Std_Http_Internal_Mock_Server_recv_x3f(v_server_828_, v_expect_829_);
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f___boxed(lean_object* v_server_834_, lean_object* v_expect_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_Http_Internal_Mock_Server_recv_x3f(v_server_834_, v_expect_835_);
return v_res_837_;
}
}
lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(lean_object* v_server_838_){
_start:
{
lean_object* v_clientToServer_840_; lean_object* v___x_841_; 
v_clientToServer_840_ = lean_ctor_get(v_server_838_, 0);
lean_inc_ref_n(v_clientToServer_840_, 2);
lean_dec_ref(v_server_838_);
v___x_841_ = l_Std_CloseableChannel_tryRecv___redArg(v_clientToServer_840_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_dec_ref(v_clientToServer_840_);
return v___x_841_;
}
else
{
lean_object* v_val_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_val_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_val_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v_clientToServer_840_, v_val_842_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_server_838_ = stack[0].m_obj;
lean_object* v_res_851_;
v_res_851_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_838_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg___boxed(lean_object* v_server_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_852_);
return v_res_854_;
}
}
lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f(lean_object* v_server_855_, uint64_t v___expect_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_855_);
return v___x_858_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Server_tryRecv_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_server_855_ = stack[0].m_obj;
uint64_t v___expect_856_ = stack[1].m_num;
lean_object* v_res_859_;
v_res_859_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f(v_server_855_, v___expect_856_);
stack->m_obj
 = v_res_859_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___boxed(lean_object* v_server_860_, lean_object* v___expect_861_, lean_object* v_a_862_){
_start:
{
uint64_t v___expect_boxed_863_; lean_object* v_res_864_; 
v___expect_boxed_863_ = lean_unbox_uint64(v___expect_861_);
lean_dec_ref(v___expect_861_);
v_res_864_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f(v_server_860_, v___expect_boxed_863_);
return v_res_864_;
}
}
lean_object* l_Std_Http_Internal_Mock_Server_close(lean_object* v_server_865_){
_start:
{
lean_object* v_clientToServer_867_; lean_object* v_serverToClient_868_; uint8_t v___x_896_; 
v_clientToServer_867_ = lean_ctor_get(v_server_865_, 0);
lean_inc_ref_n(v_clientToServer_867_, 2);
v_serverToClient_868_ = lean_ctor_get(v_server_865_, 1);
lean_inc_ref(v_serverToClient_868_);
lean_dec_ref(v_server_865_);
v___x_896_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_867_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_867_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_dec_ref_known(v___x_897_, 1);
goto v___jp_869_;
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v_serverToClient_868_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_911_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_911_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_911_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
uint8_t v___x_902_; 
v___x_902_ = lean_unbox(v_a_898_);
lean_dec(v_a_898_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_903_);
v___x_905_ = v___x_900_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_907_);
v___x_909_ = v___x_900_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
else
{
lean_dec_ref(v_clientToServer_867_);
goto v___jp_869_;
}
v___jp_869_:
{
uint8_t v___x_870_; 
lean_inc_ref(v_serverToClient_868_);
v___x_870_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_868_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_868_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_893_; 
v_a_880_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_893_ == 0)
{
v___x_882_ = v___x_871_;
v_isShared_883_ = v_isSharedCheck_893_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_871_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_893_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
uint8_t v___x_884_; 
v___x_884_ = lean_unbox(v_a_880_);
lean_dec(v_a_880_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_889_);
v___x_891_ = v___x_882_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref(v_serverToClient_868_);
v___x_894_ = lean_box(0);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_Mock_Server_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_server_865_ = stack[0].m_obj;
lean_object* v_res_912_;
v_res_912_ = l_Std_Http_Internal_Mock_Server_close(v_server_865_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_close___boxed(lean_object* v_server_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_Http_Internal_Mock_Server_close(v_server_913_);
return v_res_915_;
}
}
lean_object* l_Std_Http_Internal_instTransportClient___lam__0(lean_object* v_client_916_, uint64_t v_expect_917_){
_start:
{
lean_object* v_serverToClient_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_serverToClient_919_ = lean_ctor_get(v_client_916_, 1);
lean_inc_ref(v_serverToClient_919_);
lean_dec_ref(v_client_916_);
v___x_920_ = lean_box_uint64(v_expect_917_);
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
v___x_922_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_919_, v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_instTransportClient___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_916_ = stack[0].m_obj;
uint64_t v_expect_917_ = stack[1].m_num;
lean_object* v_res_923_;
v_res_923_ = l_Std_Http_Internal_instTransportClient___lam__0(v_client_916_, v_expect_917_);
stack->m_obj
 = v_res_923_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__0___boxed(lean_object* v_client_924_, lean_object* v_expect_925_, lean_object* v___y_926_){
_start:
{
uint64_t v_expect_boxed_927_; lean_object* v_res_928_; 
v_expect_boxed_927_ = lean_unbox_uint64(v_expect_925_);
lean_dec_ref(v_expect_925_);
v_res_928_ = l_Std_Http_Internal_instTransportClient___lam__0(v_client_924_, v_expect_boxed_927_);
return v_res_928_;
}
}
lean_object* l_Std_Http_Internal_instTransportClient___lam__1(lean_object* v_client_929_, lean_object* v_data_930_){
_start:
{
lean_object* v_clientToServer_932_; lean_object* v___x_933_; 
v_clientToServer_932_ = lean_ctor_get(v_client_929_, 0);
lean_inc_ref(v_clientToServer_932_);
lean_dec_ref(v_client_929_);
v___x_933_ = l_Std_Http_Internal_Mock_sendAll(v_clientToServer_932_, v_data_930_);
return v___x_933_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_instTransportClient___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_929_ = stack[0].m_obj;
lean_object* v_data_930_ = stack[1].m_obj;
lean_object* v_res_934_;
v_res_934_ = l_Std_Http_Internal_instTransportClient___lam__1(v_client_929_, v_data_930_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__1___boxed(lean_object* v_client_935_, lean_object* v_data_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_Http_Internal_instTransportClient___lam__1(v_client_935_, v_data_936_);
return v_res_938_;
}
}
lean_object* l_Std_Http_Internal_instTransportClient___lam__2(lean_object* v_client_939_, uint64_t v_x_940_){
_start:
{
lean_object* v_serverToClient_941_; lean_object* v___x_942_; 
v_serverToClient_941_ = lean_ctor_get(v_client_939_, 1);
lean_inc_ref(v_serverToClient_941_);
lean_dec_ref(v_client_939_);
v___x_942_ = l_Std_CloseableChannel_recvSelector___redArg(v_serverToClient_941_);
return v___x_942_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_instTransportClient___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_client_939_ = stack[0].m_obj;
uint64_t v_x_940_ = stack[1].m_num;
lean_object* v_res_943_;
v_res_943_ = l_Std_Http_Internal_instTransportClient___lam__2(v_client_939_, v_x_940_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__2___boxed(lean_object* v_client_944_, lean_object* v_x_945_){
_start:
{
uint64_t v_x_52__boxed_946_; lean_object* v_res_947_; 
v_x_52__boxed_946_ = lean_unbox_uint64(v_x_945_);
lean_dec_ref(v_x_945_);
v_res_947_ = l_Std_Http_Internal_instTransportClient___lam__2(v_client_944_, v_x_52__boxed_946_);
return v_res_947_;
}
}
lean_object* l_Std_Http_Internal_instTransportServer___lam__0(lean_object* v_server_958_, uint64_t v_expect_959_){
_start:
{
lean_object* v_clientToServer_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_clientToServer_961_ = lean_ctor_get(v_server_958_, 0);
lean_inc_ref(v_clientToServer_961_);
lean_dec_ref(v_server_958_);
v___x_962_ = lean_box_uint64(v_expect_959_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
v___x_964_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_961_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_instTransportServer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_server_958_ = stack[0].m_obj;
uint64_t v_expect_959_ = stack[1].m_num;
lean_object* v_res_965_;
v_res_965_ = l_Std_Http_Internal_instTransportServer___lam__0(v_server_958_, v_expect_959_);
stack->m_obj
 = v_res_965_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__0___boxed(lean_object* v_server_966_, lean_object* v_expect_967_, lean_object* v___y_968_){
_start:
{
uint64_t v_expect_boxed_969_; lean_object* v_res_970_; 
v_expect_boxed_969_ = lean_unbox_uint64(v_expect_967_);
lean_dec_ref(v_expect_967_);
v_res_970_ = l_Std_Http_Internal_instTransportServer___lam__0(v_server_966_, v_expect_boxed_969_);
return v_res_970_;
}
}
lean_object* l_Std_Http_Internal_instTransportServer___lam__1(lean_object* v_server_971_, lean_object* v_data_972_){
_start:
{
lean_object* v_serverToClient_974_; lean_object* v___x_975_; 
v_serverToClient_974_ = lean_ctor_get(v_server_971_, 1);
lean_inc_ref(v_serverToClient_974_);
lean_dec_ref(v_server_971_);
v___x_975_ = l_Std_Http_Internal_Mock_sendAll(v_serverToClient_974_, v_data_972_);
return v___x_975_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_instTransportServer___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_server_971_ = stack[0].m_obj;
lean_object* v_data_972_ = stack[1].m_obj;
lean_object* v_res_976_;
v_res_976_ = l_Std_Http_Internal_instTransportServer___lam__1(v_server_971_, v_data_972_);
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__1___boxed(lean_object* v_server_977_, lean_object* v_data_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Std_Http_Internal_instTransportServer___lam__1(v_server_977_, v_data_978_);
return v_res_980_;
}
}
lean_object* l_Std_Http_Internal_instTransportServer___lam__2(lean_object* v_server_981_, uint64_t v_x_982_){
_start:
{
lean_object* v_clientToServer_983_; lean_object* v___x_984_; 
v_clientToServer_983_ = lean_ctor_get(v_server_981_, 0);
lean_inc_ref(v_clientToServer_983_);
lean_dec_ref(v_server_981_);
v___x_984_ = l_Std_CloseableChannel_recvSelector___redArg(v_clientToServer_983_);
return v___x_984_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_instTransportServer___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_server_981_ = stack[0].m_obj;
uint64_t v_x_982_ = stack[1].m_num;
lean_object* v_res_985_;
v_res_985_ = l_Std_Http_Internal_instTransportServer___lam__2(v_server_981_, v_x_982_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__2___boxed(lean_object* v_server_986_, lean_object* v_x_987_){
_start:
{
uint64_t v_x_52__boxed_988_; lean_object* v_res_989_; 
v_x_52__boxed_988_ = lean_unbox_uint64(v_x_987_);
lean_dec_ref(v_x_987_);
v_res_989_ = l_Std_Http_Internal_instTransportServer___lam__2(v_server_986_, v_x_52__boxed_988_);
return v_res_989_;
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

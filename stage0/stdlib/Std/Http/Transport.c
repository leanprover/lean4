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
lean_dec_ref_known(v_x_88_, 1);
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
lean_dec_ref_known(v_a_99_, 1);
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
lean_object* v___f_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v_val_130_; lean_object* v___x_134_; 
v___f_126_ = ((lean_object*)(l_Std_Http_instTransportClient___lam__5___closed__1));
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = 0;
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
v_val_130_ = v___x_140_;
goto v___jp_129_;
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
v_val_130_ = v___x_148_;
goto v___jp_129_;
}
}
}
v___jp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v_val_130_);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
v___x_133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_127_, v___x_128_, v___x_132_, v___f_126_);
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
lean_dec_ref_known(v_x_205_, 1);
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
lean_dec_ref_known(v_expect_273_, 1);
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
lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = 0;
lean_inc_ref(v_recvChan_272_);
v___x_287_ = l_Std_CloseableChannel_tryRecv___redArg(v_recvChan_272_);
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_285_, v___x_286_, v___x_289_, v___f_283_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; 
lean_dec_ref(v___f_282_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
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
lean_dec_ref_known(v_a_291_, 1);
if (lean_obj_tag(v_a_301_) == 0)
{
lean_object* v_a_302_; 
lean_dec(v_prio_274_);
lean_dec(v_expect_273_);
lean_dec_ref(v_recvChan_272_);
v_a_302_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v_a_301_, 1);
v_a_279_ = v_a_302_;
goto v___jp_278_;
}
else
{
lean_object* v_a_303_; 
v_a_303_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v_a_301_, 1);
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
lean_dec_ref_known(v___x_290_, 1);
v___x_306_ = l_BaseIO_chainTask___redArg(v_a_305_, v___f_282_, v_prio_274_, v___x_286_);
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
lean_dec_ref_known(v_a_327_, 1);
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
lean_dec_ref_known(v_a_327_, 1);
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2(lean_object* v_recvChan_346_, lean_object* v_expect_347_, lean_object* v___x_348_, lean_object* v_val_349_, uint8_t v___x_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref(v_val_349_);
lean_dec(v___x_348_);
lean_dec(v_expect_347_);
lean_dec_ref(v_recvChan_346_);
v_a_353_ = lean_ctor_get(v_x_351_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v_x_351_);
if (v_isSharedCheck_361_ == 0)
{
v___x_355_ = v_x_351_;
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v_x_351_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_360_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; 
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_373_; 
v_a_362_ = lean_ctor_get(v_x_351_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v_x_351_);
if (v_isSharedCheck_373_ == 0)
{
v___x_364_ = v_x_351_;
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v_x_351_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
lean_inc(v_a_362_);
v___f_366_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed), 3, 1);
lean_closure_set(v___f_366_, 0, v_a_362_);
lean_inc(v___x_348_);
v___x_367_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_346_, v_expect_347_, v___x_348_, v_a_362_, v_val_349_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_372_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___x_371_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_348_, v___x_350_, v___x_370_, v___f_366_);
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed(lean_object* v_recvChan_374_, lean_object* v_expect_375_, lean_object* v___x_376_, lean_object* v_val_377_, lean_object* v___x_378_, lean_object* v_x_379_, lean_object* v___y_380_){
_start:
{
uint8_t v___x_2249__boxed_381_; lean_object* v_res_382_; 
v___x_2249__boxed_381_ = lean_unbox(v___x_378_);
v_res_382_ = l_Std_Http_Internal_Mock_recvJoined___lam__2(v_recvChan_374_, v_expect_375_, v___x_376_, v_val_377_, v___x_2249__boxed_381_, v_x_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3(lean_object* v_recvChan_383_, lean_object* v_expect_384_, lean_object* v___f_385_, lean_object* v_x_386_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
lean_object* v___x_388_; 
lean_dec_ref(v___f_385_);
lean_dec(v_expect_384_);
lean_dec_ref(v_recvChan_383_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v_x_386_);
return v___x_388_;
}
else
{
lean_object* v_a_389_; 
v_a_389_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_a_389_);
if (lean_obj_tag(v_a_389_) == 0)
{
lean_object* v___x_390_; 
lean_dec_ref(v___f_385_);
lean_dec(v_expect_384_);
lean_dec_ref(v_recvChan_383_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v_x_386_);
return v___x_390_;
}
else
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_412_; 
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_386_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v_x_386_, 0);
lean_dec(v_unused_413_);
v___x_392_ = v_x_386_;
v_isShared_393_ = v_isSharedCheck_412_;
goto v_resetjp_391_;
}
else
{
lean_dec(v_x_386_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_412_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_val_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_411_; 
v_val_394_ = lean_ctor_get(v_a_389_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_a_389_);
if (v_isSharedCheck_411_ == 0)
{
v___x_396_ = v_a_389_;
v_isShared_397_ = v_isSharedCheck_411_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_val_394_);
lean_dec(v_a_389_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_411_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___f_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = 0;
v___x_400_ = lean_box(v___x_399_);
v___f_401_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed), 7, 5);
lean_closure_set(v___f_401_, 0, v_recvChan_383_);
lean_closure_set(v___f_401_, 1, v_expect_384_);
lean_closure_set(v___f_401_, 2, v___x_398_);
lean_closure_set(v___f_401_, 3, v_val_394_);
lean_closure_set(v___f_401_, 4, v___x_400_);
v___x_402_ = lean_io_promise_new();
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_402_);
v___x_404_ = v___x_392_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_410_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set_tag(v___x_396_, 0);
lean_ctor_set(v___x_396_, 0, v___x_404_);
v___x_406_ = v___x_396_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_409_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_398_, v___x_399_, v___x_406_, v___f_401_);
v___x_408_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_398_, v___x_399_, v___x_407_, v___f_385_);
return v___x_408_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed(lean_object* v_recvChan_414_, lean_object* v_expect_415_, lean_object* v___f_416_, lean_object* v_x_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_Http_Internal_Mock_recvJoined___lam__3(v_recvChan_414_, v_expect_415_, v___f_416_, v_x_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__4(lean_object* v_a_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_421_, 0, v_a_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5(lean_object* v___f_422_, lean_object* v___f_423_, lean_object* v_x_424_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v___f_423_);
lean_dec_ref(v___f_422_);
v_a_426_ = lean_ctor_get(v_x_424_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_434_ == 0)
{
v___x_428_ = v_x_424_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v_x_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_433_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_436_; uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_a_435_ = lean_ctor_get(v_x_424_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v_x_424_, 1);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = 0;
v___x_438_ = lean_task_map(v___f_422_, v_a_435_, v___x_436_, v___x_437_);
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
v___x_440_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_436_, v___x_437_, v___x_439_, v___f_423_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed(lean_object* v___f_441_, lean_object* v___f_442_, lean_object* v_x_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_Http_Internal_Mock_recvJoined___lam__5(v___f_441_, v___f_442_, v_x_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined(lean_object* v_recvChan_448_, lean_object* v_expect_449_){
_start:
{
lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v___f_453_; lean_object* v___f_454_; lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___f_451_ = ((lean_object*)(l_Std_Http_Internal_Mock_recvJoined___closed__0));
lean_inc_ref(v_recvChan_448_);
v___f_452_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed), 5, 3);
lean_closure_set(v___f_452_, 0, v_recvChan_448_);
lean_closure_set(v___f_452_, 1, v_expect_449_);
lean_closure_set(v___f_452_, 2, v___f_451_);
v___f_453_ = ((lean_object*)(l_Std_Http_Internal_Mock_recvJoined___closed__1));
v___f_454_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed), 4, 2);
lean_closure_set(v___f_454_, 0, v___f_453_);
lean_closure_set(v___f_454_, 1, v___f_452_);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = 0;
v___x_457_ = l_Std_CloseableChannel_recv___redArg(v_recvChan_448_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
v___x_460_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_455_, v___x_456_, v___x_459_, v___f_454_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvJoined___boxed(lean_object* v_recvChan_461_, lean_object* v_expect_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Http_Internal_Mock_recvJoined(v_recvChan_461_, v_expect_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__0(lean_object* v___y_467_){
_start:
{
lean_object* v___y_469_; 
if (lean_obj_tag(v___y_467_) == 0)
{
lean_object* v_a_472_; uint8_t v___x_473_; 
v_a_472_ = lean_ctor_get(v___y_467_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___y_467_, 1);
v___x_473_ = lean_unbox(v_a_472_);
lean_dec(v_a_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___lam__0___closed__0));
v___y_469_ = v___x_474_;
goto v___jp_468_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___lam__0___closed__1));
v___y_469_ = v___x_475_;
goto v___jp_468_;
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v_a_476_ = lean_ctor_get(v___y_467_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___y_467_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___y_467_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___y_467_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
v___jp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc_ref(v___y_469_);
v___x_470_ = lean_mk_io_user_error(v___y_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__1(lean_object* v___f_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v___f_484_);
v_a_487_ = lean_ctor_get(v_x_485_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_485_);
if (v_isSharedCheck_495_ == 0)
{
v___x_489_ = v_x_485_;
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v_x_485_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_494_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_a_496_ = lean_ctor_get(v_x_485_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v_x_485_, 1);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = 0;
v___x_499_ = lean_task_map(v___f_484_, v_a_496_, v___x_497_, v___x_498_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___lam__1___boxed(lean_object* v___f_501_, lean_object* v_x_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_Http_Internal_Mock_send___lam__1(v___f_501_, v_x_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send(lean_object* v_sendChan_508_, lean_object* v_data_509_){
_start:
{
lean_object* v___f_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___f_511_ = ((lean_object*)(l_Std_Http_Internal_Mock_send___closed__1));
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = 0;
v___x_514_ = l_Std_CloseableChannel_send___redArg(v_sendChan_508_, v_data_509_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
v___x_517_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_512_, v___x_513_, v___x_516_, v___f_511_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_send___boxed(lean_object* v_sendChan_518_, lean_object* v_data_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_Http_Internal_Mock_send(v_sendChan_518_, v_data_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0(lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v_x_526_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; 
lean_dec_ref_known(v_x_526_, 1);
v___x_529_ = ((lean_object*)(l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1));
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___lam__0___boxed(lean_object* v_x_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Http_Internal_Mock_sendAll___lam__0(v_x_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(lean_object* v___x_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_544_; 
v_a_536_ = lean_ctor_get(v_x_534_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_x_534_);
if (v_isSharedCheck_544_ == 0)
{
v___x_538_ = v_x_534_;
v_isShared_539_ = v_isSharedCheck_544_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v_x_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_544_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_543_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
}
else
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_553_; 
v_isSharedCheck_553_ = !lean_is_exclusive(v_x_534_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_x_534_, 0);
lean_dec(v_unused_554_);
v___x_546_ = v_x_534_;
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
else
{
lean_dec(v_x_534_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_533_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_552_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed(lean_object* v___x_555_, lean_object* v_x_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(v___x_555_, v_x_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed(lean_object* v_i_559_, lean_object* v_sendChan_560_, lean_object* v_as_561_, lean_object* v_sz_562_, lean_object* v_x_563_, lean_object* v___y_564_){
_start:
{
size_t v_i_boxed_565_; size_t v_sz_boxed_566_; lean_object* v_res_567_; 
v_i_boxed_565_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_sz_boxed_566_ = lean_unbox_usize(v_sz_562_);
lean_dec(v_sz_562_);
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(v_i_boxed_565_, v_sendChan_560_, v_as_561_, v_sz_boxed_566_, v_x_563_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(lean_object* v_sendChan_570_, lean_object* v_as_571_, size_t v_sz_572_, size_t v_i_573_, lean_object* v_b_574_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_lt(v_i_573_, v_sz_572_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v_as_571_);
lean_dec_ref(v_sendChan_570_);
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v_b_574_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v_a_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_579_ = lean_box_usize(v_i_573_);
v___x_580_ = lean_box_usize(v_sz_572_);
lean_inc_ref(v_as_571_);
lean_inc_ref(v_sendChan_570_);
v___f_581_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_581_, 0, v___x_579_);
lean_closure_set(v___f_581_, 1, v_sendChan_570_);
lean_closure_set(v___f_581_, 2, v_as_571_);
lean_closure_set(v___f_581_, 3, v___x_580_);
v___f_582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0));
v_a_583_ = lean_array_uget(v_as_571_, v_i_573_);
lean_dec_ref(v_as_571_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = 0;
v___x_586_ = l_Std_Http_Internal_Mock_send(v_sendChan_570_, v_a_583_);
v___x_587_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_584_, v___x_585_, v___x_586_, v___f_582_);
v___x_588_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_584_, v___x_585_, v___x_587_, v___f_581_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(size_t v_i_589_, lean_object* v_sendChan_590_, lean_object* v_as_591_, size_t v_sz_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_as_591_);
lean_dec_ref(v_sendChan_590_);
v_a_595_ = lean_ctor_get(v_x_593_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_603_ == 0)
{
v___x_597_ = v_x_593_;
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v_x_593_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_623_; 
v_a_604_ = lean_ctor_get(v_x_593_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_623_ == 0)
{
v___x_606_ = v_x_593_;
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v_x_593_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
if (lean_obj_tag(v_a_604_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref(v_as_591_);
lean_dec_ref(v_sendChan_590_);
v_a_608_ = lean_ctor_get(v_a_604_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_618_ == 0)
{
v___x_610_ = v_a_604_;
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v_a_604_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v_a_608_);
v___x_613_ = v___x_606_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_613_);
v___x_615_ = v___x_610_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
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
else
{
lean_object* v_a_619_; size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
lean_del_object(v___x_606_);
v_a_619_ = lean_ctor_get(v_a_604_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v_a_604_, 1);
v___x_620_ = ((size_t)1ULL);
v___x_621_ = lean_usize_add(v_i_589_, v___x_620_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_590_, v_as_591_, v_sz_592_, v___x_621_, v_a_619_);
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___boxed(lean_object* v_sendChan_624_, lean_object* v_as_625_, lean_object* v_sz_626_, lean_object* v_i_627_, lean_object* v_b_628_, lean_object* v___y_629_){
_start:
{
size_t v_sz_boxed_630_; size_t v_i_boxed_631_; lean_object* v_res_632_; 
v_sz_boxed_630_ = lean_unbox_usize(v_sz_626_);
lean_dec(v_sz_626_);
v_i_boxed_631_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_624_, v_as_625_, v_sz_boxed_630_, v_i_boxed_631_, v_b_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll(lean_object* v_sendChan_634_, lean_object* v_data_635_){
_start:
{
lean_object* v___f_637_; lean_object* v___x_638_; size_t v_sz_639_; size_t v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___f_637_ = ((lean_object*)(l_Std_Http_Internal_Mock_sendAll___closed__0));
v___x_638_ = lean_box(0);
v_sz_639_ = lean_array_size(v_data_635_);
v___x_640_ = ((size_t)0ULL);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = 0;
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_634_, v_data_635_, v_sz_639_, v___x_640_, v___x_638_);
v___x_644_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_641_, v___x_642_, v___x_643_, v___f_637_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_sendAll___boxed(lean_object* v_sendChan_645_, lean_object* v_data_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_Http_Internal_Mock_sendAll(v_sendChan_645_, v_data_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_recvSelector(lean_object* v_recvChan_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_CloseableChannel_recvSelector___redArg(v_recvChan_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan(lean_object* v_client_651_){
_start:
{
lean_object* v_serverToClient_652_; 
v_serverToClient_652_ = lean_ctor_get(v_client_651_, 1);
lean_inc_ref(v_serverToClient_652_);
return v_serverToClient_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getRecvChan___boxed(lean_object* v_client_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Http_Internal_Mock_Client_getRecvChan(v_client_653_);
lean_dec_ref(v_client_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan(lean_object* v_client_655_){
_start:
{
lean_object* v_clientToServer_656_; 
v_clientToServer_656_ = lean_ctor_get(v_client_655_, 0);
lean_inc_ref(v_clientToServer_656_);
return v_clientToServer_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_getSendChan___boxed(lean_object* v_client_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_Http_Internal_Mock_Client_getSendChan(v_client_657_);
lean_dec_ref(v_client_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_send(lean_object* v_client_659_, lean_object* v_data_660_){
_start:
{
lean_object* v_clientToServer_662_; lean_object* v___x_663_; 
v_clientToServer_662_ = lean_ctor_get(v_client_659_, 0);
lean_inc_ref(v_clientToServer_662_);
lean_dec_ref(v_client_659_);
v___x_663_ = l_Std_Http_Internal_Mock_send(v_clientToServer_662_, v_data_660_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_send___boxed(lean_object* v_client_664_, lean_object* v_data_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_Http_Internal_Mock_Client_send(v_client_664_, v_data_665_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f(lean_object* v_client_668_, lean_object* v_expect_669_){
_start:
{
lean_object* v_serverToClient_671_; lean_object* v___x_672_; 
v_serverToClient_671_ = lean_ctor_get(v_client_668_, 1);
lean_inc_ref(v_serverToClient_671_);
lean_dec_ref(v_client_668_);
v___x_672_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_671_, v_expect_669_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_recv_x3f___boxed(lean_object* v_client_673_, lean_object* v_expect_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_Http_Internal_Mock_Client_recv_x3f(v_client_673_, v_expect_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(lean_object* v___x_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_680_; 
lean_inc_ref(v___x_677_);
v___x_680_ = l_Std_CloseableChannel_tryRecv___redArg(v___x_677_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_dec_ref(v___x_677_);
return v_a_678_;
}
else
{
lean_object* v_val_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; 
v_val_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_byte_array_size(v_a_678_);
v___x_684_ = lean_byte_array_size(v_val_681_);
v___x_685_ = 0;
v___x_686_ = lean_byte_array_copy_slice(v_val_681_, v___x_682_, v_a_678_, v___x_683_, v___x_684_, v___x_685_);
lean_dec(v_val_681_);
v_a_678_ = v___x_686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg___boxed(lean_object* v___x_688_, lean_object* v_a_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v___x_688_, v_a_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(lean_object* v_client_692_){
_start:
{
lean_object* v_serverToClient_694_; lean_object* v___x_695_; 
v_serverToClient_694_ = lean_ctor_get(v_client_692_, 1);
lean_inc_ref_n(v_serverToClient_694_, 2);
lean_dec_ref(v_client_692_);
v___x_695_ = l_Std_CloseableChannel_tryRecv___redArg(v_serverToClient_694_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_dec_ref(v_serverToClient_694_);
return v___x_695_;
}
else
{
lean_object* v_val_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_val_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_704_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_val_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v_serverToClient_694_, v_val_696_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg___boxed(lean_object* v_client_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f(lean_object* v_client_708_, uint64_t v___expect_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_708_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_tryRecv_x3f___boxed(lean_object* v_client_712_, lean_object* v___expect_713_, lean_object* v_a_714_){
_start:
{
uint64_t v___expect_boxed_715_; lean_object* v_res_716_; 
v___expect_boxed_715_ = lean_unbox_uint64(v___expect_713_);
lean_dec_ref(v___expect_713_);
v_res_716_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f(v_client_712_, v___expect_boxed_715_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(lean_object* v___x_717_, lean_object* v_inst_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v___x_717_, v_a_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___boxed(lean_object* v___x_722_, lean_object* v_inst_723_, lean_object* v_a_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(v___x_722_, v_inst_723_, v_a_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_close(lean_object* v_client_731_){
_start:
{
lean_object* v_clientToServer_733_; lean_object* v_serverToClient_734_; uint8_t v___x_762_; 
v_clientToServer_733_ = lean_ctor_get(v_client_731_, 0);
lean_inc_ref_n(v_clientToServer_733_, 2);
v_serverToClient_734_ = lean_ctor_get(v_client_731_, 1);
lean_inc_ref(v_serverToClient_734_);
lean_dec_ref(v_client_731_);
v___x_762_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_733_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_733_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_dec_ref_known(v___x_763_, 1);
goto v___jp_735_;
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_serverToClient_734_);
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_777_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_777_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_777_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
uint8_t v___x_768_; 
v___x_768_ = lean_unbox(v_a_764_);
lean_dec(v_a_764_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_769_);
v___x_771_ = v___x_766_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_773_);
v___x_775_ = v___x_766_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
else
{
lean_dec_ref(v_clientToServer_733_);
goto v___jp_735_;
}
v___jp_735_:
{
uint8_t v___x_736_; 
lean_inc_ref(v_serverToClient_734_);
v___x_736_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_734_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
v___x_737_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_734_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_759_; 
v_a_746_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_759_ == 0)
{
v___x_748_ = v___x_737_;
v_isShared_749_ = v_isSharedCheck_759_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_737_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_759_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
uint8_t v___x_750_; 
v___x_750_ = lean_unbox(v_a_746_);
lean_dec(v_a_746_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_751_);
v___x_753_ = v___x_748_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_755_);
v___x_757_ = v___x_748_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref(v_serverToClient_734_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Client_close___boxed(lean_object* v_client_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_Http_Internal_Mock_Client_close(v_client_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan(lean_object* v_server_781_){
_start:
{
lean_object* v_clientToServer_782_; 
v_clientToServer_782_ = lean_ctor_get(v_server_781_, 0);
lean_inc_ref(v_clientToServer_782_);
return v_clientToServer_782_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getRecvChan___boxed(lean_object* v_server_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_Http_Internal_Mock_Server_getRecvChan(v_server_783_);
lean_dec_ref(v_server_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan(lean_object* v_server_785_){
_start:
{
lean_object* v_serverToClient_786_; 
v_serverToClient_786_ = lean_ctor_get(v_server_785_, 1);
lean_inc_ref(v_serverToClient_786_);
return v_serverToClient_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_getSendChan___boxed(lean_object* v_server_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_Http_Internal_Mock_Server_getSendChan(v_server_787_);
lean_dec_ref(v_server_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_send(lean_object* v_server_789_, lean_object* v_data_790_){
_start:
{
lean_object* v_serverToClient_792_; lean_object* v___x_793_; 
v_serverToClient_792_ = lean_ctor_get(v_server_789_, 1);
lean_inc_ref(v_serverToClient_792_);
lean_dec_ref(v_server_789_);
v___x_793_ = l_Std_Http_Internal_Mock_send(v_serverToClient_792_, v_data_790_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_send___boxed(lean_object* v_server_794_, lean_object* v_data_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_Http_Internal_Mock_Server_send(v_server_794_, v_data_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f(lean_object* v_server_798_, lean_object* v_expect_799_){
_start:
{
lean_object* v_clientToServer_801_; lean_object* v___x_802_; 
v_clientToServer_801_ = lean_ctor_get(v_server_798_, 0);
lean_inc_ref(v_clientToServer_801_);
lean_dec_ref(v_server_798_);
v___x_802_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_801_, v_expect_799_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_recv_x3f___boxed(lean_object* v_server_803_, lean_object* v_expect_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_Http_Internal_Mock_Server_recv_x3f(v_server_803_, v_expect_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(lean_object* v_server_807_){
_start:
{
lean_object* v_clientToServer_809_; lean_object* v___x_810_; 
v_clientToServer_809_ = lean_ctor_get(v_server_807_, 0);
lean_inc_ref_n(v_clientToServer_809_, 2);
lean_dec_ref(v_server_807_);
v___x_810_ = l_Std_CloseableChannel_tryRecv___redArg(v_clientToServer_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_dec_ref(v_clientToServer_809_);
return v___x_810_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v_val_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_819_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v_clientToServer_809_, v_val_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg___boxed(lean_object* v_server_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f(lean_object* v_server_823_, uint64_t v___expect_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_823_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_tryRecv_x3f___boxed(lean_object* v_server_827_, lean_object* v___expect_828_, lean_object* v_a_829_){
_start:
{
uint64_t v___expect_boxed_830_; lean_object* v_res_831_; 
v___expect_boxed_830_ = lean_unbox_uint64(v___expect_828_);
lean_dec_ref(v___expect_828_);
v_res_831_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f(v_server_827_, v___expect_boxed_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_close(lean_object* v_server_832_){
_start:
{
lean_object* v_clientToServer_834_; lean_object* v_serverToClient_835_; uint8_t v___x_863_; 
v_clientToServer_834_ = lean_ctor_get(v_server_832_, 0);
lean_inc_ref_n(v_clientToServer_834_, 2);
v_serverToClient_835_ = lean_ctor_get(v_server_832_, 1);
lean_inc_ref(v_serverToClient_835_);
lean_dec_ref(v_server_832_);
v___x_863_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_834_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
v___x_864_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_834_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_dec_ref_known(v___x_864_, 1);
goto v___jp_836_;
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v_serverToClient_835_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_878_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___x_869_; 
v___x_869_ = lean_unbox(v_a_865_);
lean_dec(v_a_865_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_874_);
v___x_876_ = v___x_867_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
else
{
lean_dec_ref(v_clientToServer_834_);
goto v___jp_836_;
}
v___jp_836_:
{
uint8_t v___x_837_; 
lean_inc_ref(v_serverToClient_835_);
v___x_837_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_835_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_835_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_860_; 
v_a_847_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_860_ == 0)
{
v___x_849_ = v___x_838_;
v_isShared_850_ = v_isSharedCheck_860_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_838_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_860_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
uint8_t v___x_851_; 
v___x_851_ = lean_unbox(v_a_847_);
lean_dec(v_a_847_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_852_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__0));
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_852_);
v___x_854_ = v___x_849_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
else
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = ((lean_object*)(l_Std_Http_Internal_Mock_Client_close___closed__1));
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_856_);
v___x_858_ = v___x_849_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec_ref(v_serverToClient_835_);
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Mock_Server_close___boxed(lean_object* v_server_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_Http_Internal_Mock_Server_close(v_server_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__0(lean_object* v_client_882_, uint64_t v_expect_883_){
_start:
{
lean_object* v_serverToClient_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_serverToClient_885_ = lean_ctor_get(v_client_882_, 1);
lean_inc_ref(v_serverToClient_885_);
lean_dec_ref(v_client_882_);
v___x_886_ = lean_box_uint64(v_expect_883_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
v___x_888_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_885_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__0___boxed(lean_object* v_client_889_, lean_object* v_expect_890_, lean_object* v___y_891_){
_start:
{
uint64_t v_expect_boxed_892_; lean_object* v_res_893_; 
v_expect_boxed_892_ = lean_unbox_uint64(v_expect_890_);
lean_dec_ref(v_expect_890_);
v_res_893_ = l_Std_Http_Internal_instTransportClient___lam__0(v_client_889_, v_expect_boxed_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__1(lean_object* v_client_894_, lean_object* v_data_895_){
_start:
{
lean_object* v_clientToServer_897_; lean_object* v___x_898_; 
v_clientToServer_897_ = lean_ctor_get(v_client_894_, 0);
lean_inc_ref(v_clientToServer_897_);
lean_dec_ref(v_client_894_);
v___x_898_ = l_Std_Http_Internal_Mock_sendAll(v_clientToServer_897_, v_data_895_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__1___boxed(lean_object* v_client_899_, lean_object* v_data_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_Http_Internal_instTransportClient___lam__1(v_client_899_, v_data_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__2(lean_object* v_client_903_, uint64_t v_x_904_){
_start:
{
lean_object* v_serverToClient_905_; lean_object* v___x_906_; 
v_serverToClient_905_ = lean_ctor_get(v_client_903_, 1);
lean_inc_ref(v_serverToClient_905_);
lean_dec_ref(v_client_903_);
v___x_906_ = l_Std_CloseableChannel_recvSelector___redArg(v_serverToClient_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportClient___lam__2___boxed(lean_object* v_client_907_, lean_object* v_x_908_){
_start:
{
uint64_t v_x_44__boxed_909_; lean_object* v_res_910_; 
v_x_44__boxed_909_ = lean_unbox_uint64(v_x_908_);
lean_dec_ref(v_x_908_);
v_res_910_ = l_Std_Http_Internal_instTransportClient___lam__2(v_client_907_, v_x_44__boxed_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__0(lean_object* v_server_921_, uint64_t v_expect_922_){
_start:
{
lean_object* v_clientToServer_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_clientToServer_924_ = lean_ctor_get(v_server_921_, 0);
lean_inc_ref(v_clientToServer_924_);
lean_dec_ref(v_server_921_);
v___x_925_ = lean_box_uint64(v_expect_922_);
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
v___x_927_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_924_, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__0___boxed(lean_object* v_server_928_, lean_object* v_expect_929_, lean_object* v___y_930_){
_start:
{
uint64_t v_expect_boxed_931_; lean_object* v_res_932_; 
v_expect_boxed_931_ = lean_unbox_uint64(v_expect_929_);
lean_dec_ref(v_expect_929_);
v_res_932_ = l_Std_Http_Internal_instTransportServer___lam__0(v_server_928_, v_expect_boxed_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__1(lean_object* v_server_933_, lean_object* v_data_934_){
_start:
{
lean_object* v_serverToClient_936_; lean_object* v___x_937_; 
v_serverToClient_936_ = lean_ctor_get(v_server_933_, 1);
lean_inc_ref(v_serverToClient_936_);
lean_dec_ref(v_server_933_);
v___x_937_ = l_Std_Http_Internal_Mock_sendAll(v_serverToClient_936_, v_data_934_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__1___boxed(lean_object* v_server_938_, lean_object* v_data_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_Http_Internal_instTransportServer___lam__1(v_server_938_, v_data_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__2(lean_object* v_server_942_, uint64_t v_x_943_){
_start:
{
lean_object* v_clientToServer_944_; lean_object* v___x_945_; 
v_clientToServer_944_ = lean_ctor_get(v_server_942_, 0);
lean_inc_ref(v_clientToServer_944_);
lean_dec_ref(v_server_942_);
v___x_945_ = l_Std_CloseableChannel_recvSelector___redArg(v_clientToServer_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instTransportServer___lam__2___boxed(lean_object* v_server_946_, lean_object* v_x_947_){
_start:
{
uint64_t v_x_44__boxed_948_; lean_object* v_res_949_; 
v_x_44__boxed_948_ = lean_unbox_uint64(v_x_947_);
lean_dec_ref(v_x_947_);
v_res_949_ = l_Std_Http_Internal_instTransportServer___lam__2(v_server_946_, v_x_44__boxed_948_);
return v_res_949_;
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

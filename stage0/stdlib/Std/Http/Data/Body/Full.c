// Lean compiler output
// Module: Std.Http.Data.Body.Full
// Imports: public import Std.Sync public import Std.Http.Data.Request public import Std.Http.Data.Response public import Std.Http.Data.Body.Any public import Init.Data.ByteArray
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* l_Std_Http_Chunk_ofByteArray(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentType;
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Http_Request_Builder_header(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_header(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_ofByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_ofByteArray___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Full_ofByteArray___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_ofByteArray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_close___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_close___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Full_close___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_close___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_isClosed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_isClosed___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Full_isClosed___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_isClosed___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Full_isClosed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_isClosed___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Full_isClosed___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Full_isClosed___closed__1 = (const lean_object*)&l_Std_Http_Body_Full_isClosed___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Full_getKnownSize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_getKnownSize___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Full_getKnownSize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_Full_getKnownSize___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Body_Full_getKnownSize___lam__0___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_Full_getKnownSize___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_Full_getKnownSize___lam__0___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Body_Full_getKnownSize___lam__0___closed__2_value;
static const lean_ctor_object l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Full_getKnownSize___lam__0___closed__2_value)}};
static const lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_getKnownSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_getKnownSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Full_getKnownSize___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_getKnownSize___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Full_getKnownSize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_getKnownSize___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Full_getKnownSize___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Full_getKnownSize___closed__1 = (const lean_object*)&l_Std_Http_Body_Full_getKnownSize___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_tryRecv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_tryRecv___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Full_tryRecv___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_tryRecv___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_recvSelector___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_recvSelector___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Full_recvSelector___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_recvSelector___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_recvSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_recvSelector___lam__2___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Full_recvSelector___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_recvSelector___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector(lean_object*);
static const lean_ctor_object l_Std_Http_Body_instFull___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_instFull___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_instFull___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_instFull___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_instFull___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Body_instFull___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Body_instFull___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instFull___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instFull___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instFull___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instFull___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instFull___closed__0 = (const lean_object*)&l_Std_Http_Body_instFull___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instFull___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_recv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instFull___closed__1 = (const lean_object*)&l_Std_Http_Body_instFull___closed__1_value;
static const lean_closure_object l_Std_Http_Body_instFull___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_close___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instFull___closed__2 = (const lean_object*)&l_Std_Http_Body_instFull___closed__2_value;
static const lean_closure_object l_Std_Http_Body_instFull___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_isClosed___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instFull___closed__3 = (const lean_object*)&l_Std_Http_Body_instFull___closed__3_value;
static const lean_closure_object l_Std_Http_Body_instFull___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_recvSelector, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instFull___closed__4 = (const lean_object*)&l_Std_Http_Body_instFull___closed__4_value;
static const lean_closure_object l_Std_Http_Body_instFull___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_tryRecv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instFull___closed__5 = (const lean_object*)&l_Std_Http_Body_instFull___closed__5_value;
static const lean_closure_object l_Std_Http_Body_instFull___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_getKnownSize___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instFull___closed__6 = (const lean_object*)&l_Std_Http_Body_instFull___closed__6_value;
static const lean_ctor_object l_Std_Http_Body_instFull___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_instFull___closed__1_value),((lean_object*)&l_Std_Http_Body_instFull___closed__2_value),((lean_object*)&l_Std_Http_Body_instFull___closed__3_value),((lean_object*)&l_Std_Http_Body_instFull___closed__4_value),((lean_object*)&l_Std_Http_Body_instFull___closed__5_value),((lean_object*)&l_Std_Http_Body_instFull___closed__6_value),((lean_object*)&l_Std_Http_Body_instFull___closed__0_value)}};
static const lean_object* l_Std_Http_Body_instFull___closed__7 = (const lean_object*)&l_Std_Http_Body_instFull___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instFull = (const lean_object*)&l_Std_Http_Body_instFull___closed__7_value;
static const lean_closure_object l_Std_Http_Body_instCoeFullAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Any_ofBody, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instFull___closed__7_value)} };
static const lean_object* l_Std_Http_Body_instCoeFullAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeFullAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeFullAny = (const lean_object*)&l_Std_Http_Body_instCoeFullAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseFullAny___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeResponseFullAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeResponseFullAny___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instFull___closed__7_value)} };
static const lean_object* l_Std_Http_Body_instCoeResponseFullAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeResponseFullAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeResponseFullAny = (const lean_object*)&l_Std_Http_Body_instCoeResponseFullAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instFull___closed__7_value)} };
static const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__1 = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny = (const lean_object*)&l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Request_Builder_bytes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "application/octet-stream"};
static const lean_object* l_Std_Http_Request_Builder_bytes___closed__0 = (const lean_object*)&l_Std_Http_Request_Builder_bytes___closed__0_value;
static lean_once_cell_t l_Std_Http_Request_Builder_bytes___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_Builder_bytes___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_bytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_bytes___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Request_Builder_text___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "text/plain; charset=utf-8"};
static const lean_object* l_Std_Http_Request_Builder_text___closed__0 = (const lean_object*)&l_Std_Http_Request_Builder_text___closed__0_value;
static lean_once_cell_t l_Std_Http_Request_Builder_text___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_Builder_text___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_text(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_text___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Request_Builder_json___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "application/json"};
static const lean_object* l_Std_Http_Request_Builder_json___closed__0 = (const lean_object*)&l_Std_Http_Request_Builder_json___closed__0_value;
static lean_once_cell_t l_Std_Http_Request_Builder_json___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_Builder_json___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_json(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_json___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Request_Builder_html___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "text/html; charset=utf-8"};
static const lean_object* l_Std_Http_Request_Builder_html___closed__0 = (const lean_object*)&l_Std_Http_Request_Builder_html___closed__0_value;
static lean_once_cell_t l_Std_Http_Request_Builder_html___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_Builder_html___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_html(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_html___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_bytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_bytes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_text(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_text___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_json(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_json___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_html(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_html___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(lean_object* v_val_5_, lean_object* v_x_6_){
_start:
{
if (lean_obj_tag(v_x_6_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_16_; 
lean_dec_ref(v_val_5_);
v_a_8_ = lean_ctor_get(v_x_6_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_16_ == 0)
{
v___x_10_ = v_x_6_;
v_isShared_11_ = v_isSharedCheck_16_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v_x_6_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_16_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_13_; 
if (v_isShared_11_ == 0)
{
v___x_13_ = v___x_10_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_a_8_);
v___x_13_ = v_reuseFailAlloc_15_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
lean_object* v___x_14_; 
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
}
else
{
lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_28_; 
v_isSharedCheck_28_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_28_ == 0)
{
lean_object* v_unused_29_; 
v_unused_29_ = lean_ctor_get(v_x_6_, 0);
lean_dec(v_unused_29_);
v___x_18_ = v_x_6_;
v_isShared_19_ = v_isSharedCheck_28_;
goto v_resetjp_17_;
}
else
{
lean_dec(v_x_6_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_28_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
uint8_t v___x_20_; 
v___x_20_ = l_ByteArray_isEmpty(v_val_5_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_21_ = l_Std_Http_Chunk_ofByteArray(v_val_5_);
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_22_);
v___x_24_ = v___x_18_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_22_);
v___x_24_ = v_reuseFailAlloc_26_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; 
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
}
else
{
lean_object* v___x_27_; 
lean_del_object(v___x_18_);
lean_dec_ref(v_val_5_);
v___x_27_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1));
return v___x_27_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed(lean_object* v_val_30_, lean_object* v_x_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(v_val_30_, v_x_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(lean_object* v_a_34_, lean_object* v_x_35_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_45_; 
v_a_37_ = lean_ctor_get(v_x_35_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v_x_35_);
if (v_isSharedCheck_45_ == 0)
{
v___x_39_ = v_x_35_;
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v_x_35_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_44_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; 
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_68_; 
v_a_46_ = lean_ctor_get(v_x_35_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v_x_35_);
if (v_isSharedCheck_68_ == 0)
{
v___x_48_ = v_x_35_;
v_isShared_49_ = v_isSharedCheck_68_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v_x_35_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_68_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
if (lean_obj_tag(v_a_46_) == 0)
{
lean_object* v___x_50_; 
lean_del_object(v___x_48_);
v___x_50_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1));
return v___x_50_;
}
else
{
lean_object* v_val_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_67_; 
v_val_51_ = lean_ctor_get(v_a_46_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_a_46_);
if (v_isSharedCheck_67_ == 0)
{
v___x_53_ = v_a_46_;
v_isShared_54_ = v_isSharedCheck_67_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_val_51_);
lean_dec(v_a_46_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_67_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___f_57_; lean_object* v___x_59_; 
v___x_55_ = lean_box(0);
v___x_56_ = lean_st_ref_set(v_a_34_, v___x_55_);
v___f_57_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed), 3, 1);
lean_closure_set(v___f_57_, 0, v_val_51_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_56_);
v___x_59_ = v___x_48_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_56_);
v___x_59_ = v_reuseFailAlloc_66_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_61_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set_tag(v___x_53_, 0);
lean_ctor_set(v___x_53_, 0, v___x_59_);
v___x_61_ = v___x_53_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_59_);
v___x_61_ = v_reuseFailAlloc_65_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; uint8_t v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = 0;
v___x_64_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_62_, v___x_63_, v___x_61_, v___f_57_);
return v___x_64_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed(lean_object* v_a_69_, lean_object* v_x_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(v_a_69_, v_x_70_);
lean_dec(v_a_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; 
v___x_75_ = lean_st_ref_get(v_a_73_);
lean_inc(v_a_73_);
v___f_76_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed), 3, 1);
lean_closure_set(v___f_76_, 0, v_a_73_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = 0;
v___x_81_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_79_, v___x_80_, v___x_78_, v___f_76_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed(lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v_a_82_);
lean_dec(v_a_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0(lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
v_a_87_ = lean_ctor_get(v_x_85_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_95_ == 0)
{
v___x_89_ = v_x_85_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v_x_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_94_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_104_; 
v_a_96_ = lean_ctor_get(v_x_85_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_104_ == 0)
{
v___x_98_ = v_x_85_;
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v_x_85_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_103_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0___boxed(lean_object* v_x_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_Http_Body_Full_ofByteArray___lam__0(v_x_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray(lean_object* v_data_109_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; 
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v_data_109_);
v___x_112_ = l_Std_Mutex_new___redArg(v___x_111_);
v___f_113_ = ((lean_object*)(l_Std_Http_Body_Full_ofByteArray___closed__0));
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = 0;
v___x_118_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_116_, v___x_117_, v___x_115_, v___f_113_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___boxed(lean_object* v_data_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_Http_Body_Full_ofByteArray(v_data_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString(lean_object* v_data_122_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___f_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; 
v___x_124_ = lean_string_to_utf8(v_data_122_);
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
v___x_126_ = l_Std_Mutex_new___redArg(v___x_125_);
v___f_127_ = ((lean_object*)(l_Std_Http_Body_Full_ofByteArray___closed__0));
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = 0;
v___x_132_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_130_, v___x_131_, v___x_129_, v___f_127_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___boxed(lean_object* v_data_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_Http_Body_Full_ofString(v_data_133_);
lean_dec_ref(v_data_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0(lean_object* v_mutex_136_, lean_object* v_x_137_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_io_basemutex_unlock(v_mutex_136_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0___boxed(lean_object* v_mutex_142_, lean_object* v_x_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0(v_mutex_142_, v_x_143_);
lean_dec(v_x_143_);
lean_dec(v_mutex_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(lean_object* v_k_146_, lean_object* v_ref_147_, lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_ref_147_);
lean_dec_ref(v_k_146_);
v_a_150_ = lean_ctor_get(v_x_148_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_158_ == 0)
{
v___x_152_ = v_x_148_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v_x_148_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
}
else
{
lean_object* v___x_159_; 
lean_dec_ref(v_x_148_);
v___x_159_ = lean_apply_2(v_k_146_, v_ref_147_, lean_box(0));
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed(lean_object* v_k_160_, lean_object* v_ref_161_, lean_object* v_x_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(v_k_160_, v_ref_161_, v_x_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(lean_object* v_mutex_165_, lean_object* v___f_166_){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; 
v___x_168_ = lean_io_basemutex_lock(v_mutex_165_);
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = 0;
v___x_173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_171_, v___x_172_, v___x_170_, v___f_166_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed(lean_object* v_mutex_174_, lean_object* v___f_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(v_mutex_174_, v___f_175_);
lean_dec(v_mutex_174_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(lean_object* v___y_178_){
_start:
{
if (lean_obj_tag(v___y_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___y_178_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___y_178_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___y_178_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___y_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
v_a_187_ = lean_ctor_get(v___y_178_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___y_178_);
if (v_isSharedCheck_195_ == 0)
{
v___x_189_ = v___y_178_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___y_178_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_fst_191_; lean_object* v___x_193_; 
v_fst_191_ = lean_ctor_get(v_a_187_, 0);
lean_inc(v_fst_191_);
lean_dec(v_a_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v_fst_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_fst_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(lean_object* v_mutex_197_, lean_object* v_k_198_){
_start:
{
lean_object* v_ref_200_; lean_object* v_mutex_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___y_209_; 
v_ref_200_ = lean_ctor_get(v_mutex_197_, 0);
lean_inc(v_ref_200_);
v_mutex_201_ = lean_ctor_get(v_mutex_197_, 1);
lean_inc_n(v_mutex_201_, 2);
lean_dec_ref(v_mutex_197_);
v___f_202_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_202_, 0, v_mutex_201_);
v___f_203_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_203_, 0, v_k_198_);
lean_closure_set(v___f_203_, 1, v_ref_200_);
v___f_204_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_204_, 0, v_mutex_201_);
lean_closure_set(v___f_204_, 1, v___f_203_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = 0;
v___x_207_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_204_, v___f_202_, v___x_205_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_211_; 
v_a_211_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_211_);
lean_dec_ref(v___x_207_);
if (lean_obj_tag(v_a_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_a_212_ = lean_ctor_get(v_a_211_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_a_211_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v_a_211_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v_a_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
v___y_209_ = v___x_217_;
goto v___jp_208_;
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_a_220_ = lean_ctor_get(v_a_211_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_a_211_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v_a_211_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v_a_211_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_fst_224_; lean_object* v___x_226_; 
v_fst_224_ = lean_ctor_get(v_a_220_, 0);
lean_inc(v_fst_224_);
lean_dec(v_a_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v_fst_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_fst_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
v___y_209_ = v___x_226_;
goto v___jp_208_;
}
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_238_; 
v_a_229_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_238_ == 0)
{
v___x_231_ = v___x_207_;
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_207_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___f_233_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0));
v___x_234_ = lean_task_map(v___f_233_, v_a_229_, v___x_205_, v___x_206_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
v___jp_208_:
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___y_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___boxed(lean_object* v_mutex_239_, lean_object* v_k_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_mutex_239_, v_k_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_mutex_245_, lean_object* v_k_246_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_mutex_245_, v_k_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___boxed(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_mutex_251_, lean_object* v_k_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(v_00_u03b1_249_, v_00_u03b2_250_, v_mutex_251_, v_k_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv(lean_object* v_full_255_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 2, 0);
v___x_258_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_full_255_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv___boxed(lean_object* v_full_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Http_Body_Full_recv(v_full_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0(lean_object* v___x_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_st_ref_set(v___y_263_, v___x_262_);
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0___boxed(lean_object* v___x_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Http_Body_Full_close___lam__0(v___x_268_, v___y_269_);
lean_dec(v___y_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close(lean_object* v_full_274_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; 
v___f_276_ = ((lean_object*)(l_Std_Http_Body_Full_close___closed__0));
v___x_277_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_full_274_, v___f_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___boxed(lean_object* v_full_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Http_Body_Full_close(v_full_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__0(lean_object* v_x_281_){
_start:
{
uint8_t v___y_284_; 
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_296_; 
v_a_288_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_296_ == 0)
{
v___x_290_ = v_x_281_;
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v_x_281_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_295_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
else
{
lean_object* v_a_297_; 
v_a_297_ = lean_ctor_get(v_x_281_, 0);
lean_inc(v_a_297_);
lean_dec_ref(v_x_281_);
if (lean_obj_tag(v_a_297_) == 0)
{
uint8_t v___x_298_; 
v___x_298_ = 1;
v___y_284_ = v___x_298_;
goto v___jp_283_;
}
else
{
uint8_t v___x_299_; 
lean_dec_ref(v_a_297_);
v___x_299_ = 0;
v___y_284_ = v___x_299_;
goto v___jp_283_;
}
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_box(v___y_284_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__0___boxed(lean_object* v_x_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Http_Body_Full_isClosed___lam__0(v_x_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__1(lean_object* v___f_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = 0;
v___x_311_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_309_, v___x_310_, v___x_308_, v___f_303_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__1___boxed(lean_object* v___f_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_Http_Body_Full_isClosed___lam__1(v___f_312_, v___y_313_);
lean_dec(v___y_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed(lean_object* v_full_319_){
_start:
{
lean_object* v___f_321_; lean_object* v___x_322_; 
v___f_321_ = ((lean_object*)(l_Std_Http_Body_Full_isClosed___closed__1));
v___x_322_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_full_319_, v___f_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___boxed(lean_object* v_full_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_Http_Body_Full_isClosed(v_full_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0(lean_object* v_x_334_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_344_; 
v_a_336_ = lean_ctor_get(v_x_334_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_334_);
if (v_isSharedCheck_344_ == 0)
{
v___x_338_ = v_x_334_;
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v_x_334_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_343_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_364_; 
v_a_345_ = lean_ctor_get(v_x_334_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_334_);
if (v_isSharedCheck_364_ == 0)
{
v___x_347_ = v_x_334_;
v_isShared_348_ = v_isSharedCheck_364_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v_x_334_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_364_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
if (lean_obj_tag(v_a_345_) == 0)
{
lean_object* v___x_349_; 
lean_del_object(v___x_347_);
v___x_349_ = ((lean_object*)(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3));
return v___x_349_;
}
else
{
lean_object* v_val_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_363_; 
v_val_350_ = lean_ctor_get(v_a_345_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_a_345_);
if (v_isSharedCheck_363_ == 0)
{
v___x_352_ = v_a_345_;
v_isShared_353_ = v_isSharedCheck_363_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_val_350_);
lean_dec(v_a_345_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_363_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_354_ = lean_byte_array_size(v_val_350_);
lean_dec(v_val_350_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_355_);
v___x_357_ = v___x_352_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_362_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_357_);
v___x_359_ = v___x_347_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_361_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___boxed(lean_object* v_x_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_Http_Body_Full_getKnownSize___lam__0(v_x_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1(lean_object* v___f_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; 
v___x_371_ = lean_st_ref_get(v___y_369_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = 0;
v___x_376_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_374_, v___x_375_, v___x_373_, v___f_368_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1___boxed(lean_object* v___f_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Http_Body_Full_getKnownSize___lam__1(v___f_377_, v___y_378_);
lean_dec(v___y_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize(lean_object* v_full_384_){
_start:
{
lean_object* v___f_386_; lean_object* v___x_387_; 
v___f_386_ = ((lean_object*)(l_Std_Http_Body_Full_getKnownSize___closed__1));
v___x_387_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_full_384_, v___f_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___boxed(lean_object* v_full_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Http_Body_Full_getKnownSize(v_full_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___lam__0(lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_393_ = lean_ctor_get(v_x_391_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v_x_391_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v_x_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_400_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_411_; 
v_a_402_ = lean_ctor_get(v_x_391_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_411_ == 0)
{
v___x_404_ = v_x_391_;
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v_x_391_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v_a_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_410_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; 
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___lam__0___boxed(lean_object* v_x_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Http_Body_Full_tryRecv___lam__0(v_x_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv(lean_object* v_full_416_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___f_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; 
v___x_418_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 2, 0);
v___x_419_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_full_416_, v___x_418_);
v___f_420_ = ((lean_object*)(l_Std_Http_Body_Full_tryRecv___closed__0));
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = 0;
v___x_423_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_421_, v___x_422_, v___x_419_, v___f_420_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___boxed(lean_object* v_full_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_Http_Body_Full_tryRecv(v_full_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(lean_object* v_promise_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_438_; 
v_a_430_ = lean_ctor_get(v_x_428_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_438_ == 0)
{
v___x_432_ = v_x_428_;
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v_x_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_437_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_io_promise_resolve(v_x_428_, v_promise_427_);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed(lean_object* v_promise_442_, lean_object* v_x_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(v_promise_442_, v_x_443_);
lean_dec(v_promise_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(lean_object* v_lose_446_, lean_object* v___y_447_, lean_object* v___f_448_, lean_object* v_x_449_){
_start:
{
if (lean_obj_tag(v_x_449_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v___f_448_);
lean_dec_ref(v_lose_446_);
v_a_451_ = lean_ctor_get(v_x_449_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_449_);
if (v_isSharedCheck_459_ == 0)
{
v___x_453_ = v_x_449_;
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v_x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
else
{
lean_object* v_a_460_; uint8_t v___x_461_; 
v_a_460_ = lean_ctor_get(v_x_449_, 0);
lean_inc(v_a_460_);
lean_dec_ref(v_x_449_);
v___x_461_ = lean_unbox(v_a_460_);
lean_dec(v_a_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_dec_ref(v___f_448_);
lean_inc(v___y_447_);
v___x_462_ = lean_apply_2(v_lose_446_, v___y_447_, lean_box(0));
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v_lose_446_);
v___x_463_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v___y_447_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = 0;
v___x_466_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_464_, v___x_465_, v___x_463_, v___f_448_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed(lean_object* v_lose_467_, lean_object* v___y_468_, lean_object* v___f_469_, lean_object* v_x_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(v_lose_467_, v___y_468_, v___f_469_, v_x_470_);
lean_dec(v___y_468_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(lean_object* v_w_473_, lean_object* v_lose_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_finished_477_; lean_object* v_promise_478_; lean_object* v___x_479_; lean_object* v___f_480_; lean_object* v___f_481_; uint8_t v___y_483_; uint8_t v___x_493_; 
v_finished_477_ = lean_ctor_get(v_w_473_, 0);
lean_inc(v_finished_477_);
v_promise_478_ = lean_ctor_get(v_w_473_, 1);
lean_inc(v_promise_478_);
lean_dec_ref(v_w_473_);
v___x_479_ = lean_st_ref_take(v_finished_477_);
v___f_480_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_480_, 0, v_promise_478_);
lean_inc(v___y_475_);
v___f_481_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed), 5, 3);
lean_closure_set(v___f_481_, 0, v_lose_474_);
lean_closure_set(v___f_481_, 1, v___y_475_);
lean_closure_set(v___f_481_, 2, v___f_480_);
v___x_493_ = lean_unbox(v___x_479_);
lean_dec(v___x_479_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = 1;
v___y_483_ = v___x_494_;
goto v___jp_482_;
}
else
{
uint8_t v___x_495_; 
v___x_495_ = 0;
v___y_483_ = v___x_495_;
goto v___jp_482_;
}
v___jp_482_:
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; 
v___x_484_ = 1;
v___x_485_ = lean_box(v___x_484_);
v___x_486_ = lean_st_ref_set(v_finished_477_, v___x_485_);
lean_dec(v_finished_477_);
v___x_487_ = lean_box(v___y_483_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = 0;
v___x_492_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_490_, v___x_491_, v___x_489_, v___f_481_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed(lean_object* v_w_496_, lean_object* v_lose_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(v_w_496_, v_lose_497_, v___y_498_);
lean_dec(v___y_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0(lean_object* v___x_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_501_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0___boxed(lean_object* v___x_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Http_Body_Full_recvSelector___lam__0(v___x_506_, v___y_507_);
lean_dec(v___y_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1(lean_object* v_full_512_, lean_object* v_waiter_513_){
_start:
{
lean_object* v_lose_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_lose_515_ = ((lean_object*)(l_Std_Http_Body_Full_recvSelector___lam__1___closed__0));
v___x_516_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed), 4, 2);
lean_closure_set(v___x_516_, 0, v_waiter_513_);
lean_closure_set(v___x_516_, 1, v_lose_515_);
v___x_517_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_full_512_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1___boxed(lean_object* v_full_518_, lean_object* v_waiter_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_Http_Body_Full_recvSelector___lam__1(v_full_518_, v_waiter_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3(lean_object* v_full_522_, lean_object* v___x_523_, lean_object* v___f_524_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; 
v___x_526_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_full_522_, v___x_523_);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = 0;
v___x_529_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_527_, v___x_528_, v___x_526_, v___f_524_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3___boxed(lean_object* v_full_530_, lean_object* v___x_531_, lean_object* v___f_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Http_Body_Full_recvSelector___lam__3(v_full_530_, v___x_531_, v___f_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2(lean_object* v___x_535_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2___boxed(lean_object* v___x_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Http_Body_Full_recvSelector___lam__2(v___x_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector(lean_object* v_full_544_){
_start:
{
lean_object* v___f_545_; lean_object* v___f_546_; lean_object* v___x_547_; lean_object* v___f_548_; lean_object* v___f_549_; lean_object* v___x_550_; 
lean_inc_ref(v_full_544_);
v___f_545_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_545_, 0, v_full_544_);
v___f_546_ = ((lean_object*)(l_Std_Http_Body_Full_tryRecv___closed__0));
v___x_547_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 2, 0);
v___f_548_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_recvSelector___lam__3___boxed), 4, 3);
lean_closure_set(v___f_548_, 0, v_full_544_);
lean_closure_set(v___f_548_, 1, v___x_547_);
lean_closure_set(v___f_548_, 2, v___f_546_);
v___f_549_ = ((lean_object*)(l_Std_Http_Body_Full_recvSelector___closed__0));
v___x_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_550_, 0, v___f_548_);
lean_ctor_set(v___x_550_, 1, v___f_545_);
lean_ctor_set(v___x_550_, 2, v___f_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instFull___lam__0(lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l_Std_Http_Body_instFull___lam__0___closed__1));
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instFull___lam__0___boxed(lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Http_Body_instFull___lam__0(v_x_559_, v_x_560_);
lean_dec(v_x_560_);
lean_dec_ref(v_x_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseFullAny___lam__0(lean_object* v___x_582_, lean_object* v_f_583_){
_start:
{
lean_object* v_line_584_; lean_object* v_body_585_; lean_object* v_extensions_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
v_line_584_ = lean_ctor_get(v_f_583_, 0);
v_body_585_ = lean_ctor_get(v_f_583_, 1);
v_extensions_586_ = lean_ctor_get(v_f_583_, 2);
v_isSharedCheck_594_ = !lean_is_exclusive(v_f_583_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v_f_583_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_extensions_586_);
lean_inc(v_body_585_);
lean_inc(v_line_584_);
lean_dec(v_f_583_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_582_, v_body_585_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_line_584_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_extensions_586_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(lean_object* v___x_598_, lean_object* v_x_599_){
_start:
{
if (lean_obj_tag(v_x_599_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v___x_598_);
v_a_601_ = lean_ctor_get(v_x_599_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_599_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v_x_599_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v_x_599_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; 
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_629_; 
v_a_610_ = lean_ctor_get(v_x_599_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_x_599_);
if (v_isSharedCheck_629_ == 0)
{
v___x_612_ = v_x_599_;
v_isShared_613_ = v_isSharedCheck_629_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v_x_599_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_629_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_line_614_; lean_object* v_body_615_; lean_object* v_extensions_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
v_line_614_ = lean_ctor_get(v_a_610_, 0);
v_body_615_ = lean_ctor_get(v_a_610_, 1);
v_extensions_616_ = lean_ctor_get(v_a_610_, 2);
v_isSharedCheck_628_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_628_ == 0)
{
v___x_618_ = v_a_610_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_extensions_616_);
lean_inc(v_body_615_);
lean_inc(v_line_614_);
lean_dec(v_a_610_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_598_, v_body_615_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_620_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_line_614_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_extensions_616_);
v___x_622_ = v_reuseFailAlloc_627_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_622_);
v___x_624_ = v___x_612_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_626_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; 
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed(lean_object* v___x_630_, lean_object* v_x_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(v___x_630_, v_x_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(lean_object* v___f_634_, lean_object* v_action_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; 
lean_inc_ref(v___y_636_);
v___x_638_ = lean_apply_2(v_action_635_, v___y_636_, lean_box(0));
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = 0;
v___x_641_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_639_, v___x_640_, v___x_638_, v___f_634_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1___boxed(lean_object* v___f_642_, lean_object* v_action_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(v___f_642_, v_action_643_, v___y_644_);
lean_dec_ref(v___y_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(lean_object* v___f_652_, lean_object* v_action_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_apply_1(v_action_653_, lean_box(0));
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = 0;
v___x_659_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_657_, v___x_658_, v___x_656_, v___f_652_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1___boxed(lean_object* v___f_660_, lean_object* v_action_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(v___f_660_, v_action_661_, v___y_662_);
lean_dec_ref(v___y_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0(lean_object* v_builder_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_a_671_ = lean_ctor_get(v_x_669_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v_x_669_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v_x_669_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v_x_669_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_678_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_689_; 
v_a_680_ = lean_ctor_get(v_x_669_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_669_);
if (v_isSharedCheck_689_ == 0)
{
v___x_682_ = v_x_669_;
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v_x_669_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = l_Std_Http_Request_Builder_body___redArg(v_builder_668_, v_a_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_688_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; 
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0___boxed(lean_object* v_builder_690_, lean_object* v_x_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Http_Request_Builder_fromBytes___lam__0(v_builder_690_, v_x_691_);
lean_dec_ref(v_builder_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes(lean_object* v_builder_694_, lean_object* v_content_695_){
_start:
{
lean_object* v___x_697_; lean_object* v___f_698_; lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; 
v___x_697_ = l_Std_Http_Body_Full_ofByteArray(v_content_695_);
v___f_698_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_698_, 0, v_builder_694_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = 0;
v___x_701_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_699_, v___x_700_, v___x_697_, v___f_698_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___boxed(lean_object* v_builder_702_, lean_object* v_content_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_Http_Request_Builder_fromBytes(v_builder_702_, v_content_703_);
return v_res_705_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_bytes___closed__1(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_Std_Http_Request_Builder_bytes___closed__0));
v___x_708_ = l_Std_Http_Header_Value_ofString_x21(v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_bytes(lean_object* v_builder_709_, lean_object* v_content_710_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = l_Std_Http_Header_Name_contentType;
v___x_713_ = lean_obj_once(&l_Std_Http_Request_Builder_bytes___closed__1, &l_Std_Http_Request_Builder_bytes___closed__1_once, _init_l_Std_Http_Request_Builder_bytes___closed__1);
v___x_714_ = l_Std_Http_Request_Builder_header(v_builder_709_, v___x_712_, v___x_713_);
v___x_715_ = l_Std_Http_Request_Builder_fromBytes(v___x_714_, v_content_710_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_bytes___boxed(lean_object* v_builder_716_, lean_object* v_content_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_Http_Request_Builder_bytes(v_builder_716_, v_content_717_);
return v_res_719_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_text___closed__1(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(l_Std_Http_Request_Builder_text___closed__0));
v___x_722_ = l_Std_Http_Header_Value_ofString_x21(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_text(lean_object* v_builder_723_, lean_object* v_content_724_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_726_ = l_Std_Http_Header_Name_contentType;
v___x_727_ = lean_obj_once(&l_Std_Http_Request_Builder_text___closed__1, &l_Std_Http_Request_Builder_text___closed__1_once, _init_l_Std_Http_Request_Builder_text___closed__1);
v___x_728_ = l_Std_Http_Request_Builder_header(v_builder_723_, v___x_726_, v___x_727_);
v___x_729_ = lean_string_to_utf8(v_content_724_);
v___x_730_ = l_Std_Http_Request_Builder_fromBytes(v___x_728_, v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_text___boxed(lean_object* v_builder_731_, lean_object* v_content_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_Http_Request_Builder_text(v_builder_731_, v_content_732_);
lean_dec_ref(v_content_732_);
return v_res_734_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_json___closed__1(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l_Std_Http_Request_Builder_json___closed__0));
v___x_737_ = l_Std_Http_Header_Value_ofString_x21(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_json(lean_object* v_builder_738_, lean_object* v_content_739_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_741_ = l_Std_Http_Header_Name_contentType;
v___x_742_ = lean_obj_once(&l_Std_Http_Request_Builder_json___closed__1, &l_Std_Http_Request_Builder_json___closed__1_once, _init_l_Std_Http_Request_Builder_json___closed__1);
v___x_743_ = l_Std_Http_Request_Builder_header(v_builder_738_, v___x_741_, v___x_742_);
v___x_744_ = lean_string_to_utf8(v_content_739_);
v___x_745_ = l_Std_Http_Request_Builder_fromBytes(v___x_743_, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_json___boxed(lean_object* v_builder_746_, lean_object* v_content_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_Http_Request_Builder_json(v_builder_746_, v_content_747_);
lean_dec_ref(v_content_747_);
return v_res_749_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_html___closed__1(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Std_Http_Request_Builder_html___closed__0));
v___x_752_ = l_Std_Http_Header_Value_ofString_x21(v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_html(lean_object* v_builder_753_, lean_object* v_content_754_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_756_ = l_Std_Http_Header_Name_contentType;
v___x_757_ = lean_obj_once(&l_Std_Http_Request_Builder_html___closed__1, &l_Std_Http_Request_Builder_html___closed__1_once, _init_l_Std_Http_Request_Builder_html___closed__1);
v___x_758_ = l_Std_Http_Request_Builder_header(v_builder_753_, v___x_756_, v___x_757_);
v___x_759_ = lean_string_to_utf8(v_content_754_);
v___x_760_ = l_Std_Http_Request_Builder_fromBytes(v___x_758_, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_html___boxed(lean_object* v_builder_761_, lean_object* v_content_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_Http_Request_Builder_html(v_builder_761_, v_content_762_);
lean_dec_ref(v_content_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0(lean_object* v_builder_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_776_; 
v_a_768_ = lean_ctor_get(v_x_766_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_776_ == 0)
{
v___x_770_ = v_x_766_;
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v_x_766_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_775_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_786_; 
v_a_777_ = lean_ctor_get(v_x_766_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_786_ == 0)
{
v___x_779_ = v_x_766_;
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v_x_766_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = l_Std_Http_Response_Builder_body___redArg(v_builder_765_, v_a_777_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_781_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_785_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; 
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0___boxed(lean_object* v_builder_787_, lean_object* v_x_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_Http_Response_Builder_fromBytes___lam__0(v_builder_787_, v_x_788_);
lean_dec_ref(v_builder_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes(lean_object* v_builder_791_, lean_object* v_content_792_){
_start:
{
lean_object* v___x_794_; lean_object* v___f_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; 
v___x_794_ = l_Std_Http_Body_Full_ofByteArray(v_content_792_);
v___f_795_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_795_, 0, v_builder_791_);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = 0;
v___x_798_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_796_, v___x_797_, v___x_794_, v___f_795_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___boxed(lean_object* v_builder_799_, lean_object* v_content_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_Http_Response_Builder_fromBytes(v_builder_799_, v_content_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_bytes(lean_object* v_builder_803_, lean_object* v_content_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_806_ = l_Std_Http_Header_Name_contentType;
v___x_807_ = lean_obj_once(&l_Std_Http_Request_Builder_bytes___closed__1, &l_Std_Http_Request_Builder_bytes___closed__1_once, _init_l_Std_Http_Request_Builder_bytes___closed__1);
v___x_808_ = l_Std_Http_Response_Builder_header(v_builder_803_, v___x_806_, v___x_807_);
v___x_809_ = l_Std_Http_Response_Builder_fromBytes(v___x_808_, v_content_804_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_bytes___boxed(lean_object* v_builder_810_, lean_object* v_content_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_Http_Response_Builder_bytes(v_builder_810_, v_content_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_text(lean_object* v_builder_814_, lean_object* v_content_815_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_817_ = l_Std_Http_Header_Name_contentType;
v___x_818_ = lean_obj_once(&l_Std_Http_Request_Builder_text___closed__1, &l_Std_Http_Request_Builder_text___closed__1_once, _init_l_Std_Http_Request_Builder_text___closed__1);
v___x_819_ = l_Std_Http_Response_Builder_header(v_builder_814_, v___x_817_, v___x_818_);
v___x_820_ = lean_string_to_utf8(v_content_815_);
v___x_821_ = l_Std_Http_Response_Builder_fromBytes(v___x_819_, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_text___boxed(lean_object* v_builder_822_, lean_object* v_content_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_Http_Response_Builder_text(v_builder_822_, v_content_823_);
lean_dec_ref(v_content_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_json(lean_object* v_builder_826_, lean_object* v_content_827_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_829_ = l_Std_Http_Header_Name_contentType;
v___x_830_ = lean_obj_once(&l_Std_Http_Request_Builder_json___closed__1, &l_Std_Http_Request_Builder_json___closed__1_once, _init_l_Std_Http_Request_Builder_json___closed__1);
v___x_831_ = l_Std_Http_Response_Builder_header(v_builder_826_, v___x_829_, v___x_830_);
v___x_832_ = lean_string_to_utf8(v_content_827_);
v___x_833_ = l_Std_Http_Response_Builder_fromBytes(v___x_831_, v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_json___boxed(lean_object* v_builder_834_, lean_object* v_content_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_Http_Response_Builder_json(v_builder_834_, v_content_835_);
lean_dec_ref(v_content_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_html(lean_object* v_builder_838_, lean_object* v_content_839_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_841_ = l_Std_Http_Header_Name_contentType;
v___x_842_ = lean_obj_once(&l_Std_Http_Request_Builder_html___closed__1, &l_Std_Http_Request_Builder_html___closed__1_once, _init_l_Std_Http_Request_Builder_html___closed__1);
v___x_843_ = l_Std_Http_Response_Builder_header(v_builder_838_, v___x_841_, v___x_842_);
v___x_844_ = lean_string_to_utf8(v_content_839_);
v___x_845_ = l_Std_Http_Response_Builder_fromBytes(v___x_843_, v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_html___boxed(lean_object* v_builder_846_, lean_object* v_content_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_Http_Response_Builder_html(v_builder_846_, v_content_847_);
lean_dec_ref(v_content_847_);
return v_res_849_;
}
}
lean_object* runtime_initialize_Std_Sync(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Any(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Full(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Body_Full(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Body_Any(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Body_Full(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Full(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Body_Full(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Body_Full(builtin);
}
#ifdef __cplusplus
}
#endif

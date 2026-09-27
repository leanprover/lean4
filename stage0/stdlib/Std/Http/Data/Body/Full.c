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
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* l_Std_Http_Chunk_ofByteArray(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentType;
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Http_Request_Builder_header(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofReplayableBody(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofReplayableBody___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_header(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState = (const lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_close___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_close___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))} };
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_recvSelector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_recvSelector___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Full_recvSelector___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_recvSelector___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_recvSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_recvSelector___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Full_recvSelector___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_recvSelector___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector(lean_object*);
static const lean_closure_object l_Std_Http_Body_Full_resetInPlace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_close___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Full_resetInPlace___closed__0 = (const lean_object*)&l_Std_Http_Body_Full_resetInPlace___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_resetInPlace(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_resetInPlace___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Body_instReplayableFull___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Full_resetInPlace___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instReplayableFull___closed__0 = (const lean_object*)&l_Std_Http_Body_instReplayableFull___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instReplayableFull = (const lean_object*)&l_Std_Http_Body_instReplayableFull___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instCoeFullAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Any_ofReplayableBody, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instFull___closed__7_value),((lean_object*)&l_Std_Http_Body_instReplayableFull___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeFullAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeFullAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeFullAny = (const lean_object*)&l_Std_Http_Body_instCoeFullAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseFullAny___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeResponseFullAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeResponseFullAny___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_instFull___closed__7_value),((lean_object*)&l_Std_Http_Body_instReplayableFull___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeResponseFullAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeResponseFullAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeResponseFullAny = (const lean_object*)&l_Std_Http_Body_instCoeResponseFullAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_instFull___closed__7_value),((lean_object*)&l_Std_Http_Body_instReplayableFull___closed__0_value)} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg(lean_object* v_ready_23_){
_start:
{
lean_inc(v_ready_23_);
return v_ready_23_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg___boxed(lean_object* v_ready_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg(v_ready_24_);
lean_dec(v_ready_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_ready_29_){
_start:
{
lean_inc(v_ready_29_);
return v_ready_29_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_ready_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_ready_33_);
lean_dec(v_ready_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg(lean_object* v_sent_36_){
_start:
{
lean_inc(v_sent_36_);
return v_sent_36_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg___boxed(lean_object* v_sent_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg(v_sent_37_);
lean_dec(v_sent_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_sent_42_){
_start:
{
lean_inc(v_sent_42_);
return v_sent_42_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_sent_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_sent_46_);
lean_dec(v_sent_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg(lean_object* v_closed_49_){
_start:
{
lean_inc(v_closed_49_);
return v_closed_49_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg___boxed(lean_object* v_closed_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg(v_closed_50_);
lean_dec(v_closed_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_closed_55_){
_start:
{
lean_inc(v_closed_55_);
return v_closed_55_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_closed_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_closed_59_);
lean_dec(v_closed_59_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(uint8_t v_x_62_, uint8_t v_y_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx(v_x_62_);
v___x_65_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx(v_y_63_);
v___x_66_ = lean_nat_dec_eq(v___x_64_, v___x_65_);
lean_dec(v___x_65_);
lean_dec(v___x_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq___boxed(lean_object* v_x_67_, lean_object* v_y_68_){
_start:
{
uint8_t v_x_21__boxed_69_; uint8_t v_y_22__boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_x_21__boxed_69_ = lean_unbox(v_x_67_);
v_y_22__boxed_70_ = lean_unbox(v_y_68_);
v_res_71_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(v_x_21__boxed_69_, v_y_22__boxed_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(lean_object* v_full_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
lean_dec_ref(v_full_79_);
v_a_82_ = lean_ctor_get(v_x_80_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_90_ == 0)
{
v___x_84_ = v_x_80_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v_x_80_);
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
lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_103_; 
v_isSharedCheck_103_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; 
v_unused_104_ = lean_ctor_get(v_x_80_, 0);
lean_dec(v_unused_104_);
v___x_92_ = v_x_80_;
v_isShared_93_ = v_isSharedCheck_103_;
goto v_resetjp_91_;
}
else
{
lean_dec(v_x_80_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_103_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v_data_94_; uint8_t v___x_95_; 
v_data_94_ = lean_ctor_get(v_full_79_, 0);
lean_inc_ref(v_data_94_);
lean_dec_ref(v_full_79_);
v___x_95_ = l_ByteArray_isEmpty(v_data_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_96_ = l_Std_Http_Chunk_ofByteArray(v_data_94_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_97_);
v___x_99_ = v___x_92_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_101_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
else
{
lean_object* v___x_102_; 
lean_dec_ref(v_data_94_);
lean_del_object(v___x_92_);
v___x_102_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1));
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed(lean_object* v_full_105_, lean_object* v_x_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(v_full_105_, v_x_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(lean_object* v_a_113_, lean_object* v___f_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v___f_114_);
v_a_119_ = lean_ctor_get(v_x_115_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_x_115_);
if (v_isSharedCheck_127_ == 0)
{
v___x_121_ = v_x_115_;
v_isShared_122_ = v_isSharedCheck_127_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v_x_115_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_127_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_126_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; 
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
}
else
{
lean_object* v_a_128_; uint8_t v___x_129_; 
v_a_128_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v_x_115_, 1);
v___x_129_ = lean_unbox(v_a_128_);
lean_dec(v_a_128_);
if (v___x_129_ == 0)
{
uint8_t v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_130_ = 1;
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = 0;
v___x_133_ = lean_box(v___x_130_);
v___x_134_ = lean_st_ref_swap(v_a_113_, v___x_133_);
lean_dec(v___x_134_);
v___x_135_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1));
v___x_136_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_131_, v___x_132_, v___x_135_, v___f_114_);
return v___x_136_;
}
else
{
lean_dec_ref(v___f_114_);
goto v___jp_117_;
}
}
v___jp_117_:
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1));
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed(lean_object* v_a_137_, lean_object* v___f_138_, lean_object* v_x_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(v_a_137_, v___f_138_, v_x_139_);
lean_dec(v_a_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(lean_object* v_full_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___f_145_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed), 3, 1);
lean_closure_set(v___f_145_, 0, v_full_142_);
lean_inc(v_a_143_);
v___f_146_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed), 4, 2);
lean_closure_set(v___f_146_, 0, v_a_143_);
lean_closure_set(v___f_146_, 1, v___f_145_);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = 0;
v___x_149_ = lean_st_ref_get(v_a_143_);
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
v___x_152_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_147_, v___x_148_, v___x_151_, v___f_146_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed(lean_object* v_full_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v_full_153_, v_a_154_);
lean_dec(v_a_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0(lean_object* v_data_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
lean_dec_ref(v_data_157_);
v_a_160_ = lean_ctor_get(v_x_158_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v_x_158_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v_x_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; 
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_178_; 
v_a_169_ = lean_ctor_get(v_x_158_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_178_ == 0)
{
v___x_171_ = v_x_158_;
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v_x_158_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v_data_157_);
lean_ctor_set(v___x_173_, 1, v_a_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_173_);
v___x_175_ = v___x_171_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_177_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0___boxed(lean_object* v_data_179_, lean_object* v_x_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Http_Body_Full_ofByteArray___lam__0(v_data_179_, v_x_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray(lean_object* v_data_183_){
_start:
{
lean_object* v___f_185_; uint8_t v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___f_185_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_ofByteArray___lam__0___boxed), 3, 1);
lean_closure_set(v___f_185_, 0, v_data_183_);
v___x_186_ = 0;
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = 0;
v___x_189_ = lean_box(v___x_186_);
v___x_190_ = l_Std_Mutex_new___redArg(v___x_189_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
v___x_193_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_187_, v___x_188_, v___x_192_, v___f_185_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___boxed(lean_object* v_data_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_Http_Body_Full_ofByteArray(v_data_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___lam__0(lean_object* v_data_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
v_a_200_ = lean_ctor_get(v_x_198_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v_x_198_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v_x_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_219_; 
v_a_209_ = lean_ctor_get(v_x_198_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_219_ == 0)
{
v___x_211_ = v_x_198_;
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v_x_198_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_213_ = lean_string_to_utf8(v_data_197_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v_a_209_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_214_);
v___x_216_ = v___x_211_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_218_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___lam__0___boxed(lean_object* v_data_220_, lean_object* v_x_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_Http_Body_Full_ofString___lam__0(v_data_220_, v_x_221_);
lean_dec_ref(v_data_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString(lean_object* v_data_224_){
_start:
{
lean_object* v___f_226_; uint8_t v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___f_226_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_ofString___lam__0___boxed), 3, 1);
lean_closure_set(v___f_226_, 0, v_data_224_);
v___x_227_ = 0;
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = 0;
v___x_230_ = lean_box(v___x_227_);
v___x_231_ = l_Std_Mutex_new___redArg(v___x_230_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___x_234_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_228_, v___x_229_, v___x_233_, v___f_226_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___boxed(lean_object* v_data_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Http_Body_Full_ofString(v_data_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0(lean_object* v___y_238_){
_start:
{
if (lean_obj_tag(v___y_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v___y_238_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___y_238_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___y_238_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___y_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
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
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_255_; 
v_a_247_ = lean_ctor_get(v___y_238_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___y_238_);
if (v_isSharedCheck_255_ == 0)
{
v___x_249_ = v___y_238_;
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___y_238_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_fst_251_; lean_object* v___x_253_; 
v_fst_251_ = lean_ctor_get(v_a_247_, 0);
lean_inc(v_fst_251_);
lean_dec(v_a_247_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v_fst_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_fst_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(lean_object* v_mutex_256_, lean_object* v_x_257_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_io_basemutex_unlock(v_mutex_256_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed(lean_object* v_mutex_262_, lean_object* v_x_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(v_mutex_262_, v_x_263_);
lean_dec(v_x_263_);
lean_dec(v_mutex_262_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(lean_object* v_k_266_, lean_object* v_ref_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
lean_dec(v_ref_267_);
lean_dec_ref(v_k_266_);
v_a_270_ = lean_ctor_get(v_x_268_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_278_ == 0)
{
v___x_272_ = v_x_268_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v_x_268_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_277_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
}
else
{
lean_object* v___x_279_; 
lean_dec_ref_known(v_x_268_, 1);
v___x_279_ = lean_apply_2(v_k_266_, v_ref_267_, lean_box(0));
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed(lean_object* v_k_280_, lean_object* v_ref_281_, lean_object* v_x_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(v_k_280_, v_ref_281_, v_x_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(lean_object* v_mutex_285_, lean_object* v___f_286_){
_start:
{
lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = 0;
v___x_290_ = lean_io_basemutex_lock(v_mutex_285_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_288_, v___x_289_, v___x_292_, v___f_286_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3___boxed(lean_object* v_mutex_294_, lean_object* v___f_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(v_mutex_294_, v___f_295_);
lean_dec(v_mutex_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(lean_object* v_mutex_299_, lean_object* v_k_300_){
_start:
{
lean_object* v_ref_302_; lean_object* v_mutex_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___f_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___y_312_; 
v_ref_302_ = lean_ctor_get(v_mutex_299_, 0);
lean_inc(v_ref_302_);
v_mutex_303_ = lean_ctor_get(v_mutex_299_, 1);
lean_inc_n(v_mutex_303_, 2);
lean_dec_ref(v_mutex_299_);
v___f_304_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0));
v___f_305_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_305_, 0, v_mutex_303_);
v___f_306_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_306_, 0, v_k_300_);
lean_closure_set(v___f_306_, 1, v_ref_302_);
v___f_307_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_307_, 0, v_mutex_303_);
lean_closure_set(v___f_307_, 1, v___f_306_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = 0;
v___x_310_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_307_, v___f_305_, v___x_308_, v___x_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_314_; 
v_a_314_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_310_, 1);
if (lean_obj_tag(v_a_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_a_315_ = lean_ctor_get(v_a_314_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_a_314_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v_a_314_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v_a_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
v___y_312_ = v___x_320_;
goto v___jp_311_;
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
v_a_323_ = lean_ctor_get(v_a_314_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_314_);
if (v_isSharedCheck_331_ == 0)
{
v___x_325_ = v_a_314_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v_a_314_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_fst_327_; lean_object* v___x_329_; 
v_fst_327_ = lean_ctor_get(v_a_323_, 0);
lean_inc(v_fst_327_);
lean_dec(v_a_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v_fst_327_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_fst_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
v___y_312_ = v___x_329_;
goto v___jp_311_;
}
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
v_a_332_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_340_ == 0)
{
v___x_334_ = v___x_310_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_310_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_task_map(v___f_304_, v_a_332_, v___x_308_, v___x_309_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
v___jp_311_:
{
lean_object* v___x_313_; 
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___y_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___boxed(lean_object* v_mutex_341_, lean_object* v_k_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_mutex_341_, v_k_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_mutex_347_, lean_object* v_k_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_mutex_347_, v_k_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___boxed(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_mutex_353_, lean_object* v_k_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(v_00_u03b1_351_, v_00_u03b2_352_, v_mutex_353_, v_k_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv(lean_object* v_full_357_){
_start:
{
lean_object* v_state_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_state_359_ = lean_ctor_get(v_full_357_, 1);
lean_inc_ref(v_state_359_);
v___x_360_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 3, 1);
lean_closure_set(v___x_360_, 0, v_full_357_);
v___x_361_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_359_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv___boxed(lean_object* v_full_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_Http_Body_Full_recv(v_full_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0(uint8_t v___x_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_box(v___x_365_);
v___x_369_ = lean_st_ref_swap(v___y_366_, v___x_368_);
lean_dec(v___x_369_);
v___x_370_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1));
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0___boxed(lean_object* v___x_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
uint8_t v___x_177__boxed_374_; lean_object* v_res_375_; 
v___x_177__boxed_374_ = lean_unbox(v___x_371_);
v_res_375_ = l_Std_Http_Body_Full_close___lam__0(v___x_177__boxed_374_, v___y_372_);
lean_dec(v___y_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close(lean_object* v_full_379_){
_start:
{
lean_object* v_state_381_; lean_object* v___f_382_; lean_object* v___x_383_; 
v_state_381_ = lean_ctor_get(v_full_379_, 1);
lean_inc_ref(v_state_381_);
lean_dec_ref(v_full_379_);
v___f_382_ = ((lean_object*)(l_Std_Http_Body_Full_close___closed__0));
v___x_383_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_381_, v___f_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___boxed(lean_object* v_full_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_Http_Body_Full_close(v_full_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__0(lean_object* v_x_387_){
_start:
{
uint8_t v___y_390_; 
if (lean_obj_tag(v_x_387_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_a_394_ = lean_ctor_get(v_x_387_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_x_387_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v_x_387_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v_x_387_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_401_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; 
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
}
else
{
lean_object* v_a_403_; uint8_t v___x_404_; uint8_t v___x_405_; uint8_t v___x_406_; 
v_a_403_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v_x_387_, 1);
v___x_404_ = 0;
v___x_405_ = lean_unbox(v_a_403_);
lean_dec(v_a_403_);
v___x_406_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(v___x_405_, v___x_404_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 1;
v___y_390_ = v___x_407_;
goto v___jp_389_;
}
else
{
uint8_t v___x_408_; 
v___x_408_ = 0;
v___y_390_ = v___x_408_;
goto v___jp_389_;
}
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_box(v___y_390_);
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__0___boxed(lean_object* v_x_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_Http_Body_Full_isClosed___lam__0(v_x_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__1(lean_object* v___f_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = 0;
v___x_417_ = lean_st_ref_get(v___y_413_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
v___x_420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_415_, v___x_416_, v___x_419_, v___f_412_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__1___boxed(lean_object* v___f_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_Http_Body_Full_isClosed___lam__1(v___f_421_, v___y_422_);
lean_dec(v___y_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed(lean_object* v_full_428_){
_start:
{
lean_object* v_state_430_; lean_object* v___f_431_; lean_object* v___x_432_; 
v_state_430_ = lean_ctor_get(v_full_428_, 1);
lean_inc_ref(v_state_430_);
lean_dec_ref(v_full_428_);
v___f_431_ = ((lean_object*)(l_Std_Http_Body_Full_isClosed___closed__1));
v___x_432_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_430_, v___f_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___boxed(lean_object* v_full_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_Http_Body_Full_isClosed(v_full_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0(lean_object* v_data_444_, lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_a_449_ = lean_ctor_get(v_x_445_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_457_ == 0)
{
v___x_451_ = v_x_445_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v_x_445_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_456_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_470_; 
v_a_458_ = lean_ctor_get(v_x_445_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_470_ == 0)
{
v___x_460_ = v_x_445_;
v_isShared_461_ = v_isSharedCheck_470_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v_x_445_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_470_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
uint8_t v___x_462_; 
v___x_462_ = lean_unbox(v_a_458_);
lean_dec(v_a_458_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_463_ = lean_byte_array_size(v_data_444_);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_465_);
v___x_467_ = v___x_460_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_469_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; 
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
else
{
lean_del_object(v___x_460_);
goto v___jp_447_;
}
}
}
v___jp_447_:
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3));
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___boxed(lean_object* v_data_471_, lean_object* v_x_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_Http_Body_Full_getKnownSize___lam__0(v_data_471_, v_x_472_);
lean_dec_ref(v_data_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1(lean_object* v___f_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = 0;
v___x_480_ = lean_st_ref_get(v___y_476_);
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___x_483_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_478_, v___x_479_, v___x_482_, v___f_475_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1___boxed(lean_object* v___f_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_Http_Body_Full_getKnownSize___lam__1(v___f_484_, v___y_485_);
lean_dec(v___y_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize(lean_object* v_full_488_){
_start:
{
lean_object* v_data_490_; lean_object* v_state_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___x_494_; 
v_data_490_ = lean_ctor_get(v_full_488_, 0);
lean_inc_ref(v_data_490_);
v_state_491_ = lean_ctor_get(v_full_488_, 1);
lean_inc_ref(v_state_491_);
lean_dec_ref(v_full_488_);
v___f_492_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_getKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_492_, 0, v_data_490_);
v___f_493_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_getKnownSize___lam__1___boxed), 3, 1);
lean_closure_set(v___f_493_, 0, v___f_492_);
v___x_494_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_491_, v___f_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___boxed(lean_object* v_full_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Http_Body_Full_getKnownSize(v_full_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___lam__0(lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_a_500_ = lean_ctor_get(v_x_498_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v_x_498_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v_x_498_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v_x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_507_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; 
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_518_; 
v_a_509_ = lean_ctor_get(v_x_498_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_498_);
if (v_isSharedCheck_518_ == 0)
{
v___x_511_ = v_x_498_;
v_isShared_512_ = v_isSharedCheck_518_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v_x_498_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_518_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v_a_509_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_513_);
v___x_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_517_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___lam__0___boxed(lean_object* v_x_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_Http_Body_Full_tryRecv___lam__0(v_x_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv(lean_object* v_full_523_){
_start:
{
lean_object* v_state_525_; lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_state_525_ = lean_ctor_get(v_full_523_, 1);
lean_inc_ref(v_state_525_);
v___f_526_ = ((lean_object*)(l_Std_Http_Body_Full_tryRecv___closed__0));
v___x_527_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 3, 1);
lean_closure_set(v___x_527_, 0, v_full_523_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = 0;
v___x_530_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_525_, v___x_527_);
v___x_531_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_528_, v___x_529_, v___x_530_, v___f_526_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___boxed(lean_object* v_full_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Http_Body_Full_tryRecv(v_full_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(lean_object* v_promise_535_, lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
v_a_538_ = lean_ctor_get(v_x_536_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_546_ == 0)
{
v___x_540_ = v_x_536_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v_x_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_io_promise_resolve(v_x_536_, v_promise_535_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed(lean_object* v_promise_550_, lean_object* v_x_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(v_promise_550_, v_x_551_);
lean_dec(v_promise_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(lean_object* v_lose_554_, lean_object* v___y_555_, lean_object* v_full_556_, lean_object* v___f_557_, lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_568_; 
lean_dec_ref(v___f_557_);
lean_dec_ref(v_full_556_);
lean_dec_ref(v_lose_554_);
v_a_560_ = lean_ctor_get(v_x_558_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_568_ == 0)
{
v___x_562_ = v_x_558_;
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v_x_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_567_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; 
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
}
else
{
lean_object* v_a_569_; uint8_t v___x_570_; 
v_a_569_ = lean_ctor_get(v_x_558_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v_x_558_, 1);
v___x_570_ = lean_unbox(v_a_569_);
lean_dec(v_a_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec_ref(v___f_557_);
lean_dec_ref(v_full_556_);
lean_inc(v___y_555_);
v___x_571_ = lean_apply_2(v_lose_554_, v___y_555_, lean_box(0));
return v___x_571_;
}
else
{
lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec_ref(v_lose_554_);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = 0;
v___x_574_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v_full_556_, v___y_555_);
v___x_575_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_572_, v___x_573_, v___x_574_, v___f_557_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed(lean_object* v_lose_576_, lean_object* v___y_577_, lean_object* v_full_578_, lean_object* v___f_579_, lean_object* v_x_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(v_lose_576_, v___y_577_, v_full_578_, v___f_579_, v_x_580_);
lean_dec(v___y_577_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(lean_object* v_full_583_, lean_object* v_w_584_, lean_object* v_lose_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_finished_588_; lean_object* v_promise_589_; lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___x_592_; uint8_t v___x_593_; lean_object* v___x_594_; uint8_t v___y_596_; uint8_t v___x_604_; 
v_finished_588_ = lean_ctor_get(v_w_584_, 0);
lean_inc(v_finished_588_);
v_promise_589_ = lean_ctor_get(v_w_584_, 1);
lean_inc(v_promise_589_);
lean_dec_ref(v_w_584_);
v___f_590_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_590_, 0, v_promise_589_);
lean_inc(v___y_586_);
v___f_591_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed), 6, 4);
lean_closure_set(v___f_591_, 0, v_lose_585_);
lean_closure_set(v___f_591_, 1, v___y_586_);
lean_closure_set(v___f_591_, 2, v_full_583_);
lean_closure_set(v___f_591_, 3, v___f_590_);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = 0;
v___x_594_ = lean_st_ref_take(v_finished_588_);
v___x_604_ = lean_unbox(v___x_594_);
lean_dec(v___x_594_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; 
v___x_605_ = 1;
v___y_596_ = v___x_605_;
goto v___jp_595_;
}
else
{
v___y_596_ = v___x_593_;
goto v___jp_595_;
}
v___jp_595_:
{
uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_597_ = 1;
v___x_598_ = lean_box(v___x_597_);
v___x_599_ = lean_st_ref_put(v_finished_588_, v___x_598_);
lean_dec(v_finished_588_);
v___x_600_ = lean_box(v___y_596_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_592_, v___x_593_, v___x_602_, v___f_591_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed(lean_object* v_full_606_, lean_object* v_w_607_, lean_object* v_lose_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(v_full_606_, v_w_607_, v_lose_608_, v___y_609_);
lean_dec(v___y_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1(lean_object* v___x_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_612_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1___boxed(lean_object* v___x_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Http_Body_Full_recvSelector___lam__1(v___x_617_, v___y_618_);
lean_dec(v___y_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0(lean_object* v_full_623_, lean_object* v_state_624_, lean_object* v_waiter_625_){
_start:
{
lean_object* v_lose_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_lose_627_ = ((lean_object*)(l_Std_Http_Body_Full_recvSelector___lam__0___closed__0));
v___x_628_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed), 5, 3);
lean_closure_set(v___x_628_, 0, v_full_623_);
lean_closure_set(v___x_628_, 1, v_waiter_625_);
lean_closure_set(v___x_628_, 2, v_lose_627_);
v___x_629_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_624_, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0___boxed(lean_object* v_full_630_, lean_object* v_state_631_, lean_object* v_waiter_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Http_Body_Full_recvSelector___lam__0(v_full_630_, v_state_631_, v_waiter_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2(lean_object* v_state_635_, lean_object* v___x_636_, lean_object* v___f_637_){
_start:
{
lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = 0;
v___x_641_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_635_, v___x_636_);
v___x_642_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_639_, v___x_640_, v___x_641_, v___f_637_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2___boxed(lean_object* v_state_643_, lean_object* v___x_644_, lean_object* v___f_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Http_Body_Full_recvSelector___lam__2(v_state_643_, v___x_644_, v___f_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3(lean_object* v___x_648_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3___boxed(lean_object* v___x_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Http_Body_Full_recvSelector___lam__3(v___x_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector(lean_object* v_full_657_){
_start:
{
lean_object* v_state_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___f_662_; lean_object* v___f_663_; lean_object* v___x_664_; 
v_state_658_ = lean_ctor_get(v_full_657_, 1);
lean_inc_ref_n(v_state_658_, 2);
v___f_659_ = ((lean_object*)(l_Std_Http_Body_Full_tryRecv___closed__0));
lean_inc_ref(v_full_657_);
v___f_660_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_recvSelector___lam__0___boxed), 4, 2);
lean_closure_set(v___f_660_, 0, v_full_657_);
lean_closure_set(v___f_660_, 1, v_state_658_);
v___x_661_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 3, 1);
lean_closure_set(v___x_661_, 0, v_full_657_);
v___f_662_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_recvSelector___lam__2___boxed), 4, 3);
lean_closure_set(v___f_662_, 0, v_state_658_);
lean_closure_set(v___f_662_, 1, v___x_661_);
lean_closure_set(v___f_662_, 2, v___f_659_);
v___f_663_ = ((lean_object*)(l_Std_Http_Body_Full_recvSelector___closed__0));
v___x_664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_664_, 0, v___f_662_);
lean_ctor_set(v___x_664_, 1, v___f_660_);
lean_ctor_set(v___x_664_, 2, v___f_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_resetInPlace(lean_object* v_full_668_){
_start:
{
lean_object* v_state_670_; lean_object* v___f_671_; lean_object* v___x_672_; 
v_state_670_ = lean_ctor_get(v_full_668_, 1);
lean_inc_ref(v_state_670_);
lean_dec_ref(v_full_668_);
v___f_671_ = ((lean_object*)(l_Std_Http_Body_Full_resetInPlace___closed__0));
v___x_672_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_670_, v___f_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_resetInPlace___boxed(lean_object* v_full_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_Http_Body_Full_resetInPlace(v_full_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instFull___lam__0(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1));
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instFull___lam__0___boxed(lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_Http_Body_instFull___lam__0(v_x_680_, v_x_681_);
lean_dec(v_x_681_);
lean_dec_ref(v_x_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseFullAny___lam__0(lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v_f_708_){
_start:
{
lean_object* v_line_709_; lean_object* v_body_710_; lean_object* v_extensions_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_719_; 
v_line_709_ = lean_ctor_get(v_f_708_, 0);
v_body_710_ = lean_ctor_get(v_f_708_, 1);
v_extensions_711_ = lean_ctor_get(v_f_708_, 2);
v_isSharedCheck_719_ = !lean_is_exclusive(v_f_708_);
if (v_isSharedCheck_719_ == 0)
{
v___x_713_ = v_f_708_;
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_extensions_711_);
lean_inc(v_body_710_);
lean_inc(v_line_709_);
lean_dec(v_f_708_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_706_, v___x_707_, v_body_710_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_line_709_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_extensions_711_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(lean_object* v___x_724_, lean_object* v___x_725_, lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v___x_725_);
lean_dec_ref(v___x_724_);
v_a_728_ = lean_ctor_get(v_x_726_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_736_ == 0)
{
v___x_730_ = v_x_726_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v_x_726_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_735_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_756_; 
v_a_737_ = lean_ctor_get(v_x_726_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_756_ == 0)
{
v___x_739_ = v_x_726_;
v_isShared_740_ = v_isSharedCheck_756_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v_x_726_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_756_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_line_741_; lean_object* v_body_742_; lean_object* v_extensions_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_755_; 
v_line_741_ = lean_ctor_get(v_a_737_, 0);
v_body_742_ = lean_ctor_get(v_a_737_, 1);
v_extensions_743_ = lean_ctor_get(v_a_737_, 2);
v_isSharedCheck_755_ = !lean_is_exclusive(v_a_737_);
if (v_isSharedCheck_755_ == 0)
{
v___x_745_ = v_a_737_;
v_isShared_746_ = v_isSharedCheck_755_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_extensions_743_);
lean_inc(v_body_742_);
lean_inc(v_line_741_);
lean_dec(v_a_737_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_755_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_724_, v___x_725_, v_body_742_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_line_741_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_extensions_743_);
v___x_749_ = v_reuseFailAlloc_754_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_749_);
v___x_751_ = v___x_739_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_753_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; 
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed(lean_object* v___x_757_, lean_object* v___x_758_, lean_object* v_x_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(v___x_757_, v___x_758_, v_x_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(lean_object* v___f_762_, lean_object* v_action_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = 0;
lean_inc_ref(v___y_764_);
v___x_768_ = lean_apply_2(v_action_763_, v___y_764_, lean_box(0));
v___x_769_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_766_, v___x_767_, v___x_768_, v___f_762_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1___boxed(lean_object* v___f_770_, lean_object* v_action_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(v___f_770_, v_action_771_, v___y_772_);
lean_dec_ref(v___y_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(lean_object* v___f_781_, lean_object* v_action_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = 0;
v___x_787_ = lean_apply_1(v_action_782_, lean_box(0));
v___x_788_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_785_, v___x_786_, v___x_787_, v___f_781_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1___boxed(lean_object* v___f_789_, lean_object* v_action_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(v___f_789_, v_action_790_, v___y_791_);
lean_dec_ref(v___y_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0(lean_object* v_builder_797_, lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_a_800_ = lean_ctor_get(v_x_798_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_808_ == 0)
{
v___x_802_ = v_x_798_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v_x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_818_; 
v_a_809_ = lean_ctor_get(v_x_798_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_818_ == 0)
{
v___x_811_ = v_x_798_;
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v_x_798_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = l_Std_Http_Request_Builder_body___redArg(v_builder_797_, v_a_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_817_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; 
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0___boxed(lean_object* v_builder_819_, lean_object* v_x_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_Http_Request_Builder_fromBytes___lam__0(v_builder_819_, v_x_820_);
lean_dec_ref(v_builder_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes(lean_object* v_builder_823_, lean_object* v_content_824_){
_start:
{
lean_object* v___f_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___f_826_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_826_, 0, v_builder_823_);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = 0;
v___x_829_ = l_Std_Http_Body_Full_ofByteArray(v_content_824_);
v___x_830_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_827_, v___x_828_, v___x_829_, v___f_826_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___boxed(lean_object* v_builder_831_, lean_object* v_content_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_Http_Request_Builder_fromBytes(v_builder_831_, v_content_832_);
return v_res_834_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_bytes___closed__1(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Std_Http_Request_Builder_bytes___closed__0));
v___x_837_ = l_Std_Http_Header_Value_ofString_x21(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_bytes(lean_object* v_builder_838_, lean_object* v_content_839_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_841_ = l_Std_Http_Header_Name_contentType;
v___x_842_ = lean_obj_once(&l_Std_Http_Request_Builder_bytes___closed__1, &l_Std_Http_Request_Builder_bytes___closed__1_once, _init_l_Std_Http_Request_Builder_bytes___closed__1);
v___x_843_ = l_Std_Http_Request_Builder_header(v_builder_838_, v___x_841_, v___x_842_);
v___x_844_ = l_Std_Http_Request_Builder_fromBytes(v___x_843_, v_content_839_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_bytes___boxed(lean_object* v_builder_845_, lean_object* v_content_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_Http_Request_Builder_bytes(v_builder_845_, v_content_846_);
return v_res_848_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_text___closed__1(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = ((lean_object*)(l_Std_Http_Request_Builder_text___closed__0));
v___x_851_ = l_Std_Http_Header_Value_ofString_x21(v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_text(lean_object* v_builder_852_, lean_object* v_content_853_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_855_ = l_Std_Http_Header_Name_contentType;
v___x_856_ = lean_obj_once(&l_Std_Http_Request_Builder_text___closed__1, &l_Std_Http_Request_Builder_text___closed__1_once, _init_l_Std_Http_Request_Builder_text___closed__1);
v___x_857_ = l_Std_Http_Request_Builder_header(v_builder_852_, v___x_855_, v___x_856_);
v___x_858_ = lean_string_to_utf8(v_content_853_);
v___x_859_ = l_Std_Http_Request_Builder_fromBytes(v___x_857_, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_text___boxed(lean_object* v_builder_860_, lean_object* v_content_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_Http_Request_Builder_text(v_builder_860_, v_content_861_);
lean_dec_ref(v_content_861_);
return v_res_863_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_json___closed__1(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Std_Http_Request_Builder_json___closed__0));
v___x_866_ = l_Std_Http_Header_Value_ofString_x21(v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_json(lean_object* v_builder_867_, lean_object* v_content_868_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_870_ = l_Std_Http_Header_Name_contentType;
v___x_871_ = lean_obj_once(&l_Std_Http_Request_Builder_json___closed__1, &l_Std_Http_Request_Builder_json___closed__1_once, _init_l_Std_Http_Request_Builder_json___closed__1);
v___x_872_ = l_Std_Http_Request_Builder_header(v_builder_867_, v___x_870_, v___x_871_);
v___x_873_ = lean_string_to_utf8(v_content_868_);
v___x_874_ = l_Std_Http_Request_Builder_fromBytes(v___x_872_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_json___boxed(lean_object* v_builder_875_, lean_object* v_content_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_Http_Request_Builder_json(v_builder_875_, v_content_876_);
lean_dec_ref(v_content_876_);
return v_res_878_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_html___closed__1(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_Std_Http_Request_Builder_html___closed__0));
v___x_881_ = l_Std_Http_Header_Value_ofString_x21(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_html(lean_object* v_builder_882_, lean_object* v_content_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_885_ = l_Std_Http_Header_Name_contentType;
v___x_886_ = lean_obj_once(&l_Std_Http_Request_Builder_html___closed__1, &l_Std_Http_Request_Builder_html___closed__1_once, _init_l_Std_Http_Request_Builder_html___closed__1);
v___x_887_ = l_Std_Http_Request_Builder_header(v_builder_882_, v___x_885_, v___x_886_);
v___x_888_ = lean_string_to_utf8(v_content_883_);
v___x_889_ = l_Std_Http_Request_Builder_fromBytes(v___x_887_, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_html___boxed(lean_object* v_builder_890_, lean_object* v_content_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_Http_Request_Builder_html(v_builder_890_, v_content_891_);
lean_dec_ref(v_content_891_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0(lean_object* v_builder_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_895_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_a_897_ = lean_ctor_get(v_x_895_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v_x_895_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v_x_895_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v_x_895_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_904_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_915_; 
v_a_906_ = lean_ctor_get(v_x_895_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v_x_895_);
if (v_isSharedCheck_915_ == 0)
{
v___x_908_ = v_x_895_;
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v_x_895_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = l_Std_Http_Response_Builder_body___redArg(v_builder_894_, v_a_906_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_914_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0___boxed(lean_object* v_builder_916_, lean_object* v_x_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_Http_Response_Builder_fromBytes___lam__0(v_builder_916_, v_x_917_);
lean_dec_ref(v_builder_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes(lean_object* v_builder_920_, lean_object* v_content_921_){
_start:
{
lean_object* v___f_923_; lean_object* v___x_924_; uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___f_923_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_923_, 0, v_builder_920_);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = 0;
v___x_926_ = l_Std_Http_Body_Full_ofByteArray(v_content_921_);
v___x_927_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_924_, v___x_925_, v___x_926_, v___f_923_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___boxed(lean_object* v_builder_928_, lean_object* v_content_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_Http_Response_Builder_fromBytes(v_builder_928_, v_content_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_bytes(lean_object* v_builder_932_, lean_object* v_content_933_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_935_ = l_Std_Http_Header_Name_contentType;
v___x_936_ = lean_obj_once(&l_Std_Http_Request_Builder_bytes___closed__1, &l_Std_Http_Request_Builder_bytes___closed__1_once, _init_l_Std_Http_Request_Builder_bytes___closed__1);
v___x_937_ = l_Std_Http_Response_Builder_header(v_builder_932_, v___x_935_, v___x_936_);
v___x_938_ = l_Std_Http_Response_Builder_fromBytes(v___x_937_, v_content_933_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_bytes___boxed(lean_object* v_builder_939_, lean_object* v_content_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_Http_Response_Builder_bytes(v_builder_939_, v_content_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_text(lean_object* v_builder_943_, lean_object* v_content_944_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_946_ = l_Std_Http_Header_Name_contentType;
v___x_947_ = lean_obj_once(&l_Std_Http_Request_Builder_text___closed__1, &l_Std_Http_Request_Builder_text___closed__1_once, _init_l_Std_Http_Request_Builder_text___closed__1);
v___x_948_ = l_Std_Http_Response_Builder_header(v_builder_943_, v___x_946_, v___x_947_);
v___x_949_ = lean_string_to_utf8(v_content_944_);
v___x_950_ = l_Std_Http_Response_Builder_fromBytes(v___x_948_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_text___boxed(lean_object* v_builder_951_, lean_object* v_content_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_Http_Response_Builder_text(v_builder_951_, v_content_952_);
lean_dec_ref(v_content_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_json(lean_object* v_builder_955_, lean_object* v_content_956_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_958_ = l_Std_Http_Header_Name_contentType;
v___x_959_ = lean_obj_once(&l_Std_Http_Request_Builder_json___closed__1, &l_Std_Http_Request_Builder_json___closed__1_once, _init_l_Std_Http_Request_Builder_json___closed__1);
v___x_960_ = l_Std_Http_Response_Builder_header(v_builder_955_, v___x_958_, v___x_959_);
v___x_961_ = lean_string_to_utf8(v_content_956_);
v___x_962_ = l_Std_Http_Response_Builder_fromBytes(v___x_960_, v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_json___boxed(lean_object* v_builder_963_, lean_object* v_content_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_Http_Response_Builder_json(v_builder_963_, v_content_964_);
lean_dec_ref(v_content_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_html(lean_object* v_builder_967_, lean_object* v_content_968_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_970_ = l_Std_Http_Header_Name_contentType;
v___x_971_ = lean_obj_once(&l_Std_Http_Request_Builder_html___closed__1, &l_Std_Http_Request_Builder_html___closed__1_once, _init_l_Std_Http_Request_Builder_html___closed__1);
v___x_972_ = l_Std_Http_Response_Builder_header(v_builder_967_, v___x_970_, v___x_971_);
v___x_973_ = lean_string_to_utf8(v_content_968_);
v___x_974_ = l_Std_Http_Response_Builder_fromBytes(v___x_972_, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_html___boxed(lean_object* v_builder_975_, lean_object* v_content_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_Http_Response_Builder_html(v_builder_975_, v_content_976_);
lean_dec_ref(v_content_976_);
return v_res_978_;
}
}
lean_object* runtime_initialize_Std_Sync(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Any(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Full(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

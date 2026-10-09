// Lean compiler output
// Module: Std.Http.Data.Body.Full
// Imports: public import Std.Sync public import Std.Http.Data.Request public import Std.Http.Data.Response public import Std.Http.Data.Body.Any public import Init.Data.ByteArray.Basic
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg(lean_object* v_ready_24_){
_start:
{
lean_inc(v_ready_24_);
return v_ready_24_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg___boxed(lean_object* v_ready_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg(v_ready_25_);
lean_dec(v_ready_25_);
return v_res_26_;
}
}
lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_ready_30_){
_start:
{
lean_inc(v_ready_30_);
return v_ready_30_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_ready_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim(lean_box(0), v_t_28_, lean_box(0), v_ready_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_ready_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_ready_35_);
lean_dec(v_ready_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg(lean_object* v_sent_38_){
_start:
{
lean_inc(v_sent_38_);
return v_sent_38_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg___boxed(lean_object* v_sent_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg(v_sent_39_);
lean_dec(v_sent_39_);
return v_res_40_;
}
}
lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_sent_44_){
_start:
{
lean_inc(v_sent_44_);
return v_sent_44_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_sent_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim(lean_box(0), v_t_42_, lean_box(0), v_sent_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_sent_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_sent_49_);
lean_dec(v_sent_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg(lean_object* v_closed_52_){
_start:
{
lean_inc(v_closed_52_);
return v_closed_52_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg___boxed(lean_object* v_closed_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg(v_closed_53_);
lean_dec(v_closed_53_);
return v_res_54_;
}
}
lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_closed_58_){
_start:
{
lean_inc(v_closed_58_);
return v_closed_58_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_closed_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim(lean_box(0), v_t_56_, lean_box(0), v_closed_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_closed_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_closed_63_);
lean_dec(v_closed_63_);
return v_res_65_;
}
}
uint8_t l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(uint8_t v_x_66_, uint8_t v_y_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_68_ = lean_box(v_x_66_);
v___x_69_ = lean_obj_tag_nat(v___x_68_);
lean_dec(v___x_68_);
v___x_70_ = lean_box(v_y_67_);
v___x_71_ = lean_obj_tag_nat(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_nat_dec_eq(v___x_69_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_66_ = stack[0].m_num;
uint8_t v_y_67_ = stack[1].m_num;
uint8_t v_res_73_;
v_res_73_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(v_x_66_, v_y_67_);
stack->m_num = v_res_73_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq___boxed(lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
uint8_t v_x_24__boxed_76_; uint8_t v_y_25__boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_x_24__boxed_76_ = lean_unbox(v_x_74_);
v_y_25__boxed_77_ = lean_unbox(v_y_75_);
v_res_78_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(v_x_24__boxed_76_, v_y_25__boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(lean_object* v_full_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_97_; 
lean_dec_ref(v_full_86_);
v_a_89_ = lean_ctor_get(v_x_87_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_97_ == 0)
{
v___x_91_ = v_x_87_;
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v_x_87_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_96_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; 
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
}
else
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_110_; 
v_isSharedCheck_110_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; 
v_unused_111_ = lean_ctor_get(v_x_87_, 0);
lean_dec(v_unused_111_);
v___x_99_ = v_x_87_;
v_isShared_100_ = v_isSharedCheck_110_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_x_87_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_110_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_data_101_; uint8_t v___x_102_; 
v_data_101_ = lean_ctor_get(v_full_86_, 0);
lean_inc_ref(v_data_101_);
lean_dec_ref(v_full_86_);
v___x_102_ = l_ByteArray_isEmpty(v_data_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = l_Std_Http_Chunk_ofByteArray(v_data_101_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_104_);
v___x_106_ = v___x_99_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_108_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
else
{
lean_object* v___x_109_; 
lean_dec_ref(v_data_101_);
lean_del_object(v___x_99_);
v___x_109_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1));
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_86_ = stack[0].m_obj;
lean_object* v_x_87_ = stack[1].m_obj;
lean_object* v_res_112_;
v_res_112_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(v_full_86_, v_x_87_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed(lean_object* v_full_113_, lean_object* v_x_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(v_full_113_, v_x_114_);
return v_res_116_;
}
}
lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(lean_object* v_a_121_, lean_object* v___f_122_, lean_object* v_x_123_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_135_; 
lean_dec_ref(v___f_122_);
v_a_127_ = lean_ctor_get(v_x_123_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v_x_123_);
if (v_isSharedCheck_135_ == 0)
{
v___x_129_ = v_x_123_;
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v_x_123_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_134_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; 
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
}
else
{
lean_object* v_a_136_; uint8_t v___x_137_; 
v_a_136_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v_x_123_, 1);
v___x_137_ = lean_unbox(v_a_136_);
lean_dec(v_a_136_);
if (v___x_137_ == 0)
{
uint8_t v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_138_ = 1;
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = 0;
v___x_141_ = lean_box(v___x_138_);
v___x_142_ = lean_st_ref_swap(v_a_121_, v___x_141_);
lean_dec(v___x_142_);
v___x_143_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1));
v___x_144_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_139_, v___x_140_, v___x_143_, v___f_122_);
return v___x_144_;
}
else
{
lean_dec_ref(v___f_122_);
goto v___jp_125_;
}
}
v___jp_125_:
{
lean_object* v___x_126_; 
v___x_126_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1));
return v___x_126_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_121_ = stack[0].m_obj;
lean_object* v___f_122_ = stack[1].m_obj;
lean_object* v_x_123_ = stack[2].m_obj;
lean_object* v_res_145_;
v_res_145_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(v_a_121_, v___f_122_, v_x_123_);
stack->m_obj
 = v_res_145_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed(lean_object* v_a_146_, lean_object* v___f_147_, lean_object* v_x_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(v_a_146_, v___f_147_, v_x_148_);
lean_dec(v_a_146_);
return v_res_150_;
}
}
lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(lean_object* v_full_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___f_154_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed), 3, 1);
lean_closure_set(v___f_154_, 0, v_full_151_);
lean_inc(v_a_152_);
v___f_155_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed), 4, 2);
lean_closure_set(v___f_155_, 0, v_a_152_);
lean_closure_set(v___f_155_, 1, v___f_154_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = 0;
v___x_158_ = lean_st_ref_get(v_a_152_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___x_161_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_156_, v___x_157_, v___x_160_, v___f_155_);
return v___x_161_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_151_ = stack[0].m_obj;
lean_object* v_a_152_ = stack[1].m_obj;
lean_object* v_res_162_;
v_res_162_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v_full_151_, v_a_152_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed(lean_object* v_full_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v_full_163_, v_a_164_);
lean_dec(v_a_164_);
return v_res_166_;
}
}
lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0(lean_object* v_data_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_178_; 
lean_dec_ref(v_data_167_);
v_a_170_ = lean_ctor_get(v_x_168_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_178_ == 0)
{
v___x_172_ = v_x_168_;
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v_x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_170_);
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
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_188_; 
v_a_179_ = lean_ctor_get(v_x_168_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_188_ == 0)
{
v___x_181_ = v_x_168_;
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v_x_168_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_data_167_);
lean_ctor_set(v___x_183_, 1, v_a_179_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_187_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_ofByteArray___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_167_ = stack[0].m_obj;
lean_object* v_x_168_ = stack[1].m_obj;
lean_object* v_res_189_;
v_res_189_ = l_Std_Http_Body_Full_ofByteArray___lam__0(v_data_167_, v_x_168_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0___boxed(lean_object* v_data_190_, lean_object* v_x_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Http_Body_Full_ofByteArray___lam__0(v_data_190_, v_x_191_);
return v_res_193_;
}
}
lean_object* l_Std_Http_Body_Full_ofByteArray(lean_object* v_data_194_){
_start:
{
lean_object* v___f_196_; uint8_t v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___f_196_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_ofByteArray___lam__0___boxed), 3, 1);
lean_closure_set(v___f_196_, 0, v_data_194_);
v___x_197_ = 0;
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = 0;
v___x_200_ = lean_box(v___x_197_);
v___x_201_ = l_Std_Mutex_new___redArg(v___x_200_);
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
v___x_204_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_198_, v___x_199_, v___x_203_, v___f_196_);
return v___x_204_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_ofByteArray_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_194_ = stack[0].m_obj;
lean_object* v_res_205_;
v_res_205_ = l_Std_Http_Body_Full_ofByteArray(v_data_194_);
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___boxed(lean_object* v_data_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Http_Body_Full_ofByteArray(v_data_206_);
return v_res_208_;
}
}
lean_object* l_Std_Http_Body_Full_ofString___lam__0(lean_object* v_data_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
v_a_212_ = lean_ctor_get(v_x_210_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v_x_210_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v_x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
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
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_219_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; 
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_231_; 
v_a_221_ = lean_ctor_get(v_x_210_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_231_ == 0)
{
v___x_223_ = v_x_210_;
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v_x_210_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_225_ = lean_string_to_utf8(v_data_209_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_a_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_226_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_ofString___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_209_ = stack[0].m_obj;
lean_object* v_x_210_ = stack[1].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Std_Http_Body_Full_ofString___lam__0(v_data_209_, v_x_210_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___lam__0___boxed(lean_object* v_data_233_, lean_object* v_x_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Http_Body_Full_ofString___lam__0(v_data_233_, v_x_234_);
lean_dec_ref(v_data_233_);
return v_res_236_;
}
}
lean_object* l_Std_Http_Body_Full_ofString(lean_object* v_data_237_){
_start:
{
lean_object* v___f_239_; uint8_t v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___f_239_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_ofString___lam__0___boxed), 3, 1);
lean_closure_set(v___f_239_, 0, v_data_237_);
v___x_240_ = 0;
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = 0;
v___x_243_ = lean_box(v___x_240_);
v___x_244_ = l_Std_Mutex_new___redArg(v___x_243_);
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
v___x_247_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_241_, v___x_242_, v___x_246_, v___f_239_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_ofString_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_237_ = stack[0].m_obj;
lean_object* v_res_248_;
v_res_248_ = l_Std_Http_Body_Full_ofString(v_data_237_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___boxed(lean_object* v_data_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_Http_Body_Full_ofString(v_data_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0(lean_object* v___y_252_){
_start:
{
if (lean_obj_tag(v___y_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
v_a_253_ = lean_ctor_get(v___y_252_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___y_252_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___y_252_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___y_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
v_a_261_ = lean_ctor_get(v___y_252_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___y_252_);
if (v_isSharedCheck_269_ == 0)
{
v___x_263_ = v___y_252_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___y_252_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_fst_265_; lean_object* v___x_267_; 
v_fst_265_ = lean_ctor_get(v_a_261_, 0);
lean_inc(v_fst_265_);
lean_dec(v_a_261_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v_fst_265_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_fst_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(lean_object* v_mutex_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_io_basemutex_unlock(v_mutex_270_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_270_ = stack[0].m_obj;
lean_object* v_x_271_ = stack[1].m_obj;
lean_object* v_res_276_;
v_res_276_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(v_mutex_270_, v_x_271_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed(lean_object* v_mutex_277_, lean_object* v_x_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(v_mutex_277_, v_x_278_);
lean_dec(v_x_278_);
lean_dec(v_mutex_277_);
return v_res_280_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(lean_object* v_k_281_, lean_object* v_ref_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
lean_dec(v_ref_282_);
lean_dec_ref(v_k_281_);
v_a_285_ = lean_ctor_get(v_x_283_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_293_ == 0)
{
v___x_287_ = v_x_283_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v_x_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_292_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
}
else
{
lean_object* v___x_294_; 
lean_dec_ref_known(v_x_283_, 1);
v___x_294_ = lean_apply_2(v_k_281_, v_ref_282_, lean_box(0));
return v___x_294_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_281_ = stack[0].m_obj;
lean_object* v_ref_282_ = stack[1].m_obj;
lean_object* v_x_283_ = stack[2].m_obj;
lean_object* v_res_295_;
v_res_295_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(v_k_281_, v_ref_282_, v_x_283_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed(lean_object* v_k_296_, lean_object* v_ref_297_, lean_object* v_x_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(v_k_296_, v_ref_297_, v_x_298_);
return v_res_300_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(lean_object* v_mutex_301_, lean_object* v___f_302_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = 0;
v___x_306_ = lean_io_basemutex_lock(v_mutex_301_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
v___x_309_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_304_, v___x_305_, v___x_308_, v___f_302_);
return v___x_309_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_301_ = stack[0].m_obj;
lean_object* v___f_302_ = stack[1].m_obj;
lean_object* v_res_310_;
v_res_310_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(v_mutex_301_, v___f_302_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3___boxed(lean_object* v_mutex_311_, lean_object* v___f_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(v_mutex_311_, v___f_312_);
lean_dec(v_mutex_311_);
return v_res_314_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(lean_object* v_mutex_316_, lean_object* v_k_317_){
_start:
{
lean_object* v_ref_319_; lean_object* v_mutex_320_; lean_object* v___f_321_; lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___y_329_; 
v_ref_319_ = lean_ctor_get(v_mutex_316_, 0);
lean_inc(v_ref_319_);
v_mutex_320_ = lean_ctor_get(v_mutex_316_, 1);
lean_inc_n(v_mutex_320_, 2);
lean_dec_ref(v_mutex_316_);
v___f_321_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0));
v___f_322_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_322_, 0, v_mutex_320_);
v___f_323_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_323_, 0, v_k_317_);
lean_closure_set(v___f_323_, 1, v_ref_319_);
v___f_324_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_324_, 0, v_mutex_320_);
lean_closure_set(v___f_324_, 1, v___f_323_);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = 0;
v___x_327_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_324_, v___f_322_, v___x_325_, v___x_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_331_; 
v_a_331_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_327_, 1);
if (lean_obj_tag(v_a_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_a_332_ = lean_ctor_get(v_a_331_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v_a_331_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v_a_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
v___y_329_ = v___x_337_;
goto v___jp_328_;
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_a_340_ = lean_ctor_get(v_a_331_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v_a_331_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v_a_331_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_fst_344_; lean_object* v___x_346_; 
v_fst_344_ = lean_ctor_get(v_a_340_, 0);
lean_inc(v_fst_344_);
lean_dec(v_a_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v_fst_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_fst_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
v___y_329_ = v___x_346_;
goto v___jp_328_;
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_357_; 
v_a_349_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_357_ == 0)
{
v___x_351_ = v___x_327_;
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_327_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_task_map(v___f_321_, v_a_349_, v___x_325_, v___x_326_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
v___jp_328_:
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___y_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_316_ = stack[0].m_obj;
lean_object* v_k_317_ = stack[1].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_mutex_316_, v_k_317_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___boxed(lean_object* v_mutex_359_, lean_object* v_k_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_mutex_359_, v_k_360_);
return v_res_362_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(lean_object* v_00_u03b1_363_, lean_object* v_00_u03b2_364_, lean_object* v_mutex_365_, lean_object* v_k_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_mutex_365_, v_k_366_);
return v___x_368_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_365_ = stack[2].m_obj;
lean_object* v_k_366_ = stack[3].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(lean_box(0), lean_box(0), v_mutex_365_, v_k_366_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___boxed(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_mutex_372_, lean_object* v_k_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(v_00_u03b1_370_, v_00_u03b2_371_, v_mutex_372_, v_k_373_);
return v_res_375_;
}
}
lean_object* l_Std_Http_Body_Full_recv(lean_object* v_full_376_){
_start:
{
lean_object* v_state_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_state_378_ = lean_ctor_get(v_full_376_, 1);
lean_inc_ref(v_state_378_);
v___x_379_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 3, 1);
lean_closure_set(v___x_379_, 0, v_full_376_);
v___x_380_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_378_, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_376_ = stack[0].m_obj;
lean_object* v_res_381_;
v_res_381_ = l_Std_Http_Body_Full_recv(v_full_376_);
stack->m_obj
 = v_res_381_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv___boxed(lean_object* v_full_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Http_Body_Full_recv(v_full_382_);
return v_res_384_;
}
}
lean_object* l_Std_Http_Body_Full_close___lam__0(uint8_t v___x_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = lean_box(v___x_385_);
v___x_389_ = lean_st_ref_swap(v___y_386_, v___x_388_);
lean_dec(v___x_389_);
v___x_390_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1));
return v___x_390_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_close___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_385_ = stack[0].m_num;
lean_object* v___y_386_ = stack[1].m_obj;
lean_object* v_res_391_;
v_res_391_ = l_Std_Http_Body_Full_close___lam__0(v___x_385_, v___y_386_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0___boxed(lean_object* v___x_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v___x_177__boxed_395_; lean_object* v_res_396_; 
v___x_177__boxed_395_ = lean_unbox(v___x_392_);
v_res_396_ = l_Std_Http_Body_Full_close___lam__0(v___x_177__boxed_395_, v___y_393_);
lean_dec(v___y_393_);
return v_res_396_;
}
}
lean_object* l_Std_Http_Body_Full_close(lean_object* v_full_400_){
_start:
{
lean_object* v_state_402_; lean_object* v___f_403_; lean_object* v___x_404_; 
v_state_402_ = lean_ctor_get(v_full_400_, 1);
lean_inc_ref(v_state_402_);
lean_dec_ref(v_full_400_);
v___f_403_ = ((lean_object*)(l_Std_Http_Body_Full_close___closed__0));
v___x_404_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_402_, v___f_403_);
return v___x_404_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_400_ = stack[0].m_obj;
lean_object* v_res_405_;
v_res_405_ = l_Std_Http_Body_Full_close(v_full_400_);
stack->m_obj
 = v_res_405_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___boxed(lean_object* v_full_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_Http_Body_Full_close(v_full_406_);
return v_res_408_;
}
}
lean_object* l_Std_Http_Body_Full_isClosed___lam__0(lean_object* v_x_409_){
_start:
{
uint8_t v___y_412_; 
if (lean_obj_tag(v_x_409_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_424_; 
v_a_416_ = lean_ctor_get(v_x_409_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_409_);
if (v_isSharedCheck_424_ == 0)
{
v___x_418_ = v_x_409_;
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v_x_409_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_423_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
}
else
{
lean_object* v_a_425_; uint8_t v___x_426_; uint8_t v___x_427_; uint8_t v___x_428_; 
v_a_425_ = lean_ctor_get(v_x_409_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v_x_409_, 1);
v___x_426_ = 0;
v___x_427_ = lean_unbox(v_a_425_);
lean_dec(v_a_425_);
v___x_428_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(v___x_427_, v___x_426_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 1;
v___y_412_ = v___x_429_;
goto v___jp_411_;
}
else
{
uint8_t v___x_430_; 
v___x_430_ = 0;
v___y_412_ = v___x_430_;
goto v___jp_411_;
}
}
v___jp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_box(v___y_412_);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_isClosed___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_409_ = stack[0].m_obj;
lean_object* v_res_431_;
v_res_431_ = l_Std_Http_Body_Full_isClosed___lam__0(v_x_409_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__0___boxed(lean_object* v_x_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_Http_Body_Full_isClosed___lam__0(v_x_432_);
return v_res_434_;
}
}
lean_object* l_Std_Http_Body_Full_isClosed___lam__1(lean_object* v___f_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = 0;
v___x_440_ = lean_st_ref_get(v___y_436_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
v___x_443_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_438_, v___x_439_, v___x_442_, v___f_435_);
return v___x_443_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_isClosed___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_435_ = stack[0].m_obj;
lean_object* v___y_436_ = stack[1].m_obj;
lean_object* v_res_444_;
v_res_444_ = l_Std_Http_Body_Full_isClosed___lam__1(v___f_435_, v___y_436_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__1___boxed(lean_object* v___f_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_Http_Body_Full_isClosed___lam__1(v___f_445_, v___y_446_);
lean_dec(v___y_446_);
return v_res_448_;
}
}
lean_object* l_Std_Http_Body_Full_isClosed(lean_object* v_full_452_){
_start:
{
lean_object* v_state_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
v_state_454_ = lean_ctor_get(v_full_452_, 1);
lean_inc_ref(v_state_454_);
lean_dec_ref(v_full_452_);
v___f_455_ = ((lean_object*)(l_Std_Http_Body_Full_isClosed___closed__1));
v___x_456_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_454_, v___f_455_);
return v___x_456_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_isClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_452_ = stack[0].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Std_Http_Body_Full_isClosed(v_full_452_);
stack->m_obj
 = v_res_457_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___boxed(lean_object* v_full_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_Http_Body_Full_isClosed(v_full_458_);
return v_res_460_;
}
}
lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0(lean_object* v_data_469_, lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_482_; 
v_a_474_ = lean_ctor_get(v_x_470_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_482_ == 0)
{
v___x_476_ = v_x_470_;
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v_x_470_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_481_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; 
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_495_; 
v_a_483_ = lean_ctor_get(v_x_470_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_495_ == 0)
{
v___x_485_ = v_x_470_;
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v_x_470_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint8_t v___x_487_; 
v___x_487_ = lean_unbox(v_a_483_);
lean_dec(v_a_483_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_488_ = lean_byte_array_size(v_data_469_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_490_);
v___x_492_ = v___x_485_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_490_);
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
else
{
lean_del_object(v___x_485_);
goto v___jp_472_;
}
}
}
v___jp_472_:
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3));
return v___x_473_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_getKnownSize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_469_ = stack[0].m_obj;
lean_object* v_x_470_ = stack[1].m_obj;
lean_object* v_res_496_;
v_res_496_ = l_Std_Http_Body_Full_getKnownSize___lam__0(v_data_469_, v_x_470_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___boxed(lean_object* v_data_497_, lean_object* v_x_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Http_Body_Full_getKnownSize___lam__0(v_data_497_, v_x_498_);
lean_dec_ref(v_data_497_);
return v_res_500_;
}
}
lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1(lean_object* v___f_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = 0;
v___x_506_ = lean_st_ref_get(v___y_502_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___x_509_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_504_, v___x_505_, v___x_508_, v___f_501_);
return v___x_509_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_getKnownSize___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_501_ = stack[0].m_obj;
lean_object* v___y_502_ = stack[1].m_obj;
lean_object* v_res_510_;
v_res_510_ = l_Std_Http_Body_Full_getKnownSize___lam__1(v___f_501_, v___y_502_);
stack->m_obj
 = v_res_510_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1___boxed(lean_object* v___f_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Http_Body_Full_getKnownSize___lam__1(v___f_511_, v___y_512_);
lean_dec(v___y_512_);
return v_res_514_;
}
}
lean_object* l_Std_Http_Body_Full_getKnownSize(lean_object* v_full_515_){
_start:
{
lean_object* v_data_517_; lean_object* v_state_518_; lean_object* v___f_519_; lean_object* v___f_520_; lean_object* v___x_521_; 
v_data_517_ = lean_ctor_get(v_full_515_, 0);
lean_inc_ref(v_data_517_);
v_state_518_ = lean_ctor_get(v_full_515_, 1);
lean_inc_ref(v_state_518_);
lean_dec_ref(v_full_515_);
v___f_519_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_getKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_519_, 0, v_data_517_);
v___f_520_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_getKnownSize___lam__1___boxed), 3, 1);
lean_closure_set(v___f_520_, 0, v___f_519_);
v___x_521_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_518_, v___f_520_);
return v___x_521_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_getKnownSize_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_515_ = stack[0].m_obj;
lean_object* v_res_522_;
v_res_522_ = l_Std_Http_Body_Full_getKnownSize(v_full_515_);
stack->m_obj
 = v_res_522_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___boxed(lean_object* v_full_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Http_Body_Full_getKnownSize(v_full_523_);
return v_res_525_;
}
}
lean_object* l_Std_Http_Body_Full_tryRecv___lam__0(lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_a_528_ = lean_ctor_get(v_x_526_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v_x_526_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v_x_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_546_; 
v_a_537_ = lean_ctor_get(v_x_526_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_546_ == 0)
{
v___x_539_ = v_x_526_;
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v_x_526_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v_a_537_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_541_);
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
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_tryRecv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_526_ = stack[0].m_obj;
lean_object* v_res_547_;
v_res_547_ = l_Std_Http_Body_Full_tryRecv___lam__0(v_x_526_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___lam__0___boxed(lean_object* v_x_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Http_Body_Full_tryRecv___lam__0(v_x_548_);
return v_res_550_;
}
}
lean_object* l_Std_Http_Body_Full_tryRecv(lean_object* v_full_552_){
_start:
{
lean_object* v_state_554_; lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_state_554_ = lean_ctor_get(v_full_552_, 1);
lean_inc_ref(v_state_554_);
v___f_555_ = ((lean_object*)(l_Std_Http_Body_Full_tryRecv___closed__0));
v___x_556_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 3, 1);
lean_closure_set(v___x_556_, 0, v_full_552_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = 0;
v___x_559_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_554_, v___x_556_);
v___x_560_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_557_, v___x_558_, v___x_559_, v___f_555_);
return v___x_560_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_552_ = stack[0].m_obj;
lean_object* v_res_561_;
v_res_561_ = l_Std_Http_Body_Full_tryRecv(v_full_552_);
stack->m_obj
 = v_res_561_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___boxed(lean_object* v_full_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Http_Body_Full_tryRecv(v_full_562_);
return v_res_564_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(lean_object* v_promise_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v_a_568_ = lean_ctor_get(v_x_566_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_566_);
if (v_isSharedCheck_576_ == 0)
{
v___x_570_ = v_x_566_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v_x_566_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_575_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_io_promise_resolve(v_x_566_, v_promise_565_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_565_ = stack[0].m_obj;
lean_object* v_x_566_ = stack[1].m_obj;
lean_object* v_res_580_;
v_res_580_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(v_promise_565_, v_x_566_);
stack->m_obj
 = v_res_580_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed(lean_object* v_promise_581_, lean_object* v_x_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(v_promise_581_, v_x_582_);
lean_dec(v_promise_581_);
return v_res_584_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(lean_object* v_lose_585_, lean_object* v___y_586_, lean_object* v_full_587_, lean_object* v___f_588_, lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v___f_588_);
lean_dec_ref(v_full_587_);
lean_dec_ref(v_lose_585_);
v_a_591_ = lean_ctor_get(v_x_589_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v_x_589_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v_x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
}
else
{
lean_object* v_a_600_; uint8_t v___x_601_; 
v_a_600_ = lean_ctor_get(v_x_589_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v_x_589_, 1);
v___x_601_ = lean_unbox(v_a_600_);
lean_dec(v_a_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v___f_588_);
lean_dec_ref(v_full_587_);
lean_inc(v___y_586_);
v___x_602_ = lean_apply_2(v_lose_585_, v___y_586_, lean_box(0));
return v___x_602_;
}
else
{
lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec_ref(v_lose_585_);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = 0;
v___x_605_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v_full_587_, v___y_586_);
v___x_606_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_603_, v___x_604_, v___x_605_, v___f_588_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lose_585_ = stack[0].m_obj;
lean_object* v___y_586_ = stack[1].m_obj;
lean_object* v_full_587_ = stack[2].m_obj;
lean_object* v___f_588_ = stack[3].m_obj;
lean_object* v_x_589_ = stack[4].m_obj;
lean_object* v_res_607_;
v_res_607_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(v_lose_585_, v___y_586_, v_full_587_, v___f_588_, v_x_589_);
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed(lean_object* v_lose_608_, lean_object* v___y_609_, lean_object* v_full_610_, lean_object* v___f_611_, lean_object* v_x_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(v_lose_608_, v___y_609_, v_full_610_, v___f_611_, v_x_612_);
lean_dec(v___y_609_);
return v_res_614_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(lean_object* v_full_615_, lean_object* v_w_616_, lean_object* v_lose_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_finished_620_; lean_object* v_promise_621_; lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; uint8_t v___y_628_; uint8_t v___x_636_; 
v_finished_620_ = lean_ctor_get(v_w_616_, 0);
lean_inc(v_finished_620_);
v_promise_621_ = lean_ctor_get(v_w_616_, 1);
lean_inc(v_promise_621_);
lean_dec_ref(v_w_616_);
v___f_622_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_622_, 0, v_promise_621_);
lean_inc(v___y_618_);
v___f_623_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed), 6, 4);
lean_closure_set(v___f_623_, 0, v_lose_617_);
lean_closure_set(v___f_623_, 1, v___y_618_);
lean_closure_set(v___f_623_, 2, v_full_615_);
lean_closure_set(v___f_623_, 3, v___f_622_);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = 0;
v___x_626_ = lean_st_ref_take(v_finished_620_);
v___x_636_ = lean_unbox(v___x_626_);
lean_dec(v___x_626_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; 
v___x_637_ = 1;
v___y_628_ = v___x_637_;
goto v___jp_627_;
}
else
{
v___y_628_ = v___x_625_;
goto v___jp_627_;
}
v___jp_627_:
{
uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_629_ = 1;
v___x_630_ = lean_box(v___x_629_);
v___x_631_ = lean_st_ref_put(v_finished_620_, v___x_630_);
lean_dec(v_finished_620_);
v___x_632_ = lean_box(v___y_628_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___x_635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_624_, v___x_625_, v___x_634_, v___f_623_);
return v___x_635_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_615_ = stack[0].m_obj;
lean_object* v_w_616_ = stack[1].m_obj;
lean_object* v_lose_617_ = stack[2].m_obj;
lean_object* v___y_618_ = stack[3].m_obj;
lean_object* v_res_638_;
v_res_638_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(v_full_615_, v_w_616_, v_lose_617_, v___y_618_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed(lean_object* v_full_639_, lean_object* v_w_640_, lean_object* v_lose_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(v_full_639_, v_w_640_, v_lose_641_, v___y_642_);
lean_dec(v___y_642_);
return v_res_644_;
}
}
lean_object* l_Std_Http_Body_Full_recvSelector___lam__1(lean_object* v___x_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_645_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_recvSelector___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_645_ = stack[0].m_obj;
lean_object* v___y_646_ = stack[1].m_obj;
lean_object* v_res_650_;
v_res_650_ = l_Std_Http_Body_Full_recvSelector___lam__1(v___x_645_, v___y_646_);
stack->m_obj
 = v_res_650_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1___boxed(lean_object* v___x_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Http_Body_Full_recvSelector___lam__1(v___x_651_, v___y_652_);
lean_dec(v___y_652_);
return v_res_654_;
}
}
lean_object* l_Std_Http_Body_Full_recvSelector___lam__0(lean_object* v_full_657_, lean_object* v_state_658_, lean_object* v_waiter_659_){
_start:
{
lean_object* v_lose_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_lose_661_ = ((lean_object*)(l_Std_Http_Body_Full_recvSelector___lam__0___closed__0));
v___x_662_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed), 5, 3);
lean_closure_set(v___x_662_, 0, v_full_657_);
lean_closure_set(v___x_662_, 1, v_waiter_659_);
lean_closure_set(v___x_662_, 2, v_lose_661_);
v___x_663_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_658_, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_recvSelector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_657_ = stack[0].m_obj;
lean_object* v_state_658_ = stack[1].m_obj;
lean_object* v_waiter_659_ = stack[2].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Std_Http_Body_Full_recvSelector___lam__0(v_full_657_, v_state_658_, v_waiter_659_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0___boxed(lean_object* v_full_665_, lean_object* v_state_666_, lean_object* v_waiter_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_Http_Body_Full_recvSelector___lam__0(v_full_665_, v_state_666_, v_waiter_667_);
return v_res_669_;
}
}
lean_object* l_Std_Http_Body_Full_recvSelector___lam__2(lean_object* v_state_670_, lean_object* v___x_671_, lean_object* v___f_672_){
_start:
{
lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = 0;
v___x_676_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_670_, v___x_671_);
v___x_677_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_674_, v___x_675_, v___x_676_, v___f_672_);
return v___x_677_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_recvSelector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_state_670_ = stack[0].m_obj;
lean_object* v___x_671_ = stack[1].m_obj;
lean_object* v___f_672_ = stack[2].m_obj;
lean_object* v_res_678_;
v_res_678_ = l_Std_Http_Body_Full_recvSelector___lam__2(v_state_670_, v___x_671_, v___f_672_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2___boxed(lean_object* v_state_679_, lean_object* v___x_680_, lean_object* v___f_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_Http_Body_Full_recvSelector___lam__2(v_state_679_, v___x_680_, v___f_681_);
return v_res_683_;
}
}
lean_object* l_Std_Http_Body_Full_recvSelector___lam__3(lean_object* v___x_684_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_recvSelector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_684_ = stack[0].m_obj;
lean_object* v_res_688_;
v_res_688_ = l_Std_Http_Body_Full_recvSelector___lam__3(v___x_684_);
stack->m_obj
 = v_res_688_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3___boxed(lean_object* v___x_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_Http_Body_Full_recvSelector___lam__3(v___x_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector(lean_object* v_full_694_){
_start:
{
lean_object* v_state_695_; lean_object* v___f_696_; lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___x_701_; 
v_state_695_ = lean_ctor_get(v_full_694_, 1);
lean_inc_ref_n(v_state_695_, 2);
v___f_696_ = ((lean_object*)(l_Std_Http_Body_Full_tryRecv___closed__0));
lean_inc_ref(v_full_694_);
v___f_697_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_recvSelector___lam__0___boxed), 4, 2);
lean_closure_set(v___f_697_, 0, v_full_694_);
lean_closure_set(v___f_697_, 1, v_state_695_);
v___x_698_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 3, 1);
lean_closure_set(v___x_698_, 0, v_full_694_);
v___f_699_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_recvSelector___lam__2___boxed), 4, 3);
lean_closure_set(v___f_699_, 0, v_state_695_);
lean_closure_set(v___f_699_, 1, v___x_698_);
lean_closure_set(v___f_699_, 2, v___f_696_);
v___f_700_ = ((lean_object*)(l_Std_Http_Body_Full_recvSelector___closed__0));
v___x_701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_701_, 0, v___f_699_);
lean_ctor_set(v___x_701_, 1, v___f_697_);
lean_ctor_set(v___x_701_, 2, v___f_700_);
return v___x_701_;
}
}
lean_object* l_Std_Http_Body_Full_resetInPlace(lean_object* v_full_705_){
_start:
{
lean_object* v_state_707_; lean_object* v___f_708_; lean_object* v___x_709_; 
v_state_707_ = lean_ctor_get(v_full_705_, 1);
lean_inc_ref(v_state_707_);
lean_dec_ref(v_full_705_);
v___f_708_ = ((lean_object*)(l_Std_Http_Body_Full_resetInPlace___closed__0));
v___x_709_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_707_, v___f_708_);
return v___x_709_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Full_resetInPlace_0interp(lean_interpreter_value* stack)
{
lean_object* v_full_705_ = stack[0].m_obj;
lean_object* v_res_710_;
v_res_710_ = l_Std_Http_Body_Full_resetInPlace(v_full_705_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_resetInPlace___boxed(lean_object* v_full_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_Http_Body_Full_resetInPlace(v_full_711_);
return v_res_713_;
}
}
lean_object* l_Std_Http_Body_instFull___lam__0(lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1));
return v___x_717_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instFull___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_714_ = stack[0].m_obj;
lean_object* v_x_715_ = stack[1].m_obj;
lean_object* v_res_718_;
v_res_718_ = l_Std_Http_Body_instFull___lam__0(v_x_714_, v_x_715_);
stack->m_obj
 = v_res_718_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instFull___lam__0___boxed(lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_Http_Body_instFull___lam__0(v_x_719_, v_x_720_);
lean_dec(v_x_720_);
lean_dec_ref(v_x_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseFullAny___lam__0(lean_object* v___x_745_, lean_object* v___x_746_, lean_object* v_f_747_){
_start:
{
lean_object* v_line_748_; lean_object* v_body_749_; lean_object* v_extensions_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_line_748_ = lean_ctor_get(v_f_747_, 0);
v_body_749_ = lean_ctor_get(v_f_747_, 1);
v_extensions_750_ = lean_ctor_get(v_f_747_, 2);
v_isSharedCheck_758_ = !lean_is_exclusive(v_f_747_);
if (v_isSharedCheck_758_ == 0)
{
v___x_752_ = v_f_747_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_extensions_750_);
lean_inc(v_body_749_);
lean_inc(v_line_748_);
lean_dec(v_f_747_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_745_, v___x_746_, v_body_749_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_line_748_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_extensions_750_);
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
lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(lean_object* v___x_763_, lean_object* v___x_764_, lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v___x_764_);
lean_dec_ref(v___x_763_);
v_a_767_ = lean_ctor_get(v_x_765_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_775_ == 0)
{
v___x_769_ = v_x_765_;
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v_x_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_774_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; 
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_795_; 
v_a_776_ = lean_ctor_get(v_x_765_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_795_ == 0)
{
v___x_778_ = v_x_765_;
v_isShared_779_ = v_isSharedCheck_795_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v_x_765_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_795_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_line_780_; lean_object* v_body_781_; lean_object* v_extensions_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_794_; 
v_line_780_ = lean_ctor_get(v_a_776_, 0);
v_body_781_ = lean_ctor_get(v_a_776_, 1);
v_extensions_782_ = lean_ctor_get(v_a_776_, 2);
v_isSharedCheck_794_ = !lean_is_exclusive(v_a_776_);
if (v_isSharedCheck_794_ == 0)
{
v___x_784_ = v_a_776_;
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_extensions_782_);
lean_inc(v_body_781_);
lean_inc(v_line_780_);
lean_dec(v_a_776_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_763_, v___x_764_, v_body_781_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_line_780_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_extensions_782_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_788_);
v___x_790_ = v___x_778_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_792_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_763_ = stack[0].m_obj;
lean_object* v___x_764_ = stack[1].m_obj;
lean_object* v_x_765_ = stack[2].m_obj;
lean_object* v_res_796_;
v_res_796_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(v___x_763_, v___x_764_, v_x_765_);
stack->m_obj
 = v_res_796_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed(lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v_x_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(v___x_797_, v___x_798_, v_x_799_);
return v_res_801_;
}
}
lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(lean_object* v___f_802_, lean_object* v_action_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = 0;
lean_inc_ref(v___y_804_);
v___x_808_ = lean_apply_2(v_action_803_, v___y_804_, lean_box(0));
v___x_809_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_806_, v___x_807_, v___x_808_, v___f_802_);
return v___x_809_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_802_ = stack[0].m_obj;
lean_object* v_action_803_ = stack[1].m_obj;
lean_object* v___y_804_ = stack[2].m_obj;
lean_object* v_res_810_;
v_res_810_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(v___f_802_, v_action_803_, v___y_804_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1___boxed(lean_object* v___f_811_, lean_object* v_action_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(v___f_811_, v_action_812_, v___y_813_);
lean_dec_ref(v___y_813_);
return v_res_815_;
}
}
lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(lean_object* v___f_822_, lean_object* v_action_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = 0;
v___x_828_ = lean_apply_1(v_action_823_, lean_box(0));
v___x_829_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_826_, v___x_827_, v___x_828_, v___f_822_);
return v___x_829_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_822_ = stack[0].m_obj;
lean_object* v_action_823_ = stack[1].m_obj;
lean_object* v___y_824_ = stack[2].m_obj;
lean_object* v_res_830_;
v_res_830_ = l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(v___f_822_, v_action_823_, v___y_824_);
stack->m_obj
 = v_res_830_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1___boxed(lean_object* v___f_831_, lean_object* v_action_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(v___f_831_, v_action_832_, v___y_833_);
lean_dec_ref(v___y_833_);
return v_res_835_;
}
}
lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0(lean_object* v_builder_839_, lean_object* v_x_840_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_a_842_ = lean_ctor_get(v_x_840_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_840_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v_x_840_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v_x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_860_; 
v_a_851_ = lean_ctor_get(v_x_840_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_840_);
if (v_isSharedCheck_860_ == 0)
{
v___x_853_ = v_x_840_;
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v_x_840_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = l_Std_Http_Request_Builder_body___redArg(v_builder_839_, v_a_851_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_fromBytes___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_839_ = stack[0].m_obj;
lean_object* v_x_840_ = stack[1].m_obj;
lean_object* v_res_861_;
v_res_861_ = l_Std_Http_Request_Builder_fromBytes___lam__0(v_builder_839_, v_x_840_);
stack->m_obj
 = v_res_861_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0___boxed(lean_object* v_builder_862_, lean_object* v_x_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_Http_Request_Builder_fromBytes___lam__0(v_builder_862_, v_x_863_);
lean_dec_ref(v_builder_862_);
return v_res_865_;
}
}
lean_object* l_Std_Http_Request_Builder_fromBytes(lean_object* v_builder_866_, lean_object* v_content_867_){
_start:
{
lean_object* v___f_869_; lean_object* v___x_870_; uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___f_869_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_869_, 0, v_builder_866_);
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = 0;
v___x_872_ = l_Std_Http_Body_Full_ofByteArray(v_content_867_);
v___x_873_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_870_, v___x_871_, v___x_872_, v___f_869_);
return v___x_873_;
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_fromBytes_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_866_ = stack[0].m_obj;
lean_object* v_content_867_ = stack[1].m_obj;
lean_object* v_res_874_;
v_res_874_ = l_Std_Http_Request_Builder_fromBytes(v_builder_866_, v_content_867_);
stack->m_obj
 = v_res_874_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___boxed(lean_object* v_builder_875_, lean_object* v_content_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_Http_Request_Builder_fromBytes(v_builder_875_, v_content_876_);
return v_res_878_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_bytes___closed__1(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_Std_Http_Request_Builder_bytes___closed__0));
v___x_881_ = l_Std_Http_Header_Value_ofString_x21(v___x_880_);
return v___x_881_;
}
}
lean_object* l_Std_Http_Request_Builder_bytes(lean_object* v_builder_882_, lean_object* v_content_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_885_ = l_Std_Http_Header_Name_contentType;
v___x_886_ = lean_obj_once(&l_Std_Http_Request_Builder_bytes___closed__1, &l_Std_Http_Request_Builder_bytes___closed__1_once, _init_l_Std_Http_Request_Builder_bytes___closed__1);
v___x_887_ = l_Std_Http_Request_Builder_header(v_builder_882_, v___x_885_, v___x_886_);
v___x_888_ = l_Std_Http_Request_Builder_fromBytes(v___x_887_, v_content_883_);
return v___x_888_;
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_bytes_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_882_ = stack[0].m_obj;
lean_object* v_content_883_ = stack[1].m_obj;
lean_object* v_res_889_;
v_res_889_ = l_Std_Http_Request_Builder_bytes(v_builder_882_, v_content_883_);
stack->m_obj
 = v_res_889_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_bytes___boxed(lean_object* v_builder_890_, lean_object* v_content_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_Http_Request_Builder_bytes(v_builder_890_, v_content_891_);
return v_res_893_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_text___closed__1(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l_Std_Http_Request_Builder_text___closed__0));
v___x_896_ = l_Std_Http_Header_Value_ofString_x21(v___x_895_);
return v___x_896_;
}
}
lean_object* l_Std_Http_Request_Builder_text(lean_object* v_builder_897_, lean_object* v_content_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_900_ = l_Std_Http_Header_Name_contentType;
v___x_901_ = lean_obj_once(&l_Std_Http_Request_Builder_text___closed__1, &l_Std_Http_Request_Builder_text___closed__1_once, _init_l_Std_Http_Request_Builder_text___closed__1);
v___x_902_ = l_Std_Http_Request_Builder_header(v_builder_897_, v___x_900_, v___x_901_);
v___x_903_ = lean_string_to_utf8(v_content_898_);
v___x_904_ = l_Std_Http_Request_Builder_fromBytes(v___x_902_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_text_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_897_ = stack[0].m_obj;
lean_object* v_content_898_ = stack[1].m_obj;
lean_object* v_res_905_;
v_res_905_ = l_Std_Http_Request_Builder_text(v_builder_897_, v_content_898_);
stack->m_obj
 = v_res_905_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_text___boxed(lean_object* v_builder_906_, lean_object* v_content_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_Http_Request_Builder_text(v_builder_906_, v_content_907_);
lean_dec_ref(v_content_907_);
return v_res_909_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_json___closed__1(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Std_Http_Request_Builder_json___closed__0));
v___x_912_ = l_Std_Http_Header_Value_ofString_x21(v___x_911_);
return v___x_912_;
}
}
lean_object* l_Std_Http_Request_Builder_json(lean_object* v_builder_913_, lean_object* v_content_914_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_916_ = l_Std_Http_Header_Name_contentType;
v___x_917_ = lean_obj_once(&l_Std_Http_Request_Builder_json___closed__1, &l_Std_Http_Request_Builder_json___closed__1_once, _init_l_Std_Http_Request_Builder_json___closed__1);
v___x_918_ = l_Std_Http_Request_Builder_header(v_builder_913_, v___x_916_, v___x_917_);
v___x_919_ = lean_string_to_utf8(v_content_914_);
v___x_920_ = l_Std_Http_Request_Builder_fromBytes(v___x_918_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_json_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_913_ = stack[0].m_obj;
lean_object* v_content_914_ = stack[1].m_obj;
lean_object* v_res_921_;
v_res_921_ = l_Std_Http_Request_Builder_json(v_builder_913_, v_content_914_);
stack->m_obj
 = v_res_921_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_json___boxed(lean_object* v_builder_922_, lean_object* v_content_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_Http_Request_Builder_json(v_builder_922_, v_content_923_);
lean_dec_ref(v_content_923_);
return v_res_925_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_html___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l_Std_Http_Request_Builder_html___closed__0));
v___x_928_ = l_Std_Http_Header_Value_ofString_x21(v___x_927_);
return v___x_928_;
}
}
lean_object* l_Std_Http_Request_Builder_html(lean_object* v_builder_929_, lean_object* v_content_930_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_932_ = l_Std_Http_Header_Name_contentType;
v___x_933_ = lean_obj_once(&l_Std_Http_Request_Builder_html___closed__1, &l_Std_Http_Request_Builder_html___closed__1_once, _init_l_Std_Http_Request_Builder_html___closed__1);
v___x_934_ = l_Std_Http_Request_Builder_header(v_builder_929_, v___x_932_, v___x_933_);
v___x_935_ = lean_string_to_utf8(v_content_930_);
v___x_936_ = l_Std_Http_Request_Builder_fromBytes(v___x_934_, v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_html_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_929_ = stack[0].m_obj;
lean_object* v_content_930_ = stack[1].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Std_Http_Request_Builder_html(v_builder_929_, v_content_930_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_html___boxed(lean_object* v_builder_938_, lean_object* v_content_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_Http_Request_Builder_html(v_builder_938_, v_content_939_);
lean_dec_ref(v_content_939_);
return v_res_941_;
}
}
lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0(lean_object* v_builder_942_, lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_953_; 
v_a_945_ = lean_ctor_get(v_x_943_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_943_);
if (v_isSharedCheck_953_ == 0)
{
v___x_947_ = v_x_943_;
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v_x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_963_; 
v_a_954_ = lean_ctor_get(v_x_943_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_943_);
if (v_isSharedCheck_963_ == 0)
{
v___x_956_ = v_x_943_;
v_isShared_957_ = v_isSharedCheck_963_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v_x_943_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_963_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = l_Std_Http_Response_Builder_body___redArg(v_builder_942_, v_a_954_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_958_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_962_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; 
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Response_Builder_fromBytes___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_942_ = stack[0].m_obj;
lean_object* v_x_943_ = stack[1].m_obj;
lean_object* v_res_964_;
v_res_964_ = l_Std_Http_Response_Builder_fromBytes___lam__0(v_builder_942_, v_x_943_);
stack->m_obj
 = v_res_964_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0___boxed(lean_object* v_builder_965_, lean_object* v_x_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_Http_Response_Builder_fromBytes___lam__0(v_builder_965_, v_x_966_);
lean_dec_ref(v_builder_965_);
return v_res_968_;
}
}
lean_object* l_Std_Http_Response_Builder_fromBytes(lean_object* v_builder_969_, lean_object* v_content_970_){
_start:
{
lean_object* v___f_972_; lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___f_972_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_972_, 0, v_builder_969_);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = 0;
v___x_975_ = l_Std_Http_Body_Full_ofByteArray(v_content_970_);
v___x_976_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_973_, v___x_974_, v___x_975_, v___f_972_);
return v___x_976_;
}
}
LEAN_EXPORT void l_Std_Http_Response_Builder_fromBytes_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_969_ = stack[0].m_obj;
lean_object* v_content_970_ = stack[1].m_obj;
lean_object* v_res_977_;
v_res_977_ = l_Std_Http_Response_Builder_fromBytes(v_builder_969_, v_content_970_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___boxed(lean_object* v_builder_978_, lean_object* v_content_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_Http_Response_Builder_fromBytes(v_builder_978_, v_content_979_);
return v_res_981_;
}
}
lean_object* l_Std_Http_Response_Builder_bytes(lean_object* v_builder_982_, lean_object* v_content_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_985_ = l_Std_Http_Header_Name_contentType;
v___x_986_ = lean_obj_once(&l_Std_Http_Request_Builder_bytes___closed__1, &l_Std_Http_Request_Builder_bytes___closed__1_once, _init_l_Std_Http_Request_Builder_bytes___closed__1);
v___x_987_ = l_Std_Http_Response_Builder_header(v_builder_982_, v___x_985_, v___x_986_);
v___x_988_ = l_Std_Http_Response_Builder_fromBytes(v___x_987_, v_content_983_);
return v___x_988_;
}
}
LEAN_EXPORT void l_Std_Http_Response_Builder_bytes_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_982_ = stack[0].m_obj;
lean_object* v_content_983_ = stack[1].m_obj;
lean_object* v_res_989_;
v_res_989_ = l_Std_Http_Response_Builder_bytes(v_builder_982_, v_content_983_);
stack->m_obj
 = v_res_989_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_bytes___boxed(lean_object* v_builder_990_, lean_object* v_content_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_Http_Response_Builder_bytes(v_builder_990_, v_content_991_);
return v_res_993_;
}
}
lean_object* l_Std_Http_Response_Builder_text(lean_object* v_builder_994_, lean_object* v_content_995_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_997_ = l_Std_Http_Header_Name_contentType;
v___x_998_ = lean_obj_once(&l_Std_Http_Request_Builder_text___closed__1, &l_Std_Http_Request_Builder_text___closed__1_once, _init_l_Std_Http_Request_Builder_text___closed__1);
v___x_999_ = l_Std_Http_Response_Builder_header(v_builder_994_, v___x_997_, v___x_998_);
v___x_1000_ = lean_string_to_utf8(v_content_995_);
v___x_1001_ = l_Std_Http_Response_Builder_fromBytes(v___x_999_, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT void l_Std_Http_Response_Builder_text_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_994_ = stack[0].m_obj;
lean_object* v_content_995_ = stack[1].m_obj;
lean_object* v_res_1002_;
v_res_1002_ = l_Std_Http_Response_Builder_text(v_builder_994_, v_content_995_);
stack->m_obj
 = v_res_1002_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_text___boxed(lean_object* v_builder_1003_, lean_object* v_content_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_Http_Response_Builder_text(v_builder_1003_, v_content_1004_);
lean_dec_ref(v_content_1004_);
return v_res_1006_;
}
}
lean_object* l_Std_Http_Response_Builder_json(lean_object* v_builder_1007_, lean_object* v_content_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1010_ = l_Std_Http_Header_Name_contentType;
v___x_1011_ = lean_obj_once(&l_Std_Http_Request_Builder_json___closed__1, &l_Std_Http_Request_Builder_json___closed__1_once, _init_l_Std_Http_Request_Builder_json___closed__1);
v___x_1012_ = l_Std_Http_Response_Builder_header(v_builder_1007_, v___x_1010_, v___x_1011_);
v___x_1013_ = lean_string_to_utf8(v_content_1008_);
v___x_1014_ = l_Std_Http_Response_Builder_fromBytes(v___x_1012_, v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT void l_Std_Http_Response_Builder_json_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_1007_ = stack[0].m_obj;
lean_object* v_content_1008_ = stack[1].m_obj;
lean_object* v_res_1015_;
v_res_1015_ = l_Std_Http_Response_Builder_json(v_builder_1007_, v_content_1008_);
stack->m_obj
 = v_res_1015_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_json___boxed(lean_object* v_builder_1016_, lean_object* v_content_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_Http_Response_Builder_json(v_builder_1016_, v_content_1017_);
lean_dec_ref(v_content_1017_);
return v_res_1019_;
}
}
lean_object* l_Std_Http_Response_Builder_html(lean_object* v_builder_1020_, lean_object* v_content_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1023_ = l_Std_Http_Header_Name_contentType;
v___x_1024_ = lean_obj_once(&l_Std_Http_Request_Builder_html___closed__1, &l_Std_Http_Request_Builder_html___closed__1_once, _init_l_Std_Http_Request_Builder_html___closed__1);
v___x_1025_ = l_Std_Http_Response_Builder_header(v_builder_1020_, v___x_1023_, v___x_1024_);
v___x_1026_ = lean_string_to_utf8(v_content_1021_);
v___x_1027_ = l_Std_Http_Response_Builder_fromBytes(v___x_1025_, v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT void l_Std_Http_Response_Builder_html_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_1020_ = stack[0].m_obj;
lean_object* v_content_1021_ = stack[1].m_obj;
lean_object* v_res_1028_;
v_res_1028_ = l_Std_Http_Response_Builder_html(v_builder_1020_, v_content_1021_);
stack->m_obj
 = v_res_1028_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_html___boxed(lean_object* v_builder_1029_, lean_object* v_content_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_Http_Response_Builder_html(v_builder_1029_, v_content_1030_);
lean_dec_ref(v_content_1030_);
return v_res_1032_;
}
}
lean_object* runtime_initialize_Std_Sync(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Any(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
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
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
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
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
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
res = initialize_Init_Data_ByteArray_Basic(builtin);
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

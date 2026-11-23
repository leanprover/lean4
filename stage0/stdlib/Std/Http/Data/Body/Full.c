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
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentType;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofReplayableBody(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofReplayableBody___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Request_Builder_defaultContentType(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Response_Builder_defaultContentType(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg(lean_object* v_ready_22_){
_start:
{
lean_inc(v_ready_22_);
return v_ready_22_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg___boxed(lean_object* v_ready_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___redArg(v_ready_23_);
lean_dec(v_ready_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_ready_28_){
_start:
{
lean_inc(v_ready_28_);
return v_ready_28_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_ready_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_ready_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_ready_32_);
lean_dec(v_ready_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg(lean_object* v_sent_35_){
_start:
{
lean_inc(v_sent_35_);
return v_sent_35_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg___boxed(lean_object* v_sent_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___redArg(v_sent_36_);
lean_dec(v_sent_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_sent_41_){
_start:
{
lean_inc(v_sent_41_);
return v_sent_41_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_sent_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_sent_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_sent_45_);
lean_dec(v_sent_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg(lean_object* v_closed_48_){
_start:
{
lean_inc(v_closed_48_);
return v_closed_48_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg___boxed(lean_object* v_closed_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___redArg(v_closed_49_);
lean_dec(v_closed_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_closed_54_){
_start:
{
lean_inc(v_closed_54_);
return v_closed_54_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_closed_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_State_closed_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_closed_58_);
lean_dec(v_closed_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(uint8_t v_x_61_, uint8_t v_y_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_63_ = lean_box(v_x_61_);
v___x_64_ = lean_obj_tag_nat(v___x_63_);
lean_dec(v___x_63_);
v___x_65_ = lean_box(v_y_62_);
v___x_66_ = lean_obj_tag_nat(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_nat_dec_eq(v___x_64_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq___boxed(lean_object* v_x_68_, lean_object* v_y_69_){
_start:
{
uint8_t v_x_24__boxed_70_; uint8_t v_y_25__boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_x_24__boxed_70_ = lean_unbox(v_x_68_);
v_y_25__boxed_71_ = lean_unbox(v_y_69_);
v_res_72_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(v_x_24__boxed_70_, v_y_25__boxed_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(lean_object* v_full_80_, lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
lean_dec_ref(v_full_80_);
v_a_83_ = lean_ctor_get(v_x_81_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_81_);
if (v_isSharedCheck_91_ == 0)
{
v___x_85_ = v_x_81_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v_x_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_90_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
}
else
{
lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_104_; 
v_isSharedCheck_104_ = !lean_is_exclusive(v_x_81_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_x_81_, 0);
lean_dec(v_unused_105_);
v___x_93_ = v_x_81_;
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
else
{
lean_dec(v_x_81_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_data_95_; uint8_t v___x_96_; 
v_data_95_ = lean_ctor_get(v_full_80_, 0);
lean_inc_ref(v_data_95_);
lean_dec_ref(v_full_80_);
v___x_96_ = l_ByteArray_isEmpty(v_data_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_97_ = l_Std_Http_Chunk_ofByteArray(v_data_95_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_98_);
v___x_100_ = v___x_93_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_98_);
v___x_100_ = v_reuseFailAlloc_102_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; 
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
else
{
lean_object* v___x_103_; 
lean_dec_ref(v_data_95_);
lean_del_object(v___x_93_);
v___x_103_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1));
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed(lean_object* v_full_106_, lean_object* v_x_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(v_full_106_, v_x_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(lean_object* v_a_114_, lean_object* v___f_115_, lean_object* v_x_116_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_128_; 
lean_dec_ref(v___f_115_);
v_a_120_ = lean_ctor_get(v_x_116_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_116_);
if (v_isSharedCheck_128_ == 0)
{
v___x_122_ = v_x_116_;
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v_x_116_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_127_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; 
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
}
else
{
lean_object* v_a_129_; uint8_t v___x_130_; 
v_a_129_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_a_129_);
lean_dec_ref_known(v_x_116_, 1);
v___x_130_ = lean_unbox(v_a_129_);
lean_dec(v_a_129_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_131_ = 1;
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = 0;
v___x_134_ = lean_box(v___x_131_);
v___x_135_ = lean_st_ref_swap(v_a_114_, v___x_134_);
lean_dec(v___x_135_);
v___x_136_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1));
v___x_137_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_132_, v___x_133_, v___x_136_, v___f_115_);
return v___x_137_;
}
else
{
lean_dec_ref(v___f_115_);
goto v___jp_118_;
}
}
v___jp_118_:
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1));
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed(lean_object* v_a_138_, lean_object* v___f_139_, lean_object* v_x_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(v_a_138_, v___f_139_, v_x_140_);
lean_dec(v_a_138_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(lean_object* v_full_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___f_146_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed), 3, 1);
lean_closure_set(v___f_146_, 0, v_full_143_);
lean_inc(v_a_144_);
v___f_147_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed), 4, 2);
lean_closure_set(v___f_147_, 0, v_a_144_);
lean_closure_set(v___f_147_, 1, v___f_146_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = 0;
v___x_150_ = lean_st_ref_get(v_a_144_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
v___x_153_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_148_, v___x_149_, v___x_152_, v___f_147_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed(lean_object* v_full_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v_full_154_, v_a_155_);
lean_dec(v_a_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0(lean_object* v_data_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
lean_dec_ref(v_data_158_);
v_a_161_ = lean_ctor_get(v_x_159_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v_x_159_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v_x_159_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_179_; 
v_a_170_ = lean_ctor_get(v_x_159_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_179_ == 0)
{
v___x_172_ = v_x_159_;
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v_x_159_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v_data_158_);
lean_ctor_set(v___x_174_, 1, v_a_170_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_174_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_178_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___lam__0___boxed(lean_object* v_data_180_, lean_object* v_x_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Http_Body_Full_ofByteArray___lam__0(v_data_180_, v_x_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray(lean_object* v_data_184_){
_start:
{
lean_object* v___f_186_; uint8_t v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___f_186_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_ofByteArray___lam__0___boxed), 3, 1);
lean_closure_set(v___f_186_, 0, v_data_184_);
v___x_187_ = 0;
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = 0;
v___x_190_ = lean_box(v___x_187_);
v___x_191_ = l_Std_Mutex_new___redArg(v___x_190_);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
v___x_194_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_188_, v___x_189_, v___x_193_, v___f_186_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofByteArray___boxed(lean_object* v_data_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_Http_Body_Full_ofByteArray(v_data_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___lam__0(lean_object* v_data_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_data_198_);
v_a_201_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_209_ == 0)
{
v___x_203_ = v_x_199_;
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v_x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_208_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; 
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_220_; 
v_a_210_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_220_ == 0)
{
v___x_212_ = v_x_199_;
v_isShared_213_ = v_isSharedCheck_220_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v_x_199_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_220_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_214_ = lean_string_to_utf8(v_data_198_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_a_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_215_);
v___x_217_ = v___x_212_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_215_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___lam__0___boxed(lean_object* v_data_221_, lean_object* v_x_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_Http_Body_Full_ofString___lam__0(v_data_221_, v_x_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString(lean_object* v_data_225_){
_start:
{
lean_object* v___f_227_; uint8_t v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___f_227_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_ofString___lam__0___boxed), 3, 1);
lean_closure_set(v___f_227_, 0, v_data_225_);
v___x_228_ = 0;
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = 0;
v___x_231_ = lean_box(v___x_228_);
v___x_232_ = l_Std_Mutex_new___redArg(v___x_231_);
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_229_, v___x_230_, v___x_234_, v___f_227_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_ofString___boxed(lean_object* v_data_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_Http_Body_Full_ofString(v_data_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0(lean_object* v___y_239_){
_start:
{
if (lean_obj_tag(v___y_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
v_a_240_ = lean_ctor_get(v___y_239_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___y_239_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___y_239_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___y_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_256_; 
v_a_248_ = lean_ctor_get(v___y_239_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___y_239_);
if (v_isSharedCheck_256_ == 0)
{
v___x_250_ = v___y_239_;
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___y_239_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v_fst_252_; lean_object* v___x_254_; 
v_fst_252_ = lean_ctor_get(v_a_248_, 0);
lean_inc(v_fst_252_);
lean_dec(v_a_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v_fst_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_fst_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(lean_object* v_mutex_257_, lean_object* v_x_258_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_io_basemutex_unlock(v_mutex_257_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed(lean_object* v_mutex_263_, lean_object* v_x_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(v_mutex_263_, v_x_264_);
lean_dec(v_x_264_);
lean_dec(v_mutex_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(lean_object* v_k_267_, lean_object* v_ref_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
lean_dec(v_ref_268_);
lean_dec_ref(v_k_267_);
v_a_271_ = lean_ctor_get(v_x_269_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_269_);
if (v_isSharedCheck_279_ == 0)
{
v___x_273_ = v_x_269_;
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v_x_269_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_278_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
}
else
{
lean_object* v___x_280_; 
lean_dec_ref_known(v_x_269_, 1);
v___x_280_ = lean_apply_2(v_k_267_, v_ref_268_, lean_box(0));
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed(lean_object* v_k_281_, lean_object* v_ref_282_, lean_object* v_x_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(v_k_281_, v_ref_282_, v_x_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(lean_object* v_mutex_286_, lean_object* v___f_287_){
_start:
{
lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = 0;
v___x_291_ = lean_io_basemutex_lock(v_mutex_286_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
v___x_294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_289_, v___x_290_, v___x_293_, v___f_287_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3___boxed(lean_object* v_mutex_295_, lean_object* v___f_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(v_mutex_295_, v___f_296_);
lean_dec(v_mutex_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(lean_object* v_mutex_300_, lean_object* v_k_301_){
_start:
{
lean_object* v_ref_303_; lean_object* v_mutex_304_; lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___f_307_; lean_object* v___f_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___y_313_; 
v_ref_303_ = lean_ctor_get(v_mutex_300_, 0);
lean_inc(v_ref_303_);
v_mutex_304_ = lean_ctor_get(v_mutex_300_, 1);
lean_inc_n(v_mutex_304_, 2);
lean_dec_ref(v_mutex_300_);
v___f_305_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0));
v___f_306_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_306_, 0, v_mutex_304_);
v___f_307_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_307_, 0, v_k_301_);
lean_closure_set(v___f_307_, 1, v_ref_303_);
v___f_308_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_308_, 0, v_mutex_304_);
lean_closure_set(v___f_308_, 1, v___f_307_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = 0;
v___x_311_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_308_, v___f_306_, v___x_309_, v___x_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_315_; 
v_a_315_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_311_, 1);
if (lean_obj_tag(v_a_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v_a_315_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_a_315_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v_a_315_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v_a_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
v___y_313_ = v___x_321_;
goto v___jp_312_;
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_332_; 
v_a_324_ = lean_ctor_get(v_a_315_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_a_315_);
if (v_isSharedCheck_332_ == 0)
{
v___x_326_ = v_a_315_;
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v_a_315_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_fst_328_; lean_object* v___x_330_; 
v_fst_328_ = lean_ctor_get(v_a_324_, 0);
lean_inc(v_fst_328_);
lean_dec(v_a_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v_fst_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_fst_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
v___y_313_ = v___x_330_;
goto v___jp_312_;
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_341_; 
v_a_333_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_341_ == 0)
{
v___x_335_ = v___x_311_;
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_311_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_task_map(v___f_305_, v_a_333_, v___x_309_, v___x_310_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
v___jp_312_:
{
lean_object* v___x_314_; 
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___y_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___boxed(lean_object* v_mutex_342_, lean_object* v_k_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_mutex_342_, v_k_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_mutex_348_, lean_object* v_k_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_mutex_348_, v_k_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___boxed(lean_object* v_00_u03b1_352_, lean_object* v_00_u03b2_353_, lean_object* v_mutex_354_, lean_object* v_k_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(v_00_u03b1_352_, v_00_u03b2_353_, v_mutex_354_, v_k_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv(lean_object* v_full_358_){
_start:
{
lean_object* v_state_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_state_360_ = lean_ctor_get(v_full_358_, 1);
lean_inc_ref(v_state_360_);
v___x_361_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 3, 1);
lean_closure_set(v___x_361_, 0, v_full_358_);
v___x_362_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_360_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recv___boxed(lean_object* v_full_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_Http_Body_Full_recv(v_full_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0(uint8_t v___x_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_box(v___x_366_);
v___x_370_ = lean_st_ref_swap(v___y_367_, v___x_369_);
lean_dec(v___x_370_);
v___x_371_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1));
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___lam__0___boxed(lean_object* v___x_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
uint8_t v___x_177__boxed_375_; lean_object* v_res_376_; 
v___x_177__boxed_375_ = lean_unbox(v___x_372_);
v_res_376_ = l_Std_Http_Body_Full_close___lam__0(v___x_177__boxed_375_, v___y_373_);
lean_dec(v___y_373_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close(lean_object* v_full_380_){
_start:
{
lean_object* v_state_382_; lean_object* v___f_383_; lean_object* v___x_384_; 
v_state_382_ = lean_ctor_get(v_full_380_, 1);
lean_inc_ref(v_state_382_);
lean_dec_ref(v_full_380_);
v___f_383_ = ((lean_object*)(l_Std_Http_Body_Full_close___closed__0));
v___x_384_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_382_, v___f_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_close___boxed(lean_object* v_full_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_Http_Body_Full_close(v_full_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__0(lean_object* v_x_388_){
_start:
{
uint8_t v___y_391_; 
if (lean_obj_tag(v_x_388_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_a_395_ = lean_ctor_get(v_x_388_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_388_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v_x_388_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v_x_388_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_395_);
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
else
{
lean_object* v_a_404_; uint8_t v___x_405_; uint8_t v___x_406_; uint8_t v___x_407_; 
v_a_404_ = lean_ctor_get(v_x_388_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v_x_388_, 1);
v___x_405_ = 0;
v___x_406_ = lean_unbox(v_a_404_);
lean_dec(v_a_404_);
v___x_407_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_instBEqState_beq(v___x_406_, v___x_405_);
if (v___x_407_ == 0)
{
uint8_t v___x_408_; 
v___x_408_ = 1;
v___y_391_ = v___x_408_;
goto v___jp_390_;
}
else
{
uint8_t v___x_409_; 
v___x_409_ = 0;
v___y_391_ = v___x_409_;
goto v___jp_390_;
}
}
v___jp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_box(v___y_391_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__0___boxed(lean_object* v_x_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_Http_Body_Full_isClosed___lam__0(v_x_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__1(lean_object* v___f_413_, lean_object* v___y_414_){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = 0;
v___x_418_ = lean_st_ref_get(v___y_414_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
v___x_421_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_416_, v___x_417_, v___x_420_, v___f_413_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___lam__1___boxed(lean_object* v___f_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_Http_Body_Full_isClosed___lam__1(v___f_422_, v___y_423_);
lean_dec(v___y_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed(lean_object* v_full_429_){
_start:
{
lean_object* v_state_431_; lean_object* v___f_432_; lean_object* v___x_433_; 
v_state_431_ = lean_ctor_get(v_full_429_, 1);
lean_inc_ref(v_state_431_);
lean_dec_ref(v_full_429_);
v___f_432_ = ((lean_object*)(l_Std_Http_Body_Full_isClosed___closed__1));
v___x_433_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_431_, v___f_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_isClosed___boxed(lean_object* v_full_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_Http_Body_Full_isClosed(v_full_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0(lean_object* v_data_445_, lean_object* v_x_446_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_458_; 
v_a_450_ = lean_ctor_get(v_x_446_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_446_);
if (v_isSharedCheck_458_ == 0)
{
v___x_452_ = v_x_446_;
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v_x_446_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_457_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; 
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_471_; 
v_a_459_ = lean_ctor_get(v_x_446_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_x_446_);
if (v_isSharedCheck_471_ == 0)
{
v___x_461_ = v_x_446_;
v_isShared_462_ = v_isSharedCheck_471_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v_x_446_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_471_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; 
v___x_463_ = lean_unbox(v_a_459_);
lean_dec(v_a_459_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_464_ = lean_byte_array_size(v_data_445_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_466_);
v___x_468_ = v___x_461_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_470_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
else
{
lean_del_object(v___x_461_);
goto v___jp_448_;
}
}
}
v___jp_448_:
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3));
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__0___boxed(lean_object* v_data_472_, lean_object* v_x_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_Http_Body_Full_getKnownSize___lam__0(v_data_472_, v_x_473_);
lean_dec_ref(v_data_472_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1(lean_object* v___f_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = 0;
v___x_481_ = lean_st_ref_get(v___y_477_);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
v___x_484_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_479_, v___x_480_, v___x_483_, v___f_476_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___lam__1___boxed(lean_object* v___f_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_Http_Body_Full_getKnownSize___lam__1(v___f_485_, v___y_486_);
lean_dec(v___y_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize(lean_object* v_full_489_){
_start:
{
lean_object* v_data_491_; lean_object* v_state_492_; lean_object* v___f_493_; lean_object* v___f_494_; lean_object* v___x_495_; 
v_data_491_ = lean_ctor_get(v_full_489_, 0);
lean_inc_ref(v_data_491_);
v_state_492_ = lean_ctor_get(v_full_489_, 1);
lean_inc_ref(v_state_492_);
lean_dec_ref(v_full_489_);
v___f_493_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_getKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_493_, 0, v_data_491_);
v___f_494_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_getKnownSize___lam__1___boxed), 3, 1);
lean_closure_set(v___f_494_, 0, v___f_493_);
v___x_495_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_492_, v___f_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_getKnownSize___boxed(lean_object* v_full_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Http_Body_Full_getKnownSize(v_full_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___lam__0(lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
v_a_501_ = lean_ctor_get(v_x_499_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_509_ == 0)
{
v___x_503_ = v_x_499_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v_x_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_508_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_519_; 
v_a_510_ = lean_ctor_get(v_x_499_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_519_ == 0)
{
v___x_512_ = v_x_499_;
v_isShared_513_ = v_isSharedCheck_519_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v_x_499_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_519_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v_a_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_518_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; 
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___lam__0___boxed(lean_object* v_x_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Http_Body_Full_tryRecv___lam__0(v_x_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv(lean_object* v_full_524_){
_start:
{
lean_object* v_state_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_state_526_ = lean_ctor_get(v_full_524_, 1);
lean_inc_ref(v_state_526_);
v___f_527_ = ((lean_object*)(l_Std_Http_Body_Full_tryRecv___closed__0));
v___x_528_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 3, 1);
lean_closure_set(v___x_528_, 0, v_full_524_);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = 0;
v___x_531_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_526_, v___x_528_);
v___x_532_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_529_, v___x_530_, v___x_531_, v___f_527_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_tryRecv___boxed(lean_object* v_full_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_Http_Body_Full_tryRecv(v_full_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(lean_object* v_promise_536_, lean_object* v_x_537_){
_start:
{
if (lean_obj_tag(v_x_537_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
v_a_539_ = lean_ctor_get(v_x_537_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v_x_537_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v_x_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_io_promise_resolve(v_x_537_, v_promise_536_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed(lean_object* v_promise_551_, lean_object* v_x_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(v_promise_551_, v_x_552_);
lean_dec(v_promise_551_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(lean_object* v_lose_555_, lean_object* v___y_556_, lean_object* v_full_557_, lean_object* v___f_558_, lean_object* v_x_559_){
_start:
{
if (lean_obj_tag(v_x_559_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v___f_558_);
lean_dec_ref(v_full_557_);
lean_dec_ref(v_lose_555_);
v_a_561_ = lean_ctor_get(v_x_559_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_569_ == 0)
{
v___x_563_ = v_x_559_;
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v_x_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_569_;
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
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
else
{
lean_object* v_a_570_; uint8_t v___x_571_; 
v_a_570_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v_x_559_, 1);
v___x_571_ = lean_unbox(v_a_570_);
lean_dec(v_a_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_dec_ref(v___f_558_);
lean_dec_ref(v_full_557_);
lean_inc(v___y_556_);
v___x_572_ = lean_apply_2(v_lose_555_, v___y_556_, lean_box(0));
return v___x_572_;
}
else
{
lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v_lose_555_);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = 0;
v___x_575_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v_full_557_, v___y_556_);
v___x_576_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_573_, v___x_574_, v___x_575_, v___f_558_);
return v___x_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed(lean_object* v_lose_577_, lean_object* v___y_578_, lean_object* v_full_579_, lean_object* v___f_580_, lean_object* v_x_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(v_lose_577_, v___y_578_, v_full_579_, v___f_580_, v_x_581_);
lean_dec(v___y_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(lean_object* v_full_584_, lean_object* v_w_585_, lean_object* v_lose_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_finished_589_; lean_object* v_promise_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; uint8_t v___y_597_; uint8_t v___x_605_; 
v_finished_589_ = lean_ctor_get(v_w_585_, 0);
lean_inc(v_finished_589_);
v_promise_590_ = lean_ctor_get(v_w_585_, 1);
lean_inc(v_promise_590_);
lean_dec_ref(v_w_585_);
v___f_591_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_591_, 0, v_promise_590_);
lean_inc(v___y_587_);
v___f_592_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed), 6, 4);
lean_closure_set(v___f_592_, 0, v_lose_586_);
lean_closure_set(v___f_592_, 1, v___y_587_);
lean_closure_set(v___f_592_, 2, v_full_584_);
lean_closure_set(v___f_592_, 3, v___f_591_);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = 0;
v___x_595_ = lean_st_ref_take(v_finished_589_);
v___x_605_ = lean_unbox(v___x_595_);
lean_dec(v___x_595_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; 
v___x_606_ = 1;
v___y_597_ = v___x_606_;
goto v___jp_596_;
}
else
{
v___y_597_ = v___x_594_;
goto v___jp_596_;
}
v___jp_596_:
{
uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_598_ = 1;
v___x_599_ = lean_box(v___x_598_);
v___x_600_ = lean_st_ref_put(v_finished_589_, v___x_599_);
lean_dec(v_finished_589_);
v___x_601_ = lean_box(v___y_597_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_593_, v___x_594_, v___x_603_, v___f_592_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed(lean_object* v_full_607_, lean_object* v_w_608_, lean_object* v_lose_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(v_full_607_, v_w_608_, v_lose_609_, v___y_610_);
lean_dec(v___y_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1(lean_object* v___x_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_613_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__1___boxed(lean_object* v___x_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_Http_Body_Full_recvSelector___lam__1(v___x_618_, v___y_619_);
lean_dec(v___y_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0(lean_object* v_full_624_, lean_object* v_state_625_, lean_object* v_waiter_626_){
_start:
{
lean_object* v_lose_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_lose_628_ = ((lean_object*)(l_Std_Http_Body_Full_recvSelector___lam__0___closed__0));
v___x_629_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed), 5, 3);
lean_closure_set(v___x_629_, 0, v_full_624_);
lean_closure_set(v___x_629_, 1, v_waiter_626_);
lean_closure_set(v___x_629_, 2, v_lose_628_);
v___x_630_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_625_, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__0___boxed(lean_object* v_full_631_, lean_object* v_state_632_, lean_object* v_waiter_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_Http_Body_Full_recvSelector___lam__0(v_full_631_, v_state_632_, v_waiter_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2(lean_object* v_state_636_, lean_object* v___x_637_, lean_object* v___f_638_){
_start:
{
lean_object* v___x_640_; uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = 0;
v___x_642_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_636_, v___x_637_);
v___x_643_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_640_, v___x_641_, v___x_642_, v___f_638_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__2___boxed(lean_object* v_state_644_, lean_object* v___x_645_, lean_object* v___f_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_Http_Body_Full_recvSelector___lam__2(v_state_644_, v___x_645_, v___f_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3(lean_object* v___x_649_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector___lam__3___boxed(lean_object* v___x_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_Http_Body_Full_recvSelector___lam__3(v___x_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_recvSelector(lean_object* v_full_658_){
_start:
{
lean_object* v_state_659_; lean_object* v___f_660_; lean_object* v___f_661_; lean_object* v___x_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___x_665_; 
v_state_659_ = lean_ctor_get(v_full_658_, 1);
lean_inc_ref_n(v_state_659_, 2);
v___f_660_ = ((lean_object*)(l_Std_Http_Body_Full_tryRecv___closed__0));
lean_inc_ref(v_full_658_);
v___f_661_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_recvSelector___lam__0___boxed), 4, 2);
lean_closure_set(v___f_661_, 0, v_full_658_);
lean_closure_set(v___f_661_, 1, v_state_659_);
v___x_662_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed), 3, 1);
lean_closure_set(v___x_662_, 0, v_full_658_);
v___f_663_ = lean_alloc_closure((void*)(l_Std_Http_Body_Full_recvSelector___lam__2___boxed), 4, 3);
lean_closure_set(v___f_663_, 0, v_state_659_);
lean_closure_set(v___f_663_, 1, v___x_662_);
lean_closure_set(v___f_663_, 2, v___f_660_);
v___f_664_ = ((lean_object*)(l_Std_Http_Body_Full_recvSelector___closed__0));
v___x_665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_665_, 0, v___f_663_);
lean_ctor_set(v___x_665_, 1, v___f_661_);
lean_ctor_set(v___x_665_, 2, v___f_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_resetInPlace(lean_object* v_full_669_){
_start:
{
lean_object* v_state_671_; lean_object* v___f_672_; lean_object* v___x_673_; 
v_state_671_ = lean_ctor_get(v_full_669_, 1);
lean_inc_ref(v_state_671_);
lean_dec_ref(v_full_669_);
v___f_672_ = ((lean_object*)(l_Std_Http_Body_Full_resetInPlace___closed__0));
v___x_673_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(v_state_671_, v___f_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Full_resetInPlace___boxed(lean_object* v_full_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_Http_Body_Full_resetInPlace(v_full_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instFull___lam__0(lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = ((lean_object*)(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___closed__1));
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instFull___lam__0___boxed(lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_Http_Body_instFull___lam__0(v_x_681_, v_x_682_);
lean_dec(v_x_682_);
lean_dec_ref(v_x_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseFullAny___lam__0(lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v_f_709_){
_start:
{
lean_object* v_line_710_; lean_object* v_body_711_; lean_object* v_extensions_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
v_line_710_ = lean_ctor_get(v_f_709_, 0);
v_body_711_ = lean_ctor_get(v_f_709_, 1);
v_extensions_712_ = lean_ctor_get(v_f_709_, 2);
v_isSharedCheck_720_ = !lean_is_exclusive(v_f_709_);
if (v_isSharedCheck_720_ == 0)
{
v___x_714_ = v_f_709_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_extensions_712_);
lean_inc(v_body_711_);
lean_inc(v_line_710_);
lean_dec(v_f_709_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_707_, v___x_708_, v_body_711_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_line_710_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_extensions_712_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(lean_object* v___x_725_, lean_object* v___x_726_, lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_727_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v___x_726_);
lean_dec_ref(v___x_725_);
v_a_729_ = lean_ctor_get(v_x_727_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_737_ == 0)
{
v___x_731_ = v_x_727_;
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v_x_727_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_736_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; 
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_757_; 
v_a_738_ = lean_ctor_get(v_x_727_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_757_ == 0)
{
v___x_740_ = v_x_727_;
v_isShared_741_ = v_isSharedCheck_757_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v_x_727_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_757_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_line_742_; lean_object* v_body_743_; lean_object* v_extensions_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_756_; 
v_line_742_ = lean_ctor_get(v_a_738_, 0);
v_body_743_ = lean_ctor_get(v_a_738_, 1);
v_extensions_744_ = lean_ctor_get(v_a_738_, 2);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_738_);
if (v_isSharedCheck_756_ == 0)
{
v___x_746_ = v_a_738_;
v_isShared_747_ = v_isSharedCheck_756_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_extensions_744_);
lean_inc(v_body_743_);
lean_inc(v_line_742_);
lean_dec(v_a_738_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_756_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_725_, v___x_726_, v_body_743_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_line_742_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_extensions_744_);
v___x_750_ = v_reuseFailAlloc_755_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_750_);
v___x_752_ = v___x_740_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_754_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed(lean_object* v___x_758_, lean_object* v___x_759_, lean_object* v_x_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(v___x_758_, v___x_759_, v_x_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(lean_object* v___f_763_, lean_object* v_action_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = 0;
lean_inc_ref(v___y_765_);
v___x_769_ = lean_apply_2(v_action_764_, v___y_765_, lean_box(0));
v___x_770_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_767_, v___x_768_, v___x_769_, v___f_763_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1___boxed(lean_object* v___f_771_, lean_object* v_action_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(v___f_771_, v_action_772_, v___y_773_);
lean_dec_ref(v___y_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(lean_object* v___f_782_, lean_object* v_action_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = 0;
v___x_788_ = lean_apply_1(v_action_783_, lean_box(0));
v___x_789_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_786_, v___x_787_, v___x_788_, v___f_782_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1___boxed(lean_object* v___f_790_, lean_object* v_action_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(v___f_790_, v_action_791_, v___y_792_);
lean_dec_ref(v___y_792_);
return v_res_794_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType_spec__0(lean_object* v_as_798_, size_t v_i_799_, size_t v_stop_800_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = lean_usize_dec_eq(v_i_799_, v_stop_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v_fst_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_802_ = lean_array_uget_borrowed(v_as_798_, v_i_799_);
v_fst_803_ = lean_ctor_get(v___x_802_, 0);
v___x_804_ = l_Std_Http_Header_Name_contentType;
v___x_805_ = lean_string_dec_eq(v_fst_803_, v___x_804_);
if (v___x_805_ == 0)
{
size_t v___x_806_; size_t v___x_807_; 
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_add(v_i_799_, v___x_806_);
v_i_799_ = v___x_807_;
goto _start;
}
else
{
return v___x_805_;
}
}
else
{
uint8_t v___x_809_; 
v___x_809_ = 0;
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType_spec__0___boxed(lean_object* v_as_810_, lean_object* v_i_811_, lean_object* v_stop_812_){
_start:
{
size_t v_i_boxed_813_; size_t v_stop_boxed_814_; uint8_t v_res_815_; lean_object* v_r_816_; 
v_i_boxed_813_ = lean_unbox_usize(v_i_811_);
lean_dec(v_i_811_);
v_stop_boxed_814_ = lean_unbox_usize(v_stop_812_);
lean_dec(v_stop_812_);
v_res_815_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType_spec__0(v_as_810_, v_i_boxed_813_, v_stop_boxed_814_);
lean_dec_ref(v_as_810_);
v_r_816_ = lean_box(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType(lean_object* v_headers_817_, lean_object* v_value_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_819_ = l_Std_Http_Header_Name_contentType;
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_array_get_size(v_headers_817_);
v___x_825_ = lean_nat_dec_lt(v___x_823_, v___x_824_);
if (v___x_825_ == 0)
{
goto v___jp_820_;
}
else
{
size_t v___x_826_; size_t v___x_827_; uint8_t v___x_828_; 
v___x_826_ = ((size_t)0ULL);
v___x_827_ = lean_usize_of_nat(v___x_824_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType_spec__0(v_headers_817_, v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
goto v___jp_820_;
}
else
{
lean_dec_ref(v_value_818_);
return v_headers_817_;
}
}
v___jp_820_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v_value_818_);
v___x_822_ = lean_array_push(v_headers_817_, v___x_821_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Request_Builder_defaultContentType(lean_object* v_builder_829_, lean_object* v_value_830_){
_start:
{
lean_object* v_line_831_; lean_object* v_extensions_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_851_; 
v_line_831_ = lean_ctor_get(v_builder_829_, 0);
v_extensions_832_ = lean_ctor_get(v_builder_829_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_builder_829_);
if (v_isSharedCheck_851_ == 0)
{
v___x_834_ = v_builder_829_;
v_isShared_835_ = v_isSharedCheck_851_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_extensions_832_);
lean_inc(v_line_831_);
lean_dec(v_builder_829_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_851_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
uint8_t v_method_836_; uint8_t v_version_837_; lean_object* v_uri_838_; lean_object* v_headers_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_850_; 
v_method_836_ = lean_ctor_get_uint8(v_line_831_, sizeof(void*)*2);
v_version_837_ = lean_ctor_get_uint8(v_line_831_, sizeof(void*)*2 + 1);
v_uri_838_ = lean_ctor_get(v_line_831_, 0);
v_headers_839_ = lean_ctor_get(v_line_831_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_line_831_);
if (v_isSharedCheck_850_ == 0)
{
v___x_841_ = v_line_831_;
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_headers_839_);
lean_inc(v_uri_838_);
lean_dec(v_line_831_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType(v_headers_839_, v_value_830_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_uri_838_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___x_843_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*2, v_method_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*2 + 1, v_version_837_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_845_);
v___x_847_ = v___x_834_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_extensions_832_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0(lean_object* v_builder_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_863_; 
v_a_855_ = lean_ctor_get(v_x_853_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_853_);
if (v_isSharedCheck_863_ == 0)
{
v___x_857_ = v_x_853_;
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v_x_853_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_862_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_873_; 
v_a_864_ = lean_ctor_get(v_x_853_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_853_);
if (v_isSharedCheck_873_ == 0)
{
v___x_866_ = v_x_853_;
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v_x_853_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = l_Std_Http_Request_Builder_body___redArg(v_builder_852_, v_a_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_872_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; 
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___lam__0___boxed(lean_object* v_builder_874_, lean_object* v_x_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_Http_Request_Builder_fromBytes___lam__0(v_builder_874_, v_x_875_);
lean_dec_ref(v_builder_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes(lean_object* v_builder_878_, lean_object* v_content_879_){
_start:
{
lean_object* v___f_881_; lean_object* v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___f_881_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_881_, 0, v_builder_878_);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = 0;
v___x_884_ = l_Std_Http_Body_Full_ofByteArray(v_content_879_);
v___x_885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_882_, v___x_883_, v___x_884_, v___f_881_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_fromBytes___boxed(lean_object* v_builder_886_, lean_object* v_content_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_Http_Request_Builder_fromBytes(v_builder_886_, v_content_887_);
return v_res_889_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_bytes___closed__1(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Std_Http_Request_Builder_bytes___closed__0));
v___x_892_ = l_Std_Http_Header_Value_ofString_x21(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_bytes(lean_object* v_builder_893_, lean_object* v_content_894_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_obj_once(&l_Std_Http_Request_Builder_bytes___closed__1, &l_Std_Http_Request_Builder_bytes___closed__1_once, _init_l_Std_Http_Request_Builder_bytes___closed__1);
v___x_897_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Request_Builder_defaultContentType(v_builder_893_, v___x_896_);
v___x_898_ = l_Std_Http_Request_Builder_fromBytes(v___x_897_, v_content_894_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_bytes___boxed(lean_object* v_builder_899_, lean_object* v_content_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_Http_Request_Builder_bytes(v_builder_899_, v_content_900_);
return v_res_902_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_text___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Std_Http_Request_Builder_text___closed__0));
v___x_905_ = l_Std_Http_Header_Value_ofString_x21(v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_text(lean_object* v_builder_906_, lean_object* v_content_907_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_909_ = lean_obj_once(&l_Std_Http_Request_Builder_text___closed__1, &l_Std_Http_Request_Builder_text___closed__1_once, _init_l_Std_Http_Request_Builder_text___closed__1);
v___x_910_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Request_Builder_defaultContentType(v_builder_906_, v___x_909_);
v___x_911_ = lean_string_to_utf8(v_content_907_);
v___x_912_ = l_Std_Http_Request_Builder_fromBytes(v___x_910_, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_text___boxed(lean_object* v_builder_913_, lean_object* v_content_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_Http_Request_Builder_text(v_builder_913_, v_content_914_);
return v_res_916_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_json___closed__1(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l_Std_Http_Request_Builder_json___closed__0));
v___x_919_ = l_Std_Http_Header_Value_ofString_x21(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_json(lean_object* v_builder_920_, lean_object* v_content_921_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_923_ = lean_obj_once(&l_Std_Http_Request_Builder_json___closed__1, &l_Std_Http_Request_Builder_json___closed__1_once, _init_l_Std_Http_Request_Builder_json___closed__1);
v___x_924_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Request_Builder_defaultContentType(v_builder_920_, v___x_923_);
v___x_925_ = lean_string_to_utf8(v_content_921_);
v___x_926_ = l_Std_Http_Request_Builder_fromBytes(v___x_924_, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_json___boxed(lean_object* v_builder_927_, lean_object* v_content_928_, lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Std_Http_Request_Builder_json(v_builder_927_, v_content_928_);
return v_res_930_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_html___closed__1(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l_Std_Http_Request_Builder_html___closed__0));
v___x_933_ = l_Std_Http_Header_Value_ofString_x21(v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_html(lean_object* v_builder_934_, lean_object* v_content_935_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = lean_obj_once(&l_Std_Http_Request_Builder_html___closed__1, &l_Std_Http_Request_Builder_html___closed__1_once, _init_l_Std_Http_Request_Builder_html___closed__1);
v___x_938_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Request_Builder_defaultContentType(v_builder_934_, v___x_937_);
v___x_939_ = lean_string_to_utf8(v_content_935_);
v___x_940_ = l_Std_Http_Request_Builder_fromBytes(v___x_938_, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_html___boxed(lean_object* v_builder_941_, lean_object* v_content_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_Http_Request_Builder_html(v_builder_941_, v_content_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Full_0__Std_Http_Response_Builder_defaultContentType(lean_object* v_builder_945_, lean_object* v_value_946_){
_start:
{
lean_object* v_line_947_; lean_object* v_extensions_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_966_; 
v_line_947_ = lean_ctor_get(v_builder_945_, 0);
v_extensions_948_ = lean_ctor_get(v_builder_945_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_builder_945_);
if (v_isSharedCheck_966_ == 0)
{
v___x_950_ = v_builder_945_;
v_isShared_951_ = v_isSharedCheck_966_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_extensions_948_);
lean_inc(v_line_947_);
lean_dec(v_builder_945_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_966_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_status_952_; uint8_t v_version_953_; lean_object* v_headers_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_965_; 
v_status_952_ = lean_ctor_get(v_line_947_, 0);
v_version_953_ = lean_ctor_get_uint8(v_line_947_, sizeof(void*)*2);
v_headers_954_ = lean_ctor_get(v_line_947_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_line_947_);
if (v_isSharedCheck_965_ == 0)
{
v___x_956_ = v_line_947_;
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_headers_954_);
lean_inc(v_status_952_);
lean_dec(v_line_947_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Headers_withDefaultContentType(v_headers_954_, v_value_946_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___x_958_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_status_952_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_964_, sizeof(void*)*2, v_version_953_);
v___x_960_ = v_reuseFailAlloc_964_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_960_);
v___x_962_ = v___x_950_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_extensions_948_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0(lean_object* v_builder_967_, lean_object* v_x_968_){
_start:
{
if (lean_obj_tag(v_x_968_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_a_970_ = lean_ctor_get(v_x_968_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_978_ == 0)
{
v___x_972_ = v_x_968_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v_x_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_977_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_988_; 
v_a_979_ = lean_ctor_get(v_x_968_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_988_ == 0)
{
v___x_981_ = v_x_968_;
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v_x_968_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = l_Std_Http_Response_Builder_body___redArg(v_builder_967_, v_a_979_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_987_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___lam__0___boxed(lean_object* v_builder_989_, lean_object* v_x_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_Http_Response_Builder_fromBytes___lam__0(v_builder_989_, v_x_990_);
lean_dec_ref(v_builder_989_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes(lean_object* v_builder_993_, lean_object* v_content_994_){
_start:
{
lean_object* v___f_996_; lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___f_996_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_996_, 0, v_builder_993_);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = 0;
v___x_999_ = l_Std_Http_Body_Full_ofByteArray(v_content_994_);
v___x_1000_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_997_, v___x_998_, v___x_999_, v___f_996_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_fromBytes___boxed(lean_object* v_builder_1001_, lean_object* v_content_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_Http_Response_Builder_fromBytes(v_builder_1001_, v_content_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_bytes(lean_object* v_builder_1005_, lean_object* v_content_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_obj_once(&l_Std_Http_Request_Builder_bytes___closed__1, &l_Std_Http_Request_Builder_bytes___closed__1_once, _init_l_Std_Http_Request_Builder_bytes___closed__1);
v___x_1009_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Response_Builder_defaultContentType(v_builder_1005_, v___x_1008_);
v___x_1010_ = l_Std_Http_Response_Builder_fromBytes(v___x_1009_, v_content_1006_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_bytes___boxed(lean_object* v_builder_1011_, lean_object* v_content_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_Http_Response_Builder_bytes(v_builder_1011_, v_content_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_text(lean_object* v_builder_1015_, lean_object* v_content_1016_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1018_ = lean_obj_once(&l_Std_Http_Request_Builder_text___closed__1, &l_Std_Http_Request_Builder_text___closed__1_once, _init_l_Std_Http_Request_Builder_text___closed__1);
v___x_1019_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Response_Builder_defaultContentType(v_builder_1015_, v___x_1018_);
v___x_1020_ = lean_string_to_utf8(v_content_1016_);
v___x_1021_ = l_Std_Http_Response_Builder_fromBytes(v___x_1019_, v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_text___boxed(lean_object* v_builder_1022_, lean_object* v_content_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_Http_Response_Builder_text(v_builder_1022_, v_content_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_json(lean_object* v_builder_1026_, lean_object* v_content_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = lean_obj_once(&l_Std_Http_Request_Builder_json___closed__1, &l_Std_Http_Request_Builder_json___closed__1_once, _init_l_Std_Http_Request_Builder_json___closed__1);
v___x_1030_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Response_Builder_defaultContentType(v_builder_1026_, v___x_1029_);
v___x_1031_ = lean_string_to_utf8(v_content_1027_);
v___x_1032_ = l_Std_Http_Response_Builder_fromBytes(v___x_1030_, v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_json___boxed(lean_object* v_builder_1033_, lean_object* v_content_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Std_Http_Response_Builder_json(v_builder_1033_, v_content_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_html(lean_object* v_builder_1037_, lean_object* v_content_1038_){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1040_ = lean_obj_once(&l_Std_Http_Request_Builder_html___closed__1, &l_Std_Http_Request_Builder_html___closed__1_once, _init_l_Std_Http_Request_Builder_html___closed__1);
v___x_1041_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Response_Builder_defaultContentType(v_builder_1037_, v___x_1040_);
v___x_1042_ = lean_string_to_utf8(v_content_1038_);
v___x_1043_ = l_Std_Http_Response_Builder_fromBytes(v___x_1041_, v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_html___boxed(lean_object* v_builder_1044_, lean_object* v_content_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Std_Http_Response_Builder_html(v_builder_1044_, v_content_1045_);
return v_res_1047_;
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

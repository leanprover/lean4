// Lean compiler output
// Module: Std.Http.Data.Body.Stream
// Imports: public import Std.Sync public import Std.Async public import Std.Http.Data.Request public import Std.Http.Data.Response public import Std.Http.Data.Chunk public import Std.Http.Data.Body.Basic public import Std.Http.Data.Body.Any public import Init.Data.ByteArray
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
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_object*);
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonad(lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonadFinally___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Http_Chunk_ofByteArray(lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0_value;
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
static const lean_string_object l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Http"};
static const lean_object* l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
static const lean_string_object l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Body"};
static const lean_object* l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
static const lean_string_object l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Stream"};
static const lean_object* l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_0),((lean_object*)&l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(62, 74, 245, 198, 196, 207, 141, 173)}};
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_1),((lean_object*)&l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(80, 237, 62, 34, 135, 9, 103, 192)}};
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_2),((lean_object*)&l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(35, 197, 133, 196, 74, 182, 137, 145)}};
static const lean_object* l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instImpl_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instTypeNameStream = (const lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_mkStream___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 8, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_Body_mkStream___closed__0 = (const lean_object*)&l_Std_Http_Body_mkStream___closed__0_value;
static const lean_closure_object l_Std_Http_Body_mkStream___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_mkStream___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_mkStream___closed__1 = (const lean_object*)&l_Std_Http_Body_mkStream___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream();
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_tryRecv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_tryRecv___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_tryRecv___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_tryRecv___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_tryRecvBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_tryRecvBody___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_tryRecvBody___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Stream_tryRecvBody___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_tryRecvBody___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Stream_tryRecvBody___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_tryRecvBody___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "the promise linked to the consumer was dropped"};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object*);
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "only one blocked consumer is allowed"};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2_value;
static lean_once_cell_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3;
static lean_once_cell_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value;
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value)} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_recv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_recv___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_recv___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_recv___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_close___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_close___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_close___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_isClosed___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__0_value;
static lean_once_cell_t l_Std_Http_Body_Stream_isClosed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_isClosed___closed__1;
static lean_once_cell_t l_Std_Http_Body_Stream_isClosed___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_isClosed___closed__2;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_lift___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__3 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__3_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__4 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__4_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__4_value),((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__3_value)} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__5 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__5_value;
static lean_once_cell_t l_Std_Http_Body_Stream_isClosed___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_isClosed___closed__6;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadFinally___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__7 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__7_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__8 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__8_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__4_value),((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__8_value)} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__9 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__9_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__9_value),((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__3_value)} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__10 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__10_value;
static lean_once_cell_t l_Std_Http_Body_Stream_isClosed___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_isClosed___closed__11;
static lean_once_cell_t l_Std_Http_Body_Stream_isClosed___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_isClosed___closed__12;
static lean_once_cell_t l_Std_Http_Body_Stream_isClosed___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_isClosed___closed__13;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_getKnownSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_getKnownSize___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_getKnownSize___closed__0_value;
static lean_once_cell_t l_Std_Http_Body_Stream_getKnownSize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_getKnownSize___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Stream_recvSelector___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__3___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__3___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_recvSelector___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_recvSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_recvSelector___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_recv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_instNextChunkAsync___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_Stream_instNextChunkAsync = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1_value;
static const lean_closure_object l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__2_value;
static const lean_closure_object l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__2_value),((lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1_value),((lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__3 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__3_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__3_value;
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "body exceeded maximum size of "};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " bytes"};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "channel closed"};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "only one blocked producer is allowed"};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0_value;
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1_value;
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1_value)} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2_value;
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_hasInterest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_hasInterest___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_hasInterest___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_hasInterest___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__2_value;
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__2_value)}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3_value;
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___closed__4 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__4_value;
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__4_value)}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___closed__5 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__5_value;
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__5_value)}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Body_Stream_interestSelector___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "only one blocked interest selector is allowed"};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__3___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__3___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__3___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__3___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__3___closed__2_value;
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__3___closed__2_value)}};
static const lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_interestSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_interestSelector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_interestSelector___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Stream_interestSelector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_interestSelector___lam__6___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_interestSelector___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Stream_interestSelector___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_interestSelector___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_stream___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_stream___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_stream___closed__0 = (const lean_object*)&l_Std_Http_Body_stream___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_empty___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_empty___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_empty___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_empty___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_empty___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Body_empty___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Body_empty___lam__0___closed__1_value;
static const lean_closure_object l_Std_Http_Body_empty___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_fromBytes___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_empty___lam__0___closed__1_value)} };
static const lean_object* l_Std_Http_Body_empty___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Body_empty___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_empty___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_empty___closed__0 = (const lean_object*)&l_Std_Http_Body_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_empty();
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Body_instForInAsyncStreamChunk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_forIn___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instForInAsyncStreamChunk___closed__0 = (const lean_object*)&l_Std_Http_Body_instForInAsyncStreamChunk___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instForInAsyncStreamChunk = (const lean_object*)&l_Std_Http_Body_instForInAsyncStreamChunk___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instForInContextAsyncStreamChunk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_forIn_x27___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instForInContextAsyncStreamChunk___closed__0 = (const lean_object*)&l_Std_Http_Body_instForInContextAsyncStreamChunk___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instForInContextAsyncStreamChunk = (const lean_object*)&l_Std_Http_Body_instForInContextAsyncStreamChunk___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instStream___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_close___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instStream___closed__0 = (const lean_object*)&l_Std_Http_Body_instStream___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instStream___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_isClosed___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instStream___closed__1 = (const lean_object*)&l_Std_Http_Body_instStream___closed__1_value;
static const lean_closure_object l_Std_Http_Body_instStream___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_recvSelector, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instStream___closed__2 = (const lean_object*)&l_Std_Http_Body_instStream___closed__2_value;
static const lean_closure_object l_Std_Http_Body_instStream___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_tryRecvBody___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instStream___closed__3 = (const lean_object*)&l_Std_Http_Body_instStream___closed__3_value;
static const lean_closure_object l_Std_Http_Body_instStream___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_getKnownSize___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instStream___closed__4 = (const lean_object*)&l_Std_Http_Body_instStream___closed__4_value;
static const lean_closure_object l_Std_Http_Body_instStream___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_setKnownSize___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instStream___closed__5 = (const lean_object*)&l_Std_Http_Body_instStream___closed__5_value;
static const lean_ctor_object l_Std_Http_Body_instStream___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value),((lean_object*)&l_Std_Http_Body_instStream___closed__0_value),((lean_object*)&l_Std_Http_Body_instStream___closed__1_value),((lean_object*)&l_Std_Http_Body_instStream___closed__2_value),((lean_object*)&l_Std_Http_Body_instStream___closed__3_value),((lean_object*)&l_Std_Http_Body_instStream___closed__4_value),((lean_object*)&l_Std_Http_Body_instStream___closed__5_value)}};
static const lean_object* l_Std_Http_Body_instStream___closed__6 = (const lean_object*)&l_Std_Http_Body_instStream___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instStream = (const lean_object*)&l_Std_Http_Body_instStream___closed__6_value;
static const lean_closure_object l_Std_Http_Body_instCoeStreamAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Any_ofBody, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instStream___closed__6_value)} };
static const lean_object* l_Std_Http_Body_instCoeStreamAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeStreamAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeStreamAny = (const lean_object*)&l_Std_Http_Body_instCoeStreamAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeResponseStreamAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeResponseStreamAny___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instStream___closed__6_value)} };
static const lean_object* l_Std_Http_Body_instCoeResponseStreamAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeResponseStreamAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeResponseStreamAny = (const lean_object*)&l_Std_Http_Body_instCoeResponseStreamAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instStream___closed__6_value)} };
static const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__1 = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny = (const lean_object*)&l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_promise_8_; lean_object* v___x_9_; 
v_promise_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_promise_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_promise_8_);
return v___x_9_;
}
else
{
lean_object* v_finished_10_; lean_object* v___x_11_; 
v_finished_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_finished_10_);
lean_dec_ref(v_t_6_);
v___x_11_ = lean_apply_1(v_k_7_, v_finished_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim___redArg(lean_object* v_t_24_, lean_object* v_normal_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_24_, v_normal_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_normal_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_28_, v_normal_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim___redArg(lean_object* v_t_32_, lean_object* v_select_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_32_, v_select_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_select_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_36_, v_select_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(lean_object* v_x_40_, lean_object* v_w_41_, lean_object* v_lose_42_){
_start:
{
lean_object* v_finished_44_; lean_object* v_promise_45_; lean_object* v___x_46_; uint8_t v___y_48_; uint8_t v___x_56_; 
v_finished_44_ = lean_ctor_get(v_w_41_, 0);
v_promise_45_ = lean_ctor_get(v_w_41_, 1);
v___x_46_ = lean_st_ref_take(v_finished_44_);
v___x_56_ = lean_unbox(v___x_46_);
lean_dec(v___x_46_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
v___x_57_ = 1;
v___y_48_ = v___x_57_;
goto v___jp_47_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = 0;
v___y_48_ = v___x_58_;
goto v___jp_47_;
}
v___jp_47_:
{
uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = 1;
v___x_50_ = lean_box(v___x_49_);
v___x_51_ = lean_st_ref_set(v_finished_44_, v___x_50_);
if (v___y_48_ == 0)
{
lean_object* v___x_52_; uint8_t v___x_53_; 
lean_dec(v_x_40_);
v___x_52_ = lean_apply_1(v_lose_42_, lean_box(0));
v___x_53_ = lean_unbox(v___x_52_);
return v___x_53_;
}
else
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec_ref(v_lose_42_);
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v_x_40_);
v___x_55_ = lean_io_promise_resolve(v___x_54_, v_promise_45_);
return v___y_48_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0___boxed(lean_object* v_x_59_, lean_object* v_w_60_, lean_object* v_lose_61_, lean_object* v___y_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_59_, v_w_60_, v_lose_61_);
lean_dec_ref(v_w_60_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(uint8_t v___x_65_){
_start:
{
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed(lean_object* v___x_67_, lean_object* v___y_68_){
_start:
{
uint8_t v___x_390__boxed_69_; uint8_t v_res_70_; lean_object* v_r_71_; 
v___x_390__boxed_69_ = lean_unbox(v___x_67_);
v_res_70_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(v___x_390__boxed_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(lean_object* v_c_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_c_75_) == 0)
{
lean_object* v_promise_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_promise_78_ = lean_ctor_get(v_c_75_, 0);
v___x_79_ = lean_io_promise_resolve(v_x_76_, v_promise_78_);
v___x_80_ = 1;
return v___x_80_;
}
else
{
lean_object* v_finished_81_; lean_object* v_lose_82_; uint8_t v___x_83_; 
v_finished_81_ = lean_ctor_get(v_c_75_, 0);
v_lose_82_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_83_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_76_, v_finished_81_, v_lose_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed(lean_object* v_c_84_, lean_object* v_x_85_, lean_object* v_a_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_c_84_, v_x_85_);
lean_dec_ref(v_c_84_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(uint8_t v_x_89_, lean_object* v_w_90_, lean_object* v_lose_91_){
_start:
{
lean_object* v_finished_93_; lean_object* v_promise_94_; lean_object* v___x_95_; uint8_t v___y_97_; uint8_t v___x_106_; 
v_finished_93_ = lean_ctor_get(v_w_90_, 0);
v_promise_94_ = lean_ctor_get(v_w_90_, 1);
v___x_95_ = lean_st_ref_take(v_finished_93_);
v___x_106_ = lean_unbox(v___x_95_);
lean_dec(v___x_95_);
if (v___x_106_ == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 1;
v___y_97_ = v___x_107_;
goto v___jp_96_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = 0;
v___y_97_ = v___x_108_;
goto v___jp_96_;
}
v___jp_96_:
{
uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = 1;
v___x_99_ = lean_box(v___x_98_);
v___x_100_ = lean_st_ref_set(v_finished_93_, v___x_99_);
if (v___y_97_ == 0)
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_apply_1(v_lose_91_, lean_box(0));
v___x_102_ = lean_unbox(v___x_101_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec_ref(v_lose_91_);
v___x_103_ = lean_box(v_x_89_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
v___x_105_ = lean_io_promise_resolve(v___x_104_, v_promise_94_);
return v___y_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0___boxed(lean_object* v_x_109_, lean_object* v_w_110_, lean_object* v_lose_111_, lean_object* v___y_112_){
_start:
{
uint8_t v_x_boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_x_boxed_113_ = lean_unbox(v_x_109_);
v_res_114_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_boxed_113_, v_w_110_, v_lose_111_);
lean_dec_ref(v_w_110_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(lean_object* v_waiter_116_, uint8_t v_x_117_){
_start:
{
lean_object* v_lose_119_; uint8_t v___x_120_; 
v_lose_119_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_120_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_117_, v_waiter_116_, v_lose_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed(lean_object* v_waiter_121_, lean_object* v_x_122_, lean_object* v_a_123_){
_start:
{
uint8_t v_x_boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_x_boxed_124_ = lean_unbox(v_x_122_);
v_res_125_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_waiter_121_, v_x_boxed_124_);
lean_dec_ref(v_waiter_121_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0(lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_148_; 
v_a_140_ = lean_ctor_get(v_x_138_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_148_ == 0)
{
v___x_142_ = v_x_138_;
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v_x_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_147_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; 
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_a_149_ = lean_ctor_get(v_x_138_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v_x_138_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v_x_138_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_156_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0___boxed(lean_object* v_x_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_Http_Body_mkStream___lam__0(v_x_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream(){
_start:
{
uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_166_ = 0;
v___x_167_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__0));
v___x_168_ = l_Std_Mutex_new___redArg(v___x_167_);
v___f_169_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__1));
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_172_, v___x_166_, v___x_171_, v___f_169_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___boxed(lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Http_Body_mkStream();
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object* v_knownSize_176_, lean_object* v_chunk_177_){
_start:
{
if (lean_obj_tag(v_knownSize_176_) == 1)
{
lean_object* v_val_178_; 
v_val_178_ = lean_ctor_get(v_knownSize_176_, 0);
lean_inc(v_val_178_);
if (lean_obj_tag(v_val_178_) == 1)
{
lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_196_; 
v_isSharedCheck_196_ = !lean_is_exclusive(v_knownSize_176_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v_knownSize_176_, 0);
lean_dec(v_unused_197_);
v___x_180_ = v_knownSize_176_;
v_isShared_181_ = v_isSharedCheck_196_;
goto v_resetjp_179_;
}
else
{
lean_dec(v_knownSize_176_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_196_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_n_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_195_; 
v_n_182_ = lean_ctor_get(v_val_178_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v_val_178_);
if (v_isSharedCheck_195_ == 0)
{
v___x_184_ = v_val_178_;
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_n_182_);
lean_dec(v_val_178_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_data_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v_data_186_ = lean_ctor_get(v_chunk_177_, 0);
v___x_187_ = lean_byte_array_size(v_data_186_);
v___x_188_ = lean_nat_sub(v_n_182_, v___x_187_);
lean_dec(v_n_182_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_188_);
v___x_190_ = v___x_184_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_192_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_190_);
v___x_192_ = v___x_180_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
else
{
lean_dec(v_val_178_);
return v_knownSize_176_;
}
}
else
{
return v_knownSize_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object* v_knownSize_198_, lean_object* v_chunk_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_198_, v_chunk_199_);
lean_dec_ref(v_chunk_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object* v_pendingProducer_201_, lean_object* v_pendingConsumer_202_, uint8_t v_closed_203_, lean_object* v_knownSize_204_, lean_object* v_pendingIncompleteChunk_205_, lean_object* v_inst_206_, lean_object* v_interestWaiter_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_209_, 0, v_pendingProducer_201_);
lean_ctor_set(v___x_209_, 1, v_pendingConsumer_202_);
lean_ctor_set(v___x_209_, 2, v_interestWaiter_207_);
lean_ctor_set(v___x_209_, 3, v_knownSize_204_);
lean_ctor_set(v___x_209_, 4, v_pendingIncompleteChunk_205_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*5, v_closed_203_);
lean_inc(v___y_208_);
v___x_210_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_210_, 0, lean_box(0));
lean_closure_set(v___x_210_, 1, lean_box(0));
lean_closure_set(v___x_210_, 2, v___y_208_);
lean_closure_set(v___x_210_, 3, v___x_209_);
v___x_211_ = lean_apply_2(v_inst_206_, lean_box(0), v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object* v_pendingProducer_212_, lean_object* v_pendingConsumer_213_, lean_object* v_closed_214_, lean_object* v_knownSize_215_, lean_object* v_pendingIncompleteChunk_216_, lean_object* v_inst_217_, lean_object* v_interestWaiter_218_, lean_object* v___y_219_){
_start:
{
uint8_t v_closed_boxed_220_; lean_object* v_res_221_; 
v_closed_boxed_220_ = lean_unbox(v_closed_214_);
v_res_221_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(v_pendingProducer_212_, v_pendingConsumer_213_, v_closed_boxed_220_, v_knownSize_215_, v_pendingIncompleteChunk_216_, v_inst_217_, v_interestWaiter_218_, v___y_219_);
lean_dec(v___y_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object* v___f_222_, lean_object* v___y_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; 
lean_inc(v___y_223_);
v___x_225_ = lean_apply_2(v___f_222_, v_a_224_, v___y_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object* v___f_226_, lean_object* v___y_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(v___f_226_, v___y_227_, v_a_228_);
lean_dec(v___y_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object* v_toApplicative_230_, lean_object* v_interestWaiter_231_, lean_object* v_toBind_232_, lean_object* v___f_233_, lean_object* v___f_234_, uint8_t v_a_235_){
_start:
{
if (v_a_235_ == 0)
{
lean_object* v_toPure_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v___f_234_);
v_toPure_236_ = lean_ctor_get(v_toApplicative_230_, 1);
lean_inc(v_toPure_236_);
lean_dec_ref(v_toApplicative_230_);
v___x_237_ = lean_apply_2(v_toPure_236_, lean_box(0), v_interestWaiter_231_);
v___x_238_ = lean_apply_4(v_toBind_232_, lean_box(0), lean_box(0), v___x_237_, v___f_233_);
return v___x_238_;
}
else
{
lean_object* v_toPure_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v___f_233_);
lean_dec(v_interestWaiter_231_);
v_toPure_239_ = lean_ctor_get(v_toApplicative_230_, 1);
lean_inc(v_toPure_239_);
lean_dec_ref(v_toApplicative_230_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_apply_2(v_toPure_239_, lean_box(0), v___x_240_);
v___x_242_ = lean_apply_4(v_toBind_232_, lean_box(0), lean_box(0), v___x_241_, v___f_234_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object* v_toApplicative_243_, lean_object* v_interestWaiter_244_, lean_object* v_toBind_245_, lean_object* v___f_246_, lean_object* v___f_247_, lean_object* v_a_248_){
_start:
{
uint8_t v_a_boxed_249_; lean_object* v_res_250_; 
v_a_boxed_249_ = lean_unbox(v_a_248_);
v_res_250_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(v_toApplicative_243_, v_interestWaiter_244_, v_toBind_245_, v___f_246_, v___f_247_, v_a_boxed_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object* v_pendingProducer_251_, uint8_t v_closed_252_, lean_object* v_knownSize_253_, lean_object* v_pendingIncompleteChunk_254_, lean_object* v_inst_255_, lean_object* v_interestWaiter_256_, lean_object* v_toApplicative_257_, lean_object* v_toBind_258_, lean_object* v_pendingConsumer_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___f_262_; 
v___x_261_ = lean_box(v_closed_252_);
lean_inc(v_inst_255_);
v___f_262_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_262_, 0, v_pendingProducer_251_);
lean_closure_set(v___f_262_, 1, v_pendingConsumer_259_);
lean_closure_set(v___f_262_, 2, v___x_261_);
lean_closure_set(v___f_262_, 3, v_knownSize_253_);
lean_closure_set(v___f_262_, 4, v_pendingIncompleteChunk_254_);
lean_closure_set(v___f_262_, 5, v_inst_255_);
if (lean_obj_tag(v_interestWaiter_256_) == 0)
{
lean_object* v_toPure_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_inst_255_);
v_toPure_263_ = lean_ctor_get(v_toApplicative_257_, 1);
lean_inc(v_toPure_263_);
lean_dec_ref(v_toApplicative_257_);
lean_inc(v___y_260_);
v___f_264_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_264_, 0, v___f_262_);
lean_closure_set(v___f_264_, 1, v___y_260_);
v___x_265_ = lean_apply_2(v_toPure_263_, lean_box(0), v_interestWaiter_256_);
v___x_266_ = lean_apply_4(v_toBind_258_, lean_box(0), lean_box(0), v___x_265_, v___f_264_);
return v___x_266_;
}
else
{
lean_object* v_val_267_; lean_object* v_finished_268_; lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_val_267_ = lean_ctor_get(v_interestWaiter_256_, 0);
v_finished_268_ = lean_ctor_get(v_val_267_, 0);
lean_inc(v_finished_268_);
lean_inc(v___y_260_);
v___f_269_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_269_, 0, v___f_262_);
lean_closure_set(v___f_269_, 1, v___y_260_);
lean_inc_ref(v___f_269_);
lean_inc(v_toBind_258_);
v___f_270_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_270_, 0, v_toApplicative_257_);
lean_closure_set(v___f_270_, 1, v_interestWaiter_256_);
lean_closure_set(v___f_270_, 2, v_toBind_258_);
lean_closure_set(v___f_270_, 3, v___f_269_);
lean_closure_set(v___f_270_, 4, v___f_269_);
v___x_271_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_271_, 0, lean_box(0));
lean_closure_set(v___x_271_, 1, lean_box(0));
lean_closure_set(v___x_271_, 2, v_finished_268_);
v___x_272_ = lean_apply_2(v_inst_255_, lean_box(0), v___x_271_);
v___x_273_ = lean_apply_4(v_toBind_258_, lean_box(0), lean_box(0), v___x_272_, v___f_270_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object* v_pendingProducer_274_, lean_object* v_closed_275_, lean_object* v_knownSize_276_, lean_object* v_pendingIncompleteChunk_277_, lean_object* v_inst_278_, lean_object* v_interestWaiter_279_, lean_object* v_toApplicative_280_, lean_object* v_toBind_281_, lean_object* v_pendingConsumer_282_, lean_object* v___y_283_){
_start:
{
uint8_t v_closed_boxed_284_; lean_object* v_res_285_; 
v_closed_boxed_284_ = lean_unbox(v_closed_275_);
v_res_285_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(v_pendingProducer_274_, v_closed_boxed_284_, v_knownSize_276_, v_pendingIncompleteChunk_277_, v_inst_278_, v_interestWaiter_279_, v_toApplicative_280_, v_toBind_281_, v_pendingConsumer_282_, v___y_283_);
lean_dec(v___y_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(lean_object* v___f_286_, lean_object* v___y_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_289_; 
lean_inc(v___y_287_);
v___x_289_ = lean_apply_2(v___f_286_, v_a_288_, v___y_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(lean_object* v___f_290_, lean_object* v___y_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(v___f_290_, v___y_291_, v_a_292_);
lean_dec(v___y_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(lean_object* v___f_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_297_; 
lean_inc(v_a_295_);
v___x_297_ = lean_apply_2(v___f_294_, v_a_296_, v_a_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(lean_object* v___f_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(v___f_298_, v_a_299_, v_a_300_);
lean_dec(v_a_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(lean_object* v_toApplicative_302_, lean_object* v_pendingConsumer_303_, lean_object* v_toBind_304_, lean_object* v___f_305_, lean_object* v___f_306_, uint8_t v_a_307_){
_start:
{
if (v_a_307_ == 0)
{
lean_object* v_toPure_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v___f_306_);
v_toPure_308_ = lean_ctor_get(v_toApplicative_302_, 1);
lean_inc(v_toPure_308_);
lean_dec_ref(v_toApplicative_302_);
v___x_309_ = lean_apply_2(v_toPure_308_, lean_box(0), v_pendingConsumer_303_);
v___x_310_ = lean_apply_4(v_toBind_304_, lean_box(0), lean_box(0), v___x_309_, v___f_305_);
return v___x_310_;
}
else
{
lean_object* v_toPure_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v___f_305_);
lean_dec(v_pendingConsumer_303_);
v_toPure_311_ = lean_ctor_get(v_toApplicative_302_, 1);
lean_inc(v_toPure_311_);
lean_dec_ref(v_toApplicative_302_);
v___x_312_ = lean_box(0);
v___x_313_ = lean_apply_2(v_toPure_311_, lean_box(0), v___x_312_);
v___x_314_ = lean_apply_4(v_toBind_304_, lean_box(0), lean_box(0), v___x_313_, v___f_306_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(lean_object* v_toApplicative_315_, lean_object* v_pendingConsumer_316_, lean_object* v_toBind_317_, lean_object* v___f_318_, lean_object* v___f_319_, lean_object* v_a_320_){
_start:
{
uint8_t v_a_boxed_321_; lean_object* v_res_322_; 
v_a_boxed_321_ = lean_unbox(v_a_320_);
v_res_322_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(v_toApplicative_315_, v_pendingConsumer_316_, v_toBind_317_, v___f_318_, v___f_319_, v_a_boxed_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(lean_object* v_inst_323_, lean_object* v_toApplicative_324_, lean_object* v_toBind_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_pendingProducer_328_; lean_object* v_pendingConsumer_329_; lean_object* v_interestWaiter_330_; uint8_t v_closed_331_; lean_object* v_knownSize_332_; lean_object* v_pendingIncompleteChunk_333_; lean_object* v___x_334_; lean_object* v___f_335_; lean_object* v___y_337_; 
v_pendingProducer_328_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_pendingProducer_328_);
v_pendingConsumer_329_ = lean_ctor_get(v_a_327_, 1);
lean_inc(v_pendingConsumer_329_);
v_interestWaiter_330_ = lean_ctor_get(v_a_327_, 2);
lean_inc(v_interestWaiter_330_);
v_closed_331_ = lean_ctor_get_uint8(v_a_327_, sizeof(void*)*5);
v_knownSize_332_ = lean_ctor_get(v_a_327_, 3);
lean_inc(v_knownSize_332_);
v_pendingIncompleteChunk_333_ = lean_ctor_get(v_a_327_, 4);
lean_inc(v_pendingIncompleteChunk_333_);
lean_dec_ref(v_a_327_);
v___x_334_ = lean_box(v_closed_331_);
lean_inc(v_toBind_325_);
lean_inc_ref(v_toApplicative_324_);
lean_inc(v_inst_323_);
v___f_335_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed), 10, 8);
lean_closure_set(v___f_335_, 0, v_pendingProducer_328_);
lean_closure_set(v___f_335_, 1, v___x_334_);
lean_closure_set(v___f_335_, 2, v_knownSize_332_);
lean_closure_set(v___f_335_, 3, v_pendingIncompleteChunk_333_);
lean_closure_set(v___f_335_, 4, v_inst_323_);
lean_closure_set(v___f_335_, 5, v_interestWaiter_330_);
lean_closure_set(v___f_335_, 6, v_toApplicative_324_);
lean_closure_set(v___f_335_, 7, v_toBind_325_);
if (lean_obj_tag(v_pendingConsumer_329_) == 1)
{
lean_object* v_val_342_; 
v_val_342_ = lean_ctor_get(v_pendingConsumer_329_, 0);
if (lean_obj_tag(v_val_342_) == 1)
{
lean_object* v_finished_343_; lean_object* v_finished_344_; lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_finished_343_ = lean_ctor_get(v_val_342_, 0);
v_finished_344_ = lean_ctor_get(v_finished_343_, 0);
lean_inc(v_finished_344_);
lean_inc(v_a_326_);
v___f_345_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_345_, 0, v___f_335_);
lean_closure_set(v___f_345_, 1, v_a_326_);
lean_inc_ref(v___f_345_);
lean_inc(v_toBind_325_);
v___f_346_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_346_, 0, v_toApplicative_324_);
lean_closure_set(v___f_346_, 1, v_pendingConsumer_329_);
lean_closure_set(v___f_346_, 2, v_toBind_325_);
lean_closure_set(v___f_346_, 3, v___f_345_);
lean_closure_set(v___f_346_, 4, v___f_345_);
v___x_347_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_347_, 0, lean_box(0));
lean_closure_set(v___x_347_, 1, lean_box(0));
lean_closure_set(v___x_347_, 2, v_finished_344_);
v___x_348_ = lean_apply_2(v_inst_323_, lean_box(0), v___x_347_);
v___x_349_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_348_, v___f_346_);
return v___x_349_;
}
else
{
lean_dec(v_inst_323_);
v___y_337_ = v_a_326_;
goto v___jp_336_;
}
}
else
{
lean_dec(v_inst_323_);
v___y_337_ = v_a_326_;
goto v___jp_336_;
}
v___jp_336_:
{
lean_object* v_toPure_338_; lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_toPure_338_ = lean_ctor_get(v_toApplicative_324_, 1);
lean_inc(v_toPure_338_);
lean_dec_ref(v_toApplicative_324_);
lean_inc(v___y_337_);
v___f_339_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_339_, 0, v___f_335_);
lean_closure_set(v___f_339_, 1, v___y_337_);
v___x_340_ = lean_apply_2(v_toPure_338_, lean_box(0), v_pendingConsumer_329_);
v___x_341_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_340_, v___f_339_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(lean_object* v_inst_350_, lean_object* v_toApplicative_351_, lean_object* v_toBind_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(v_inst_350_, v_toApplicative_351_, v_toBind_352_, v_a_353_, v_a_354_);
lean_dec(v_a_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_toApplicative_359_; lean_object* v_toBind_360_; lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_toApplicative_359_ = lean_ctor_get(v_inst_356_, 0);
lean_inc_ref(v_toApplicative_359_);
v_toBind_360_ = lean_ctor_get(v_inst_356_, 1);
lean_inc_n(v_toBind_360_, 2);
lean_dec_ref(v_inst_356_);
lean_inc_n(v_a_358_, 2);
lean_inc(v_inst_357_);
v___f_361_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_361_, 0, v_inst_357_);
lean_closure_set(v___f_361_, 1, v_toApplicative_359_);
lean_closure_set(v___f_361_, 2, v_toBind_360_);
lean_closure_set(v___f_361_, 3, v_a_358_);
v___x_362_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_362_, 0, lean_box(0));
lean_closure_set(v___x_362_, 1, lean_box(0));
lean_closure_set(v___x_362_, 2, v_a_358_);
v___x_363_ = lean_apply_2(v_inst_357_, lean_box(0), v___x_362_);
v___x_364_ = lean_apply_4(v_toBind_360_, lean_box(0), lean_box(0), v___x_363_, v___f_361_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_365_, v_inst_366_, v_a_367_);
lean_dec(v_a_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(lean_object* v_m_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_370_, v_inst_371_, v_a_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(lean_object* v_m_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(v_m_374_, v_inst_375_, v_inst_376_, v_a_377_);
lean_dec(v_a_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object* v_pendingProducer_379_, lean_object* v_pendingConsumer_380_, uint8_t v_closed_381_, lean_object* v_knownSize_382_, lean_object* v_pendingIncompleteChunk_383_, lean_object* v_a_384_, lean_object* v_inst_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_box(0);
v___x_388_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_388_, 0, v_pendingProducer_379_);
lean_ctor_set(v___x_388_, 1, v_pendingConsumer_380_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
lean_ctor_set(v___x_388_, 3, v_knownSize_382_);
lean_ctor_set(v___x_388_, 4, v_pendingIncompleteChunk_383_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*5, v_closed_381_);
lean_inc(v_a_384_);
v___x_389_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_389_, 0, lean_box(0));
lean_closure_set(v___x_389_, 1, lean_box(0));
lean_closure_set(v___x_389_, 2, v_a_384_);
lean_closure_set(v___x_389_, 3, v___x_388_);
v___x_390_ = lean_apply_2(v_inst_385_, lean_box(0), v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object* v_pendingProducer_391_, lean_object* v_pendingConsumer_392_, lean_object* v_closed_393_, lean_object* v_knownSize_394_, lean_object* v_pendingIncompleteChunk_395_, lean_object* v_a_396_, lean_object* v_inst_397_, lean_object* v_a_398_){
_start:
{
uint8_t v_closed_boxed_399_; lean_object* v_res_400_; 
v_closed_boxed_399_ = lean_unbox(v_closed_393_);
v_res_400_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(v_pendingProducer_391_, v_pendingConsumer_392_, v_closed_boxed_399_, v_knownSize_394_, v_pendingIncompleteChunk_395_, v_a_396_, v_inst_397_, v_a_398_);
lean_dec(v_a_396_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(lean_object* v_toApplicative_401_, lean_object* v_a_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_toBind_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_interestWaiter_407_; 
v_interestWaiter_407_ = lean_ctor_get(v_a_406_, 2);
lean_inc(v_interestWaiter_407_);
if (lean_obj_tag(v_interestWaiter_407_) == 1)
{
lean_object* v_toFunctor_408_; lean_object* v_pendingProducer_409_; lean_object* v_pendingConsumer_410_; uint8_t v_closed_411_; lean_object* v_knownSize_412_; lean_object* v_pendingIncompleteChunk_413_; lean_object* v_val_414_; lean_object* v_mapConst_415_; lean_object* v___x_416_; lean_object* v___f_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_toFunctor_408_ = lean_ctor_get(v_toApplicative_401_, 0);
lean_inc_ref(v_toFunctor_408_);
lean_dec_ref(v_toApplicative_401_);
v_pendingProducer_409_ = lean_ctor_get(v_a_406_, 0);
lean_inc(v_pendingProducer_409_);
v_pendingConsumer_410_ = lean_ctor_get(v_a_406_, 1);
lean_inc(v_pendingConsumer_410_);
v_closed_411_ = lean_ctor_get_uint8(v_a_406_, sizeof(void*)*5);
v_knownSize_412_ = lean_ctor_get(v_a_406_, 3);
lean_inc(v_knownSize_412_);
v_pendingIncompleteChunk_413_ = lean_ctor_get(v_a_406_, 4);
lean_inc(v_pendingIncompleteChunk_413_);
lean_dec_ref(v_a_406_);
v_val_414_ = lean_ctor_get(v_interestWaiter_407_, 0);
lean_inc(v_val_414_);
lean_dec_ref(v_interestWaiter_407_);
v_mapConst_415_ = lean_ctor_get(v_toFunctor_408_, 1);
lean_inc(v_mapConst_415_);
lean_dec_ref(v_toFunctor_408_);
v___x_416_ = lean_box(v_closed_411_);
lean_inc(v_a_402_);
v___f_417_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_417_, 0, v_pendingProducer_409_);
lean_closure_set(v___f_417_, 1, v_pendingConsumer_410_);
lean_closure_set(v___f_417_, 2, v___x_416_);
lean_closure_set(v___f_417_, 3, v_knownSize_412_);
lean_closure_set(v___f_417_, 4, v_pendingIncompleteChunk_413_);
lean_closure_set(v___f_417_, 5, v_a_402_);
lean_closure_set(v___f_417_, 6, v_inst_403_);
v___x_418_ = 1;
v___x_419_ = lean_box(v___x_418_);
v___x_420_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_420_, 0, v_val_414_);
lean_closure_set(v___x_420_, 1, v___x_419_);
v___x_421_ = lean_apply_2(v_inst_404_, lean_box(0), v___x_420_);
v___x_422_ = lean_box(0);
v___x_423_ = lean_apply_4(v_mapConst_415_, lean_box(0), lean_box(0), v___x_422_, v___x_421_);
v___x_424_ = lean_apply_4(v_toBind_405_, lean_box(0), lean_box(0), v___x_423_, v___f_417_);
return v___x_424_;
}
else
{
lean_object* v_toPure_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v_interestWaiter_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_toBind_405_);
lean_dec(v_inst_404_);
lean_dec(v_inst_403_);
v_toPure_425_ = lean_ctor_get(v_toApplicative_401_, 1);
lean_inc(v_toPure_425_);
lean_dec_ref(v_toApplicative_401_);
v___x_426_ = lean_box(0);
v___x_427_ = lean_apply_2(v_toPure_425_, lean_box(0), v___x_426_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(lean_object* v_toApplicative_428_, lean_object* v_a_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_toBind_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(v_toApplicative_428_, v_a_429_, v_inst_430_, v_inst_431_, v_toBind_432_, v_a_433_);
lean_dec(v_a_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_toApplicative_439_; lean_object* v_toBind_440_; lean_object* v___f_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_toApplicative_439_ = lean_ctor_get(v_inst_435_, 0);
lean_inc_ref(v_toApplicative_439_);
v_toBind_440_ = lean_ctor_get(v_inst_435_, 1);
lean_inc_n(v_toBind_440_, 2);
lean_dec_ref(v_inst_435_);
lean_inc(v_inst_436_);
lean_inc_n(v_a_438_, 2);
v___f_441_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_441_, 0, v_toApplicative_439_);
lean_closure_set(v___f_441_, 1, v_a_438_);
lean_closure_set(v___f_441_, 2, v_inst_436_);
lean_closure_set(v___f_441_, 3, v_inst_437_);
lean_closure_set(v___f_441_, 4, v_toBind_440_);
v___x_442_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_442_, 0, lean_box(0));
lean_closure_set(v___x_442_, 1, lean_box(0));
lean_closure_set(v___x_442_, 2, v_a_438_);
v___x_443_ = lean_apply_2(v_inst_436_, lean_box(0), v___x_442_);
v___x_444_ = lean_apply_4(v_toBind_440_, lean_box(0), lean_box(0), v___x_443_, v___f_441_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_445_, v_inst_446_, v_inst_447_, v_a_448_);
lean_dec(v_a_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(lean_object* v_m_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_451_, v_inst_452_, v_inst_453_, v_a_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(lean_object* v_m_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(v_m_456_, v_inst_457_, v_inst_458_, v_inst_459_, v_a_460_);
lean_dec(v_a_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_462_, lean_object* v_a_463_){
_start:
{
uint8_t v___y_465_; lean_object* v_pendingProducer_469_; 
v_pendingProducer_469_ = lean_ctor_get(v_a_463_, 0);
if (lean_obj_tag(v_pendingProducer_469_) == 0)
{
uint8_t v_closed_470_; 
v_closed_470_ = lean_ctor_get_uint8(v_a_463_, sizeof(void*)*5);
v___y_465_ = v_closed_470_;
goto v___jp_464_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = 1;
v___y_465_ = v___x_471_;
goto v___jp_464_;
}
v___jp_464_:
{
lean_object* v_toPure_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_toPure_466_ = lean_ctor_get(v_toApplicative_462_, 1);
lean_inc(v_toPure_466_);
lean_dec_ref(v_toApplicative_462_);
v___x_467_ = lean_box(v___y_465_);
v___x_468_ = lean_apply_2(v_toPure_466_, lean_box(0), v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(v_toApplicative_472_, v_a_473_);
lean_dec_ref(v_a_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_toApplicative_478_; lean_object* v_toBind_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_toApplicative_478_ = lean_ctor_get(v_inst_475_, 0);
lean_inc_ref(v_toApplicative_478_);
v_toBind_479_ = lean_ctor_get(v_inst_475_, 1);
lean_inc(v_toBind_479_);
lean_dec_ref(v_inst_475_);
v___f_480_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_480_, 0, v_toApplicative_478_);
lean_inc(v_a_477_);
v___x_481_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_481_, 0, lean_box(0));
lean_closure_set(v___x_481_, 1, lean_box(0));
lean_closure_set(v___x_481_, 2, v_a_477_);
v___x_482_ = lean_apply_2(v_inst_476_, lean_box(0), v___x_481_);
v___x_483_ = lean_apply_4(v_toBind_479_, lean_box(0), lean_box(0), v___x_482_, v___f_480_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_484_, v_inst_485_, v_a_486_);
lean_dec(v_a_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(lean_object* v_m_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_489_, v_inst_490_, v_a_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(lean_object* v_m_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(v_m_493_, v_inst_494_, v_inst_495_, v_a_496_);
lean_dec(v_a_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(lean_object* v_toApplicative_498_, lean_object* v_a_499_){
_start:
{
uint8_t v___y_501_; lean_object* v_pendingConsumer_505_; 
v_pendingConsumer_505_ = lean_ctor_get(v_a_499_, 1);
if (lean_obj_tag(v_pendingConsumer_505_) == 0)
{
uint8_t v___x_506_; 
v___x_506_ = 0;
v___y_501_ = v___x_506_;
goto v___jp_500_;
}
else
{
uint8_t v___x_507_; 
v___x_507_ = 1;
v___y_501_ = v___x_507_;
goto v___jp_500_;
}
v___jp_500_:
{
lean_object* v_toPure_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_toPure_502_ = lean_ctor_get(v_toApplicative_498_, 1);
lean_inc(v_toPure_502_);
lean_dec_ref(v_toApplicative_498_);
v___x_503_ = lean_box(v___y_501_);
v___x_504_ = lean_apply_2(v_toPure_502_, lean_box(0), v___x_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(v_toApplicative_508_, v_a_509_);
lean_dec_ref(v_a_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_toApplicative_514_; lean_object* v_toBind_515_; lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_toApplicative_514_ = lean_ctor_get(v_inst_511_, 0);
lean_inc_ref(v_toApplicative_514_);
v_toBind_515_ = lean_ctor_get(v_inst_511_, 1);
lean_inc(v_toBind_515_);
lean_dec_ref(v_inst_511_);
v___f_516_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_516_, 0, v_toApplicative_514_);
lean_inc(v_a_513_);
v___x_517_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_517_, 0, lean_box(0));
lean_closure_set(v___x_517_, 1, lean_box(0));
lean_closure_set(v___x_517_, 2, v_a_513_);
v___x_518_ = lean_apply_2(v_inst_512_, lean_box(0), v___x_517_);
v___x_519_ = lean_apply_4(v_toBind_515_, lean_box(0), lean_box(0), v___x_518_, v___f_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_520_, v_inst_521_, v_a_522_);
lean_dec(v_a_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(lean_object* v_m_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_525_, v_inst_526_, v_a_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(lean_object* v_m_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(v_m_529_, v_inst_530_, v_inst_531_, v_a_532_);
lean_dec(v_a_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_534_, lean_object* v_chunk_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_toPure_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_toPure_537_ = lean_ctor_get(v_toApplicative_534_, 1);
lean_inc(v_toPure_537_);
lean_dec_ref(v_toApplicative_534_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v_chunk_535_);
v___x_539_ = lean_apply_2(v_toPure_537_, lean_box(0), v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_540_, lean_object* v_done_541_, lean_object* v_inst_542_, lean_object* v_toBind_543_, lean_object* v___f_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_toFunctor_546_; lean_object* v_mapConst_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_toFunctor_546_ = lean_ctor_get(v_toApplicative_540_, 0);
lean_inc_ref(v_toFunctor_546_);
lean_dec_ref(v_toApplicative_540_);
v_mapConst_547_ = lean_ctor_get(v_toFunctor_546_, 1);
lean_inc(v_mapConst_547_);
lean_dec_ref(v_toFunctor_546_);
v___x_548_ = 1;
v___x_549_ = lean_box(v___x_548_);
v___x_550_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_550_, 0, lean_box(0));
lean_closure_set(v___x_550_, 1, v___x_549_);
lean_closure_set(v___x_550_, 2, v_done_541_);
v___x_551_ = lean_apply_2(v_inst_542_, lean_box(0), v___x_550_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_apply_4(v_mapConst_547_, lean_box(0), lean_box(0), v___x_552_, v___x_551_);
v___x_554_ = lean_apply_4(v_toBind_543_, lean_box(0), lean_box(0), v___x_553_, v___f_544_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_555_, lean_object* v_inst_556_, lean_object* v_toBind_557_, lean_object* v_a_558_, lean_object* v_inst_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_pendingProducer_561_; 
v_pendingProducer_561_ = lean_ctor_get(v_a_560_, 0);
if (lean_obj_tag(v_pendingProducer_561_) == 1)
{
lean_object* v_val_562_; lean_object* v_pendingConsumer_563_; lean_object* v_interestWaiter_564_; uint8_t v_closed_565_; lean_object* v_knownSize_566_; lean_object* v_pendingIncompleteChunk_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_583_; 
v_val_562_ = lean_ctor_get(v_pendingProducer_561_, 0);
lean_inc(v_val_562_);
v_pendingConsumer_563_ = lean_ctor_get(v_a_560_, 1);
v_interestWaiter_564_ = lean_ctor_get(v_a_560_, 2);
v_closed_565_ = lean_ctor_get_uint8(v_a_560_, sizeof(void*)*5);
v_knownSize_566_ = lean_ctor_get(v_a_560_, 3);
v_pendingIncompleteChunk_567_ = lean_ctor_get(v_a_560_, 4);
v_isSharedCheck_583_ = !lean_is_exclusive(v_a_560_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v_a_560_, 0);
lean_dec(v_unused_584_);
v___x_569_ = v_a_560_;
v_isShared_570_ = v_isSharedCheck_583_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_pendingIncompleteChunk_567_);
lean_inc(v_knownSize_566_);
lean_inc(v_interestWaiter_564_);
lean_inc(v_pendingConsumer_563_);
lean_dec(v_a_560_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_583_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_chunk_571_; lean_object* v_done_572_; lean_object* v___x_573_; lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v_chunk_571_ = lean_ctor_get(v_val_562_, 0);
lean_inc_ref_n(v_chunk_571_, 2);
v_done_572_ = lean_ctor_get(v_val_562_, 1);
lean_inc(v_done_572_);
lean_dec(v_val_562_);
v___x_573_ = lean_box(0);
lean_inc_ref(v_toApplicative_555_);
v___f_574_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_574_, 0, v_toApplicative_555_);
lean_closure_set(v___f_574_, 1, v_chunk_571_);
lean_inc(v_toBind_557_);
v___f_575_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_575_, 0, v_toApplicative_555_);
lean_closure_set(v___f_575_, 1, v_done_572_);
lean_closure_set(v___f_575_, 2, v_inst_556_);
lean_closure_set(v___f_575_, 3, v_toBind_557_);
lean_closure_set(v___f_575_, 4, v___f_574_);
v___x_576_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_566_, v_chunk_571_);
lean_dec_ref(v_chunk_571_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 3, v___x_576_);
lean_ctor_set(v___x_569_, 0, v___x_573_);
v___x_578_ = v___x_569_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_pendingConsumer_563_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_interestWaiter_564_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v_pendingIncompleteChunk_567_);
lean_ctor_set_uint8(v_reuseFailAlloc_582_, sizeof(void*)*5, v_closed_565_);
v___x_578_ = v_reuseFailAlloc_582_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_inc(v_a_558_);
v___x_579_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_579_, 0, lean_box(0));
lean_closure_set(v___x_579_, 1, lean_box(0));
lean_closure_set(v___x_579_, 2, v_a_558_);
lean_closure_set(v___x_579_, 3, v___x_578_);
v___x_580_ = lean_apply_2(v_inst_559_, lean_box(0), v___x_579_);
v___x_581_ = lean_apply_4(v_toBind_557_, lean_box(0), lean_box(0), v___x_580_, v___f_575_);
return v___x_581_;
}
}
}
else
{
lean_object* v_toPure_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec_ref(v_a_560_);
lean_dec(v_inst_559_);
lean_dec(v_toBind_557_);
lean_dec(v_inst_556_);
v_toPure_585_ = lean_ctor_get(v_toApplicative_555_, 1);
lean_inc(v_toPure_585_);
lean_dec_ref(v_toApplicative_555_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_apply_2(v_toPure_585_, lean_box(0), v___x_586_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_toApplicative_588_, lean_object* v_inst_589_, lean_object* v_toBind_590_, lean_object* v_a_591_, lean_object* v_inst_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(v_toApplicative_588_, v_inst_589_, v_toBind_590_, v_a_591_, v_inst_592_, v_a_593_);
lean_dec(v_a_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_toApplicative_599_; lean_object* v_toBind_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_toApplicative_599_ = lean_ctor_get(v_inst_595_, 0);
lean_inc_ref(v_toApplicative_599_);
v_toBind_600_ = lean_ctor_get(v_inst_595_, 1);
lean_inc_n(v_toBind_600_, 2);
lean_dec_ref(v_inst_595_);
lean_inc(v_inst_596_);
lean_inc_n(v_a_598_, 2);
v___f_601_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_601_, 0, v_toApplicative_599_);
lean_closure_set(v___f_601_, 1, v_inst_597_);
lean_closure_set(v___f_601_, 2, v_toBind_600_);
lean_closure_set(v___f_601_, 3, v_a_598_);
lean_closure_set(v___f_601_, 4, v_inst_596_);
v___x_602_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_602_, 0, lean_box(0));
lean_closure_set(v___x_602_, 1, lean_box(0));
lean_closure_set(v___x_602_, 2, v_a_598_);
v___x_603_ = lean_apply_2(v_inst_596_, lean_box(0), v___x_602_);
v___x_604_ = lean_apply_4(v_toBind_600_, lean_box(0), lean_box(0), v___x_603_, v___f_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_605_, v_inst_606_, v_inst_607_, v_a_608_);
lean_dec(v_a_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(lean_object* v_m_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_611_, v_inst_612_, v_inst_613_, v_a_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(lean_object* v_m_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(v_m_616_, v_inst_617_, v_inst_618_, v_inst_619_, v_a_620_);
lean_dec(v_a_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(uint8_t v___x_622_, lean_object* v_knownSize_623_, lean_object* v_inst_624_, lean_object* v_____r_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_ctor_set(v___x_628_, 3, v_knownSize_623_);
lean_ctor_set(v___x_628_, 4, v___x_627_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*5, v___x_622_);
lean_inc(v___y_626_);
v___x_629_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_629_, 0, lean_box(0));
lean_closure_set(v___x_629_, 1, lean_box(0));
lean_closure_set(v___x_629_, 2, v___y_626_);
lean_closure_set(v___x_629_, 3, v___x_628_);
v___x_630_ = lean_apply_2(v_inst_624_, lean_box(0), v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed(lean_object* v___x_631_, lean_object* v_knownSize_632_, lean_object* v_inst_633_, lean_object* v_____r_634_, lean_object* v___y_635_){
_start:
{
uint8_t v___x_784__boxed_636_; lean_object* v_res_637_; 
v___x_784__boxed_636_ = lean_unbox(v___x_631_);
v_res_637_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(v___x_784__boxed_636_, v_knownSize_632_, v_inst_633_, v_____r_634_, v___y_635_);
lean_dec(v___y_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(lean_object* v___f_638_, lean_object* v___y_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_641_; 
lean_inc(v___y_639_);
v___x_641_ = lean_apply_2(v___f_638_, v_a_640_, v___y_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object* v___f_642_, lean_object* v___y_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(v___f_642_, v___y_643_, v_a_644_);
lean_dec(v___y_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object* v_pendingProducer_646_, lean_object* v_toApplicative_647_, lean_object* v___f_648_, uint8_t v_closed_649_, lean_object* v_inst_650_, lean_object* v_toBind_651_, lean_object* v_____r_652_, lean_object* v___y_653_){
_start:
{
if (lean_obj_tag(v_pendingProducer_646_) == 1)
{
lean_object* v_val_654_; lean_object* v_toFunctor_655_; lean_object* v_done_656_; lean_object* v_mapConst_657_; lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_val_654_ = lean_ctor_get(v_pendingProducer_646_, 0);
lean_inc(v_val_654_);
lean_dec_ref(v_pendingProducer_646_);
v_toFunctor_655_ = lean_ctor_get(v_toApplicative_647_, 0);
lean_inc_ref(v_toFunctor_655_);
lean_dec_ref(v_toApplicative_647_);
v_done_656_ = lean_ctor_get(v_val_654_, 1);
lean_inc(v_done_656_);
lean_dec(v_val_654_);
v_mapConst_657_ = lean_ctor_get(v_toFunctor_655_, 1);
lean_inc(v_mapConst_657_);
lean_dec_ref(v_toFunctor_655_);
lean_inc(v___y_653_);
v___f_658_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_658_, 0, v___f_648_);
lean_closure_set(v___f_658_, 1, v___y_653_);
v___x_659_ = lean_box(v_closed_649_);
v___x_660_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_660_, 0, lean_box(0));
lean_closure_set(v___x_660_, 1, v___x_659_);
lean_closure_set(v___x_660_, 2, v_done_656_);
v___x_661_ = lean_apply_2(v_inst_650_, lean_box(0), v___x_660_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_apply_4(v_mapConst_657_, lean_box(0), lean_box(0), v___x_662_, v___x_661_);
v___x_664_ = lean_apply_4(v_toBind_651_, lean_box(0), lean_box(0), v___x_663_, v___f_658_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v_toBind_651_);
lean_dec(v_inst_650_);
lean_dec_ref(v_toApplicative_647_);
lean_dec(v_pendingProducer_646_);
v___x_665_ = lean_box(0);
lean_inc(v___y_653_);
v___x_666_ = lean_apply_2(v___f_648_, v___x_665_, v___y_653_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed(lean_object* v_pendingProducer_667_, lean_object* v_toApplicative_668_, lean_object* v___f_669_, lean_object* v_closed_670_, lean_object* v_inst_671_, lean_object* v_toBind_672_, lean_object* v_____r_673_, lean_object* v___y_674_){
_start:
{
uint8_t v_closed_boxed_675_; lean_object* v_res_676_; 
v_closed_boxed_675_ = lean_unbox(v_closed_670_);
v_res_676_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(v_pendingProducer_667_, v_toApplicative_668_, v___f_669_, v_closed_boxed_675_, v_inst_671_, v_toBind_672_, v_____r_673_, v___y_674_);
lean_dec(v___y_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object* v_interestWaiter_677_, lean_object* v_toApplicative_678_, lean_object* v___f_679_, uint8_t v_closed_680_, lean_object* v_inst_681_, lean_object* v_toBind_682_, lean_object* v_____r_683_, lean_object* v___y_684_){
_start:
{
if (lean_obj_tag(v_interestWaiter_677_) == 1)
{
lean_object* v_toFunctor_685_; lean_object* v_val_686_; lean_object* v_mapConst_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_toFunctor_685_ = lean_ctor_get(v_toApplicative_678_, 0);
lean_inc_ref(v_toFunctor_685_);
lean_dec_ref(v_toApplicative_678_);
v_val_686_ = lean_ctor_get(v_interestWaiter_677_, 0);
lean_inc(v_val_686_);
lean_dec_ref(v_interestWaiter_677_);
v_mapConst_687_ = lean_ctor_get(v_toFunctor_685_, 1);
lean_inc(v_mapConst_687_);
lean_dec_ref(v_toFunctor_685_);
lean_inc(v___y_684_);
v___f_688_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_688_, 0, v___f_679_);
lean_closure_set(v___f_688_, 1, v___y_684_);
v___x_689_ = lean_box(v_closed_680_);
v___x_690_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_690_, 0, v_val_686_);
lean_closure_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_apply_2(v_inst_681_, lean_box(0), v___x_690_);
v___x_692_ = lean_box(0);
v___x_693_ = lean_apply_4(v_mapConst_687_, lean_box(0), lean_box(0), v___x_692_, v___x_691_);
v___x_694_ = lean_apply_4(v_toBind_682_, lean_box(0), lean_box(0), v___x_693_, v___f_688_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v_toBind_682_);
lean_dec(v_inst_681_);
lean_dec_ref(v_toApplicative_678_);
lean_dec(v_interestWaiter_677_);
v___x_695_ = lean_box(0);
lean_inc(v___y_684_);
v___x_696_ = lean_apply_2(v___f_679_, v___x_695_, v___y_684_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object* v_interestWaiter_697_, lean_object* v_toApplicative_698_, lean_object* v___f_699_, lean_object* v_closed_700_, lean_object* v_inst_701_, lean_object* v_toBind_702_, lean_object* v_____r_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_closed_boxed_705_; lean_object* v_res_706_; 
v_closed_boxed_705_ = lean_unbox(v_closed_700_);
v_res_706_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_697_, v_toApplicative_698_, v___f_699_, v_closed_boxed_705_, v_inst_701_, v_toBind_702_, v_____r_703_, v___y_704_);
lean_dec(v___y_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(lean_object* v___f_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_710_; 
lean_inc(v_a_708_);
v___x_710_ = lean_apply_2(v___f_707_, v_a_709_, v_a_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object* v___f_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(v___f_711_, v_a_712_, v_a_713_);
lean_dec(v_a_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object* v_inst_715_, lean_object* v_toApplicative_716_, lean_object* v_inst_717_, lean_object* v_toBind_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
uint8_t v_closed_721_; 
v_closed_721_ = lean_ctor_get_uint8(v_a_720_, sizeof(void*)*5);
if (v_closed_721_ == 0)
{
lean_object* v_pendingProducer_722_; lean_object* v_pendingConsumer_723_; lean_object* v_interestWaiter_724_; lean_object* v_knownSize_725_; uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___f_730_; lean_object* v___x_731_; lean_object* v___f_732_; 
v_pendingProducer_722_ = lean_ctor_get(v_a_720_, 0);
lean_inc(v_pendingProducer_722_);
v_pendingConsumer_723_ = lean_ctor_get(v_a_720_, 1);
lean_inc(v_pendingConsumer_723_);
v_interestWaiter_724_ = lean_ctor_get(v_a_720_, 2);
lean_inc_n(v_interestWaiter_724_, 2);
v_knownSize_725_ = lean_ctor_get(v_a_720_, 3);
lean_inc(v_knownSize_725_);
lean_dec_ref(v_a_720_);
v___x_726_ = 1;
v___x_727_ = lean_box(v___x_726_);
v___f_728_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_728_, 0, v___x_727_);
lean_closure_set(v___f_728_, 1, v_knownSize_725_);
lean_closure_set(v___f_728_, 2, v_inst_715_);
v___x_729_ = lean_box(v_closed_721_);
lean_inc_n(v_toBind_718_, 2);
lean_inc_n(v_inst_717_, 2);
lean_inc_ref_n(v_toApplicative_716_, 2);
v___f_730_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_730_, 0, v_pendingProducer_722_);
lean_closure_set(v___f_730_, 1, v_toApplicative_716_);
lean_closure_set(v___f_730_, 2, v___f_728_);
lean_closure_set(v___f_730_, 3, v___x_729_);
lean_closure_set(v___f_730_, 4, v_inst_717_);
lean_closure_set(v___f_730_, 5, v_toBind_718_);
v___x_731_ = lean_box(v_closed_721_);
lean_inc_ref(v___f_730_);
v___f_732_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_732_, 0, v_interestWaiter_724_);
lean_closure_set(v___f_732_, 1, v_toApplicative_716_);
lean_closure_set(v___f_732_, 2, v___f_730_);
lean_closure_set(v___f_732_, 3, v___x_731_);
lean_closure_set(v___f_732_, 4, v_inst_717_);
lean_closure_set(v___f_732_, 5, v_toBind_718_);
if (lean_obj_tag(v_pendingConsumer_723_) == 1)
{
lean_object* v_toFunctor_733_; lean_object* v_val_734_; lean_object* v_mapConst_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec_ref(v___f_730_);
lean_dec(v_interestWaiter_724_);
v_toFunctor_733_ = lean_ctor_get(v_toApplicative_716_, 0);
lean_inc_ref(v_toFunctor_733_);
lean_dec_ref(v_toApplicative_716_);
v_val_734_ = lean_ctor_get(v_pendingConsumer_723_, 0);
lean_inc(v_val_734_);
lean_dec_ref(v_pendingConsumer_723_);
v_mapConst_735_ = lean_ctor_get(v_toFunctor_733_, 1);
lean_inc(v_mapConst_735_);
lean_dec_ref(v_toFunctor_733_);
lean_inc(v_a_719_);
v___f_736_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_736_, 0, v___f_732_);
lean_closure_set(v___f_736_, 1, v_a_719_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed), 3, 2);
lean_closure_set(v___x_738_, 0, v_val_734_);
lean_closure_set(v___x_738_, 1, v___x_737_);
v___x_739_ = lean_apply_2(v_inst_717_, lean_box(0), v___x_738_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_apply_4(v_mapConst_735_, lean_box(0), lean_box(0), v___x_740_, v___x_739_);
v___x_742_ = lean_apply_4(v_toBind_718_, lean_box(0), lean_box(0), v___x_741_, v___f_736_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec_ref(v___f_732_);
lean_dec(v_pendingConsumer_723_);
v___x_743_ = lean_box(0);
v___x_744_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_724_, v_toApplicative_716_, v___f_730_, v_closed_721_, v_inst_717_, v_toBind_718_, v___x_743_, v_a_719_);
return v___x_744_;
}
}
else
{
lean_object* v_toPure_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec_ref(v_a_720_);
lean_dec(v_toBind_718_);
lean_dec(v_inst_717_);
lean_dec(v_inst_715_);
v_toPure_745_ = lean_ctor_get(v_toApplicative_716_, 1);
lean_inc(v_toPure_745_);
lean_dec_ref(v_toApplicative_716_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_apply_2(v_toPure_745_, lean_box(0), v___x_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object* v_inst_748_, lean_object* v_toApplicative_749_, lean_object* v_inst_750_, lean_object* v_toBind_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(v_inst_748_, v_toApplicative_749_, v_inst_750_, v_toBind_751_, v_a_752_, v_a_753_);
lean_dec(v_a_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_toApplicative_759_; lean_object* v_toBind_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_toApplicative_759_ = lean_ctor_get(v_inst_755_, 0);
lean_inc_ref(v_toApplicative_759_);
v_toBind_760_ = lean_ctor_get(v_inst_755_, 1);
lean_inc_n(v_toBind_760_, 2);
lean_dec_ref(v_inst_755_);
lean_inc_n(v_a_758_, 2);
lean_inc(v_inst_756_);
v___f_761_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_761_, 0, v_inst_756_);
lean_closure_set(v___f_761_, 1, v_toApplicative_759_);
lean_closure_set(v___f_761_, 2, v_inst_757_);
lean_closure_set(v___f_761_, 3, v_toBind_760_);
lean_closure_set(v___f_761_, 4, v_a_758_);
v___x_762_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_762_, 0, lean_box(0));
lean_closure_set(v___x_762_, 1, lean_box(0));
lean_closure_set(v___x_762_, 2, v_a_758_);
v___x_763_ = lean_apply_2(v_inst_756_, lean_box(0), v___x_762_);
v___x_764_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_763_, v___f_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_765_, v_inst_766_, v_inst_767_, v_a_768_);
lean_dec(v_a_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object* v_m_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_771_, v_inst_772_, v_inst_773_, v_a_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object* v_m_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(v_m_776_, v_inst_777_, v_inst_778_, v_inst_779_, v_a_780_);
lean_dec(v_a_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object* v_chunk_782_, lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_chunk_782_);
v_a_785_ = lean_ctor_get(v_x_783_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_793_ == 0)
{
v___x_787_ = v_x_783_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v_x_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_785_);
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
else
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_802_; 
v_isSharedCheck_802_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_x_783_, 0);
lean_dec(v_unused_803_);
v___x_795_ = v_x_783_;
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_x_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v_chunk_782_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object* v_chunk_804_, lean_object* v_x_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_chunk_804_, v_x_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object* v_done_812_, lean_object* v___f_813_, lean_object* v_x_814_){
_start:
{
if (lean_obj_tag(v_x_814_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v___f_813_);
v_a_816_ = lean_ctor_get(v_x_814_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_x_814_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v_x_814_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v_x_814_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
else
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v_x_814_);
v___x_825_ = 1;
v___x_826_ = lean_box(v___x_825_);
v___x_827_ = lean_io_promise_resolve(v___x_826_, v_done_812_);
v___x_828_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = 0;
v___x_831_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_829_, v___x_830_, v___x_828_, v___f_813_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object* v_done_832_, lean_object* v___f_833_, lean_object* v_x_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_done_832_, v___f_833_, v_x_834_);
lean_dec(v_done_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2(lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_852_; 
v_a_844_ = lean_ctor_get(v_x_842_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_852_ == 0)
{
v___x_846_ = v_x_842_;
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v_x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; 
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_893_; 
v_a_853_ = lean_ctor_get(v_x_842_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_893_ == 0)
{
v___x_855_ = v_x_842_;
v_isShared_856_ = v_isSharedCheck_893_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v_x_842_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_893_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_pendingProducer_857_; 
v_pendingProducer_857_ = lean_ctor_get(v_a_853_, 0);
lean_inc(v_pendingProducer_857_);
if (lean_obj_tag(v_pendingProducer_857_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_891_; 
v_val_858_ = lean_ctor_get(v_pendingProducer_857_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_pendingProducer_857_);
if (v_isSharedCheck_891_ == 0)
{
v___x_860_ = v_pendingProducer_857_;
v_isShared_861_ = v_isSharedCheck_891_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_val_858_);
lean_dec(v_pendingProducer_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_891_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_pendingConsumer_862_; lean_object* v_interestWaiter_863_; uint8_t v_closed_864_; lean_object* v_knownSize_865_; lean_object* v_pendingIncompleteChunk_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_889_; 
v_pendingConsumer_862_ = lean_ctor_get(v_a_853_, 1);
v_interestWaiter_863_ = lean_ctor_get(v_a_853_, 2);
v_closed_864_ = lean_ctor_get_uint8(v_a_853_, sizeof(void*)*5);
v_knownSize_865_ = lean_ctor_get(v_a_853_, 3);
v_pendingIncompleteChunk_866_ = lean_ctor_get(v_a_853_, 4);
v_isSharedCheck_889_ = !lean_is_exclusive(v_a_853_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v_a_853_, 0);
lean_dec(v_unused_890_);
v___x_868_ = v_a_853_;
v_isShared_869_ = v_isSharedCheck_889_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_pendingIncompleteChunk_866_);
lean_inc(v_knownSize_865_);
lean_inc(v_interestWaiter_863_);
lean_inc(v_pendingConsumer_862_);
lean_dec(v_a_853_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_889_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_chunk_870_; lean_object* v_done_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v_chunk_870_ = lean_ctor_get(v_val_858_, 0);
lean_inc_ref(v_chunk_870_);
v_done_871_ = lean_ctor_get(v_val_858_, 1);
lean_inc(v_done_871_);
lean_dec(v_val_858_);
v___x_872_ = lean_box(0);
v___x_873_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_865_, v_chunk_870_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 3, v___x_873_);
lean_ctor_set(v___x_868_, 0, v___x_872_);
v___x_875_ = v___x_868_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_pendingConsumer_862_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_interestWaiter_863_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_pendingIncompleteChunk_866_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, sizeof(void*)*5, v_closed_864_);
v___x_875_ = v_reuseFailAlloc_888_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___x_880_; 
v___x_876_ = lean_st_ref_set(v_a_841_, v___x_875_);
v___f_877_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_877_, 0, v_chunk_870_);
v___f_878_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_878_, 0, v_done_871_);
lean_closure_set(v___f_878_, 1, v___f_877_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_876_);
v___x_880_ = v___x_855_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_876_);
v___x_880_ = v_reuseFailAlloc_887_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 0);
lean_ctor_set(v___x_860_, 0, v___x_880_);
v___x_882_ = v___x_860_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_886_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = 0;
v___x_885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_883_, v___x_884_, v___x_882_, v___f_878_);
return v___x_885_;
}
}
}
}
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v_pendingProducer_857_);
lean_del_object(v___x_855_);
lean_dec(v_a_853_);
v___x_892_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1));
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___boxed(lean_object* v_a_894_, lean_object* v_x_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2(v_a_894_, v_x_895_);
lean_dec(v_a_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; 
v___x_900_ = lean_st_ref_get(v_a_898_);
lean_inc(v_a_898_);
v___f_901_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___boxed), 3, 1);
lean_closure_set(v___f_901_, 0, v_a_898_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = 0;
v___x_906_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_904_, v___x_905_, v___x_903_, v___f_901_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object* v_a_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_907_);
lean_dec(v_a_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object* v_pendingProducer_910_, lean_object* v_pendingConsumer_911_, uint8_t v_closed_912_, lean_object* v_knownSize_913_, lean_object* v_pendingIncompleteChunk_914_, lean_object* v_interestWaiter_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_918_, 0, v_pendingProducer_910_);
lean_ctor_set(v___x_918_, 1, v_pendingConsumer_911_);
lean_ctor_set(v___x_918_, 2, v_interestWaiter_915_);
lean_ctor_set(v___x_918_, 3, v_knownSize_913_);
lean_ctor_set(v___x_918_, 4, v_pendingIncompleteChunk_914_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*5, v_closed_912_);
v___x_919_ = lean_st_ref_set(v___y_916_, v___x_918_);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object* v_pendingProducer_922_, lean_object* v_pendingConsumer_923_, lean_object* v_closed_924_, lean_object* v_knownSize_925_, lean_object* v_pendingIncompleteChunk_926_, lean_object* v_interestWaiter_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v_closed_boxed_930_; lean_object* v_res_931_; 
v_closed_boxed_930_ = lean_unbox(v_closed_924_);
v_res_931_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_922_, v_pendingConsumer_923_, v_closed_boxed_930_, v_knownSize_925_, v_pendingIncompleteChunk_926_, v_interestWaiter_927_, v___y_928_);
lean_dec(v___y_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object* v___f_932_, lean_object* v___y_933_, lean_object* v_x_934_){
_start:
{
if (lean_obj_tag(v_x_934_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v___f_932_);
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
lean_object* v_a_945_; lean_object* v___x_946_; 
v_a_945_ = lean_ctor_get(v_x_934_, 0);
lean_inc(v_a_945_);
lean_dec_ref(v_x_934_);
lean_inc(v___y_933_);
v___x_946_ = lean_apply_3(v___f_932_, v_a_945_, v___y_933_, lean_box(0));
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object* v___f_947_, lean_object* v___y_948_, lean_object* v_x_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_947_, v___y_948_, v_x_949_);
lean_dec(v___y_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object* v_interestWaiter_956_, lean_object* v___f_957_, lean_object* v___f_958_, lean_object* v_x_959_){
_start:
{
if (lean_obj_tag(v_x_959_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v___f_958_);
lean_dec_ref(v___f_957_);
lean_dec(v_interestWaiter_956_);
v_a_961_ = lean_ctor_get(v_x_959_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_959_);
if (v_isSharedCheck_969_ == 0)
{
v___x_963_ = v_x_959_;
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v_x_959_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_968_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_967_; 
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_986_; 
v_a_970_ = lean_ctor_get(v_x_959_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_959_);
if (v_isSharedCheck_986_ == 0)
{
v___x_972_ = v_x_959_;
v_isShared_973_ = v_isSharedCheck_986_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v_x_959_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_986_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
uint8_t v___x_974_; 
v___x_974_ = lean_unbox(v_a_970_);
if (v___x_974_ == 0)
{
lean_object* v___x_976_; 
lean_dec_ref(v___f_958_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v_interestWaiter_956_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_interestWaiter_956_);
v___x_976_ = v_reuseFailAlloc_981_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; 
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_unbox(v_a_970_);
lean_dec(v_a_970_);
v___x_980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_978_, v___x_979_, v___x_977_, v___f_957_);
return v___x_980_;
}
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; 
lean_del_object(v___x_972_);
lean_dec(v_a_970_);
lean_dec_ref(v___f_957_);
lean_dec(v_interestWaiter_956_);
v___x_982_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1));
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_984_ = 0;
v___x_985_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_983_, v___x_984_, v___x_982_, v___f_958_);
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object* v_interestWaiter_987_, lean_object* v___f_988_, lean_object* v___f_989_, lean_object* v_x_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_987_, v___f_988_, v___f_989_, v_x_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object* v_pendingProducer_993_, uint8_t v_closed_994_, lean_object* v_knownSize_995_, lean_object* v_pendingIncompleteChunk_996_, lean_object* v_interestWaiter_997_, lean_object* v_pendingConsumer_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___f_1002_; 
v___x_1001_ = lean_box(v_closed_994_);
v___f_1002_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed), 8, 5);
lean_closure_set(v___f_1002_, 0, v_pendingProducer_993_);
lean_closure_set(v___f_1002_, 1, v_pendingConsumer_998_);
lean_closure_set(v___f_1002_, 2, v___x_1001_);
lean_closure_set(v___f_1002_, 3, v_knownSize_995_);
lean_closure_set(v___f_1002_, 4, v_pendingIncompleteChunk_996_);
if (lean_obj_tag(v_interestWaiter_997_) == 0)
{
lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; 
lean_inc(v___y_999_);
v___f_1003_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1003_, 0, v___f_1002_);
lean_closure_set(v___f_1003_, 1, v___y_999_);
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_interestWaiter_997_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = 0;
v___x_1008_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1006_, v___x_1007_, v___x_1005_, v___f_1003_);
return v___x_1008_;
}
else
{
lean_object* v_val_1009_; lean_object* v_finished_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; 
v_val_1009_ = lean_ctor_get(v_interestWaiter_997_, 0);
v_finished_1010_ = lean_ctor_get(v_val_1009_, 0);
v___x_1011_ = lean_st_ref_get(v_finished_1010_);
lean_inc(v___y_999_);
v___f_1012_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1012_, 0, v___f_1002_);
lean_closure_set(v___f_1012_, 1, v___y_999_);
lean_inc_ref(v___f_1012_);
v___f_1013_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1013_, 0, v_interestWaiter_997_);
lean_closure_set(v___f_1013_, 1, v___f_1012_);
lean_closure_set(v___f_1013_, 2, v___f_1012_);
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1011_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = 0;
v___x_1018_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1016_, v___x_1017_, v___x_1015_, v___f_1013_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object* v_pendingProducer_1019_, lean_object* v_closed_1020_, lean_object* v_knownSize_1021_, lean_object* v_pendingIncompleteChunk_1022_, lean_object* v_interestWaiter_1023_, lean_object* v_pendingConsumer_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
uint8_t v_closed_boxed_1027_; lean_object* v_res_1028_; 
v_closed_boxed_1027_ = lean_unbox(v_closed_1020_);
v_res_1028_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_1019_, v_closed_boxed_1027_, v_knownSize_1021_, v_pendingIncompleteChunk_1022_, v_interestWaiter_1023_, v_pendingConsumer_1024_, v___y_1025_);
lean_dec(v___y_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object* v___f_1029_, lean_object* v___y_1030_, lean_object* v_x_1031_){
_start:
{
if (lean_obj_tag(v_x_1031_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v___f_1029_);
v_a_1033_ = lean_ctor_get(v_x_1031_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1035_ = v_x_1031_;
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v_x_1031_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1043_; 
v_a_1042_ = lean_ctor_get(v_x_1031_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v_x_1031_);
lean_inc(v___y_1030_);
v___x_1043_ = lean_apply_3(v___f_1029_, v_a_1042_, v___y_1030_, lean_box(0));
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object* v___f_1044_, lean_object* v___y_1045_, lean_object* v_x_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_1044_, v___y_1045_, v_x_1046_);
lean_dec(v___y_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object* v___f_1049_, lean_object* v_a_1050_, lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v___f_1049_);
v_a_1053_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v_x_1051_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v_x_1051_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1063_; 
v_a_1062_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1062_);
lean_dec_ref(v_x_1051_);
lean_inc(v_a_1050_);
v___x_1063_ = lean_apply_3(v___f_1049_, v_a_1062_, v_a_1050_, lean_box(0));
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object* v___f_1064_, lean_object* v_a_1065_, lean_object* v_x_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_1064_, v_a_1065_, v_x_1066_);
lean_dec(v_a_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object* v_pendingConsumer_1073_, lean_object* v___f_1074_, lean_object* v___f_1075_, lean_object* v_x_1076_){
_start:
{
if (lean_obj_tag(v_x_1076_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v___f_1075_);
lean_dec_ref(v___f_1074_);
lean_dec(v_pendingConsumer_1073_);
v_a_1078_ = lean_ctor_get(v_x_1076_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_x_1076_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v_x_1076_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v_x_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1103_; 
v_a_1087_ = lean_ctor_get(v_x_1076_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_x_1076_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1089_ = v_x_1076_;
v_isShared_1090_ = v_isSharedCheck_1103_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v_x_1076_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1103_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_unbox(v_a_1087_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1093_; 
lean_dec_ref(v___f_1075_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_pendingConsumer_1073_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_pendingConsumer_1073_);
v___x_1093_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = lean_unbox(v_a_1087_);
lean_dec(v_a_1087_);
v___x_1097_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1095_, v___x_1096_, v___x_1094_, v___f_1074_);
return v___x_1097_;
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; 
lean_del_object(v___x_1089_);
lean_dec(v_a_1087_);
lean_dec_ref(v___f_1074_);
lean_dec(v_pendingConsumer_1073_);
v___x_1099_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1));
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = 0;
v___x_1102_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1100_, v___x_1101_, v___x_1099_, v___f_1075_);
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object* v_pendingConsumer_1104_, lean_object* v___f_1105_, lean_object* v___f_1106_, lean_object* v_x_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_1104_, v___f_1105_, v___f_1106_, v_x_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object* v_a_1110_, lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
v_a_1113_ = lean_ctor_get(v_x_1111_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1111_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v_x_1111_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v_x_1111_);
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
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1161_; 
v_a_1122_ = lean_ctor_get(v_x_1111_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_x_1111_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1124_ = v_x_1111_;
v_isShared_1125_ = v_isSharedCheck_1161_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v_x_1111_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1161_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_pendingProducer_1126_; lean_object* v_pendingConsumer_1127_; lean_object* v_interestWaiter_1128_; uint8_t v_closed_1129_; lean_object* v_knownSize_1130_; lean_object* v_pendingIncompleteChunk_1131_; lean_object* v___x_1132_; lean_object* v___f_1133_; lean_object* v___y_1135_; 
v_pendingProducer_1126_ = lean_ctor_get(v_a_1122_, 0);
lean_inc(v_pendingProducer_1126_);
v_pendingConsumer_1127_ = lean_ctor_get(v_a_1122_, 1);
lean_inc(v_pendingConsumer_1127_);
v_interestWaiter_1128_ = lean_ctor_get(v_a_1122_, 2);
lean_inc(v_interestWaiter_1128_);
v_closed_1129_ = lean_ctor_get_uint8(v_a_1122_, sizeof(void*)*5);
v_knownSize_1130_ = lean_ctor_get(v_a_1122_, 3);
lean_inc(v_knownSize_1130_);
v_pendingIncompleteChunk_1131_ = lean_ctor_get(v_a_1122_, 4);
lean_inc(v_pendingIncompleteChunk_1131_);
lean_dec(v_a_1122_);
v___x_1132_ = lean_box(v_closed_1129_);
v___f_1133_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1133_, 0, v_pendingProducer_1126_);
lean_closure_set(v___f_1133_, 1, v___x_1132_);
lean_closure_set(v___f_1133_, 2, v_knownSize_1130_);
lean_closure_set(v___f_1133_, 3, v_pendingIncompleteChunk_1131_);
lean_closure_set(v___f_1133_, 4, v_interestWaiter_1128_);
if (lean_obj_tag(v_pendingConsumer_1127_) == 1)
{
lean_object* v_val_1144_; 
v_val_1144_ = lean_ctor_get(v_pendingConsumer_1127_, 0);
lean_inc(v_val_1144_);
if (lean_obj_tag(v_val_1144_) == 1)
{
lean_object* v_finished_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1160_; 
lean_del_object(v___x_1124_);
v_finished_1145_ = lean_ctor_get(v_val_1144_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_val_1144_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1147_ = v_val_1144_;
v_isShared_1148_ = v_isSharedCheck_1160_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_finished_1145_);
lean_dec(v_val_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1160_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_finished_1149_; lean_object* v___x_1150_; lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___x_1154_; 
v_finished_1149_ = lean_ctor_get(v_finished_1145_, 0);
lean_inc(v_finished_1149_);
lean_dec_ref(v_finished_1145_);
v___x_1150_ = lean_st_ref_get(v_finished_1149_);
lean_dec(v_finished_1149_);
lean_inc(v_a_1110_);
v___f_1151_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1151_, 0, v___f_1133_);
lean_closure_set(v___f_1151_, 1, v_a_1110_);
lean_inc_ref(v___f_1151_);
v___f_1152_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1152_, 0, v_pendingConsumer_1127_);
lean_closure_set(v___f_1152_, 1, v___f_1151_);
lean_closure_set(v___f_1152_, 2, v___f_1151_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1150_);
v___x_1154_ = v___x_1147_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1150_);
v___x_1154_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = 0;
v___x_1158_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1156_, v___x_1157_, v___x_1155_, v___f_1152_);
return v___x_1158_;
}
}
}
else
{
lean_dec(v_val_1144_);
v___y_1135_ = v_a_1110_;
goto v___jp_1134_;
}
}
else
{
v___y_1135_ = v_a_1110_;
goto v___jp_1134_;
}
v___jp_1134_:
{
lean_object* v___f_1136_; lean_object* v___x_1138_; 
lean_inc(v___y_1135_);
v___f_1136_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1136_, 0, v___f_1133_);
lean_closure_set(v___f_1136_, 1, v___y_1135_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v_pendingConsumer_1127_);
v___x_1138_ = v___x_1124_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_pendingConsumer_1127_);
v___x_1138_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = 0;
v___x_1142_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1140_, v___x_1141_, v___x_1139_, v___f_1136_);
return v___x_1142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object* v_a_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_1162_, v_x_1163_);
lean_dec(v_a_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; 
v___x_1168_ = lean_st_ref_get(v_a_1166_);
lean_inc(v_a_1166_);
v___f_1169_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1169_, 0, v_a_1166_);
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = 0;
v___x_1174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1172_, v___x_1173_, v___x_1171_, v___f_1169_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object* v_a_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_1175_);
lean_dec(v_a_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object* v_mutex_1178_, lean_object* v_x_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_io_basemutex_unlock(v_mutex_1178_);
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_1184_, lean_object* v_x_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(v_mutex_1184_, v_x_1185_);
lean_dec(v_x_1185_);
lean_dec(v_mutex_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object* v_k_1188_, lean_object* v_ref_1189_, lean_object* v_x_1190_){
_start:
{
if (lean_obj_tag(v_x_1190_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_ref_1189_);
lean_dec_ref(v_k_1188_);
v_a_1192_ = lean_ctor_get(v_x_1190_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1190_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1194_ = v_x_1190_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v_x_1190_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
}
else
{
lean_object* v___x_1201_; 
lean_dec_ref(v_x_1190_);
v___x_1201_ = lean_apply_2(v_k_1188_, v_ref_1189_, lean_box(0));
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object* v_k_1202_, lean_object* v_ref_1203_, lean_object* v_x_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(v_k_1202_, v_ref_1203_, v_x_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object* v_mutex_1207_, lean_object* v___f_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1210_ = lean_io_basemutex_lock(v_mutex_1207_);
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = 0;
v___x_1215_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1213_, v___x_1214_, v___x_1212_, v___f_1208_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_1216_, lean_object* v___f_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(v_mutex_1216_, v___f_1217_);
lean_dec(v_mutex_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object* v___y_1220_){
_start:
{
if (lean_obj_tag(v___y_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_a_1221_ = lean_ctor_get(v___y_1220_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___y_1220_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___y_1220_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___y_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1237_; 
v_a_1229_ = lean_ctor_get(v___y_1220_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___y_1220_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1231_ = v___y_1220_;
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___y_1220_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_fst_1233_; lean_object* v___x_1235_; 
v_fst_1233_ = lean_ctor_get(v_a_1229_, 0);
lean_inc(v_fst_1233_);
lean_dec(v_a_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v_fst_1233_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_fst_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(lean_object* v_mutex_1239_, lean_object* v_k_1240_){
_start:
{
lean_object* v_ref_1242_; lean_object* v_mutex_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___y_1251_; 
v_ref_1242_ = lean_ctor_get(v_mutex_1239_, 0);
lean_inc(v_ref_1242_);
v_mutex_1243_ = lean_ctor_get(v_mutex_1239_, 1);
lean_inc_n(v_mutex_1243_, 2);
lean_dec_ref(v_mutex_1239_);
v___f_1244_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1244_, 0, v_mutex_1243_);
v___f_1245_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1245_, 0, v_k_1240_);
lean_closure_set(v___f_1245_, 1, v_ref_1242_);
v___f_1246_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1246_, 0, v_mutex_1243_);
lean_closure_set(v___f_1246_, 1, v___f_1245_);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = 0;
v___x_1249_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1246_, v___f_1244_, v___x_1247_, v___x_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1253_; 
v_a_1253_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1253_);
lean_dec_ref(v___x_1249_);
if (lean_obj_tag(v_a_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_a_1254_ = lean_ctor_get(v_a_1253_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_a_1253_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v_a_1253_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v_a_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v___y_1251_ = v___x_1259_;
goto v___jp_1250_;
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
v_a_1262_ = lean_ctor_get(v_a_1253_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_a_1253_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1264_ = v_a_1253_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v_a_1253_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v_fst_1266_; lean_object* v___x_1268_; 
v_fst_1266_ = lean_ctor_get(v_a_1262_, 0);
lean_inc(v_fst_1266_);
lean_dec(v_a_1262_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_fst_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_fst_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
v___y_1251_ = v___x_1268_;
goto v___jp_1250_;
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1280_; 
v_a_1271_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1273_ = v___x_1249_;
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1249_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___f_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___f_1275_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0));
v___x_1276_ = lean_task_map(v___f_1275_, v_a_1271_, v___x_1247_, v___x_1248_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
v___jp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___y_1251_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___boxed(lean_object* v_mutex_1281_, lean_object* v_k_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1281_, v_k_1282_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(lean_object* v_00_u03b1_1285_, lean_object* v_00_u03b2_1286_, lean_object* v_mutex_1287_, lean_object* v_k_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1287_, v_k_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_00_u03b2_1292_, lean_object* v_mutex_1293_, lean_object* v_k_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(v_00_u03b1_1291_, v_00_u03b2_1292_, v_mutex_1293_, v_k_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0(lean_object* v___y_1297_, lean_object* v_x_1298_){
_start:
{
if (lean_obj_tag(v_x_1298_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1308_; 
v_a_1300_ = lean_ctor_get(v_x_1298_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x_1298_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1302_ = v_x_1298_;
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v_x_1298_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
}
else
{
lean_object* v___x_1309_; 
lean_dec_ref(v_x_1298_);
v___x_1309_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1297_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(lean_object* v___y_1310_, lean_object* v_x_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_Http_Body_Stream_tryRecv___lam__0(v___y_1310_, v_x_1311_);
lean_dec(v___y_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1(lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; 
v___x_1316_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1314_);
lean_inc(v___y_1314_);
v___f_1317_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecv___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1317_, 0, v___y_1314_);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = 0;
v___x_1320_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1318_, v___x_1319_, v___x_1316_, v___f_1317_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Std_Http_Body_Stream_tryRecv___lam__1(v___y_1321_);
lean_dec(v___y_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv(lean_object* v_stream_1325_){
_start:
{
lean_object* v___f_1327_; lean_object* v___x_1328_; 
v___f_1327_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecv___closed__0));
v___x_1328_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1325_, v___f_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___boxed(lean_object* v_stream_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_Http_Body_Stream_tryRecv(v_stream_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(lean_object* v_x_1332_){
_start:
{
uint8_t v___y_1335_; 
if (lean_obj_tag(v_x_1332_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_a_1339_ = lean_ctor_get(v_x_1332_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_x_1332_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1341_ = v_x_1332_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v_x_1332_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v_pendingProducer_1349_; 
v_a_1348_ = lean_ctor_get(v_x_1332_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v_x_1332_);
v_pendingProducer_1349_ = lean_ctor_get(v_a_1348_, 0);
if (lean_obj_tag(v_pendingProducer_1349_) == 0)
{
uint8_t v_closed_1350_; 
v_closed_1350_ = lean_ctor_get_uint8(v_a_1348_, sizeof(void*)*5);
lean_dec(v_a_1348_);
v___y_1335_ = v_closed_1350_;
goto v___jp_1334_;
}
else
{
uint8_t v___x_1351_; 
lean_dec(v_a_1348_);
v___x_1351_ = 1;
v___y_1335_ = v___x_1351_;
goto v___jp_1334_;
}
}
v___jp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_box(v___y_1335_);
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed(lean_object* v_x_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(v_x_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(lean_object* v_a_1356_){
_start:
{
lean_object* v___x_1358_; lean_object* v___f_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; 
v___x_1358_ = lean_st_ref_get(v_a_1356_);
v___f_1359_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0));
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = 0;
v___x_1364_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1362_, v___x_1363_, v___x_1361_, v___f_1359_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___boxed(lean_object* v_a_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v_a_1365_);
lean_dec(v_a_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0(lean_object* v_x_1368_){
_start:
{
if (lean_obj_tag(v_x_1368_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1378_; 
v_a_1370_ = lean_ctor_get(v_x_1368_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1368_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1372_ = v_x_1368_;
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v_x_1368_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1388_; 
v_a_1379_ = lean_ctor_get(v_x_1368_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_x_1368_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1381_ = v_x_1368_;
v_isShared_1382_ = v_isSharedCheck_1388_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v_x_1368_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1388_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_a_1379_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed(lean_object* v_x_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Std_Http_Body_Stream_tryRecvBody___lam__0(v_x_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1(lean_object* v___y_1396_, lean_object* v___f_1397_, lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v___f_1397_);
v_a_1400_ = lean_ctor_get(v_x_1398_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_x_1398_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1402_ = v_x_1398_;
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v_x_1398_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
}
else
{
lean_object* v_a_1409_; uint8_t v___x_1410_; 
v_a_1409_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_a_1409_);
lean_dec_ref(v_x_1398_);
v___x_1410_ = lean_unbox(v_a_1409_);
lean_dec(v_a_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_dec_ref(v___f_1397_);
v___x_1411_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1));
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1412_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1396_);
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = 0;
v___x_1415_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1413_, v___x_1414_, v___x_1412_, v___f_1397_);
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed(lean_object* v___y_1416_, lean_object* v___f_1417_, lean_object* v_x_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1(v___y_1416_, v___f_1417_, v_x_1418_);
lean_dec(v___y_1416_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2(lean_object* v___y_1421_, lean_object* v___f_1422_, lean_object* v_x_1423_){
_start:
{
if (lean_obj_tag(v_x_1423_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1433_; 
lean_dec_ref(v___f_1422_);
v_a_1425_ = lean_ctor_get(v_x_1423_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1423_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1427_ = v_x_1423_;
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v_x_1423_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; 
lean_dec_ref(v_x_1423_);
v___x_1434_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_1421_);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = 0;
v___x_1437_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1435_, v___x_1436_, v___x_1434_, v___f_1422_);
return v___x_1437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed(lean_object* v___y_1438_, lean_object* v___f_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Std_Http_Body_Stream_tryRecvBody___lam__2(v___y_1438_, v___f_1439_, v_x_1440_);
lean_dec(v___y_1438_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3(lean_object* v___f_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; lean_object* v___f_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; 
v___x_1446_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1444_);
lean_inc_n(v___y_1444_, 2);
v___f_1447_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1447_, 0, v___y_1444_);
lean_closure_set(v___f_1447_, 1, v___f_1443_);
v___f_1448_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1448_, 0, v___y_1444_);
lean_closure_set(v___f_1448_, 1, v___f_1447_);
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = 0;
v___x_1451_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1449_, v___x_1450_, v___x_1446_, v___f_1448_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed(lean_object* v___f_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_Http_Body_Stream_tryRecvBody___lam__3(v___f_1452_, v___y_1453_);
lean_dec(v___y_1453_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody(lean_object* v_stream_1459_){
_start:
{
lean_object* v___f_1461_; lean_object* v___x_1462_; 
v___f_1461_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_1462_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1459_, v___f_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___boxed(lean_object* v_stream_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v_pendingProducer_1469_; lean_object* v_pendingConsumer_1470_; lean_object* v_interestWaiter_1471_; uint8_t v_closed_1472_; lean_object* v_knownSize_1473_; lean_object* v_pendingIncompleteChunk_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1500_; 
v___x_1468_ = lean_st_ref_get(v_a_1466_);
v_pendingProducer_1469_ = lean_ctor_get(v___x_1468_, 0);
v_pendingConsumer_1470_ = lean_ctor_get(v___x_1468_, 1);
v_interestWaiter_1471_ = lean_ctor_get(v___x_1468_, 2);
v_closed_1472_ = lean_ctor_get_uint8(v___x_1468_, sizeof(void*)*5);
v_knownSize_1473_ = lean_ctor_get(v___x_1468_, 3);
v_pendingIncompleteChunk_1474_ = lean_ctor_get(v___x_1468_, 4);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1476_ = v___x_1468_;
v_isShared_1477_ = v_isSharedCheck_1500_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1474_);
lean_inc(v_knownSize_1473_);
lean_inc(v_interestWaiter_1471_);
lean_inc(v_pendingConsumer_1470_);
lean_inc(v_pendingProducer_1469_);
lean_dec(v___x_1468_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1500_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___y_1479_; lean_object* v_interestWaiter_1480_; lean_object* v___y_1481_; lean_object* v_pendingConsumer_1487_; lean_object* v___y_1488_; 
if (lean_obj_tag(v_pendingConsumer_1470_) == 1)
{
lean_object* v_val_1494_; 
v_val_1494_ = lean_ctor_get(v_pendingConsumer_1470_, 0);
if (lean_obj_tag(v_val_1494_) == 1)
{
lean_object* v_finished_1495_; lean_object* v_finished_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v_finished_1495_ = lean_ctor_get(v_val_1494_, 0);
v_finished_1496_ = lean_ctor_get(v_finished_1495_, 0);
v___x_1497_ = lean_st_ref_get(v_finished_1496_);
v___x_1498_ = lean_unbox(v___x_1497_);
lean_dec(v___x_1497_);
if (v___x_1498_ == 0)
{
v_pendingConsumer_1487_ = v_pendingConsumer_1470_;
v___y_1488_ = v_a_1466_;
goto v___jp_1486_;
}
else
{
lean_object* v___x_1499_; 
lean_dec_ref(v_pendingConsumer_1470_);
v___x_1499_ = lean_box(0);
v_pendingConsumer_1487_ = v___x_1499_;
v___y_1488_ = v_a_1466_;
goto v___jp_1486_;
}
}
else
{
v_pendingConsumer_1487_ = v_pendingConsumer_1470_;
v___y_1488_ = v_a_1466_;
goto v___jp_1486_;
}
}
else
{
v_pendingConsumer_1487_ = v_pendingConsumer_1470_;
v___y_1488_ = v_a_1466_;
goto v___jp_1486_;
}
v___jp_1478_:
{
lean_object* v___x_1483_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 2, v_interestWaiter_1480_);
lean_ctor_set(v___x_1476_, 1, v___y_1479_);
v___x_1483_ = v___x_1476_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_pendingProducer_1469_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___y_1479_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_interestWaiter_1480_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_knownSize_1473_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_pendingIncompleteChunk_1474_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*5, v_closed_1472_);
v___x_1483_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_st_ref_set(v___y_1481_, v___x_1483_);
return v___x_1484_;
}
}
v___jp_1486_:
{
if (lean_obj_tag(v_interestWaiter_1471_) == 0)
{
v___y_1479_ = v_pendingConsumer_1487_;
v_interestWaiter_1480_ = v_interestWaiter_1471_;
v___y_1481_ = v___y_1488_;
goto v___jp_1478_;
}
else
{
lean_object* v_val_1489_; lean_object* v_finished_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_val_1489_ = lean_ctor_get(v_interestWaiter_1471_, 0);
v_finished_1490_ = lean_ctor_get(v_val_1489_, 0);
v___x_1491_ = lean_st_ref_get(v_finished_1490_);
v___x_1492_ = lean_unbox(v___x_1491_);
lean_dec(v___x_1491_);
if (v___x_1492_ == 0)
{
v___y_1479_ = v_pendingConsumer_1487_;
v_interestWaiter_1480_ = v_interestWaiter_1471_;
v___y_1481_ = v___y_1488_;
goto v___jp_1478_;
}
else
{
lean_object* v___x_1493_; 
lean_dec_ref(v_interestWaiter_1471_);
v___x_1493_ = lean_box(0);
v___y_1479_ = v_pendingConsumer_1487_;
v_interestWaiter_1480_ = v___x_1493_;
v___y_1481_ = v___y_1488_;
goto v___jp_1478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object* v_a_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_1501_);
lean_dec(v_a_1501_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v_pendingProducer_1507_; 
v___x_1506_ = lean_st_ref_get(v_a_1504_);
v_pendingProducer_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_pendingProducer_1507_);
if (lean_obj_tag(v_pendingProducer_1507_) == 1)
{
lean_object* v_val_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1536_; 
v_val_1508_ = lean_ctor_get(v_pendingProducer_1507_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_pendingProducer_1507_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1510_ = v_pendingProducer_1507_;
v_isShared_1511_ = v_isSharedCheck_1536_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_val_1508_);
lean_dec(v_pendingProducer_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1536_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_pendingConsumer_1512_; lean_object* v_interestWaiter_1513_; uint8_t v_closed_1514_; lean_object* v_knownSize_1515_; lean_object* v_pendingIncompleteChunk_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1534_; 
v_pendingConsumer_1512_ = lean_ctor_get(v___x_1506_, 1);
v_interestWaiter_1513_ = lean_ctor_get(v___x_1506_, 2);
v_closed_1514_ = lean_ctor_get_uint8(v___x_1506_, sizeof(void*)*5);
v_knownSize_1515_ = lean_ctor_get(v___x_1506_, 3);
v_pendingIncompleteChunk_1516_ = lean_ctor_get(v___x_1506_, 4);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v___x_1506_, 0);
lean_dec(v_unused_1535_);
v___x_1518_ = v___x_1506_;
v_isShared_1519_ = v_isSharedCheck_1534_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1516_);
lean_inc(v_knownSize_1515_);
lean_inc(v_interestWaiter_1513_);
lean_inc(v_pendingConsumer_1512_);
lean_dec(v___x_1506_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1534_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_chunk_1520_; lean_object* v_done_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v_chunk_1520_ = lean_ctor_get(v_val_1508_, 0);
lean_inc_ref(v_chunk_1520_);
v_done_1521_ = lean_ctor_get(v_val_1508_, 1);
lean_inc(v_done_1521_);
lean_dec(v_val_1508_);
v___x_1522_ = lean_box(0);
v___x_1523_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1515_, v_chunk_1520_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 3, v___x_1523_);
lean_ctor_set(v___x_1518_, 0, v___x_1522_);
v___x_1525_ = v___x_1518_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_pendingConsumer_1512_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_interestWaiter_1513_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_pendingIncompleteChunk_1516_);
lean_ctor_set_uint8(v_reuseFailAlloc_1533_, sizeof(void*)*5, v_closed_1514_);
v___x_1525_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1526_ = lean_st_ref_set(v_a_1504_, v___x_1525_);
v___x_1527_ = 1;
v___x_1528_ = lean_box(v___x_1527_);
v___x_1529_ = lean_io_promise_resolve(v___x_1528_, v_done_1521_);
lean_dec(v_done_1521_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v_chunk_1520_);
v___x_1531_ = v___x_1510_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_chunk_1520_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
else
{
lean_object* v___x_1537_; 
lean_dec(v_pendingProducer_1507_);
lean_dec(v___x_1506_);
v___x_1537_ = lean_box(0);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object* v_a_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_1538_);
lean_dec(v_a_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1543_; lean_object* v_interestWaiter_1544_; 
v___x_1543_ = lean_st_ref_get(v_a_1541_);
v_interestWaiter_1544_ = lean_ctor_get(v___x_1543_, 2);
lean_inc(v_interestWaiter_1544_);
if (lean_obj_tag(v_interestWaiter_1544_) == 1)
{
lean_object* v_pendingProducer_1545_; lean_object* v_pendingConsumer_1546_; uint8_t v_closed_1547_; lean_object* v_knownSize_1548_; lean_object* v_pendingIncompleteChunk_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1561_; 
v_pendingProducer_1545_ = lean_ctor_get(v___x_1543_, 0);
v_pendingConsumer_1546_ = lean_ctor_get(v___x_1543_, 1);
v_closed_1547_ = lean_ctor_get_uint8(v___x_1543_, sizeof(void*)*5);
v_knownSize_1548_ = lean_ctor_get(v___x_1543_, 3);
v_pendingIncompleteChunk_1549_ = lean_ctor_get(v___x_1543_, 4);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v___x_1543_, 2);
lean_dec(v_unused_1562_);
v___x_1551_ = v___x_1543_;
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1549_);
lean_inc(v_knownSize_1548_);
lean_inc(v_pendingConsumer_1546_);
lean_inc(v_pendingProducer_1545_);
lean_dec(v___x_1543_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_val_1553_; uint8_t v___x_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v_val_1553_ = lean_ctor_get(v_interestWaiter_1544_, 0);
lean_inc(v_val_1553_);
lean_dec_ref(v_interestWaiter_1544_);
v___x_1554_ = 1;
v___x_1555_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1553_, v___x_1554_);
lean_dec(v_val_1553_);
v___x_1556_ = lean_box(0);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 2, v___x_1556_);
v___x_1558_ = v___x_1551_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_pendingProducer_1545_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_pendingConsumer_1546_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v_knownSize_1548_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v_pendingIncompleteChunk_1549_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*5, v_closed_1547_);
v___x_1558_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_st_ref_set(v_a_1541_, v___x_1558_);
return v___x_1559_;
}
}
}
else
{
lean_object* v___x_1563_; 
lean_dec(v_interestWaiter_1544_);
lean_dec(v___x_1543_);
v___x_1563_ = lean_box(0);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object* v_a_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_1564_);
lean_dec(v_a_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object* v_mutex_1567_, lean_object* v_k_1568_){
_start:
{
lean_object* v_ref_1570_; lean_object* v_mutex_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_ref_1570_ = lean_ctor_get(v_mutex_1567_, 0);
lean_inc(v_ref_1570_);
v_mutex_1571_ = lean_ctor_get(v_mutex_1567_, 1);
lean_inc(v_mutex_1571_);
lean_dec_ref(v_mutex_1567_);
v___x_1572_ = lean_io_basemutex_lock(v_mutex_1571_);
v___x_1573_ = lean_apply_2(v_k_1568_, v_ref_1570_, lean_box(0));
v___x_1574_ = lean_io_basemutex_unlock(v_mutex_1571_);
lean_dec(v_mutex_1571_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object* v_mutex_1575_, lean_object* v_k_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1575_, v_k_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object* v_00_u03b1_1579_, lean_object* v_00_u03b2_1580_, lean_object* v_mutex_1581_, lean_object* v_k_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1581_, v_k_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object* v_00_u03b1_1585_, lean_object* v_00_u03b2_1586_, lean_object* v_mutex_1587_, lean_object* v_k_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(v_00_u03b1_1585_, v_00_u03b2_1586_, v_mutex_1587_, v_k_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object* v_x_1596_){
_start:
{
if (lean_obj_tag(v_x_1596_) == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2));
return v___x_1597_;
}
else
{
lean_object* v_val_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_val_1598_ = lean_ctor_get(v_x_1596_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_x_1596_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v_x_1596_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_val_1598_);
lean_dec(v_x_1596_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_val_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2));
v___x_1612_ = lean_task_pure(v___x_1611_);
return v___x_1612_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0));
v___x_1614_ = lean_task_pure(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object* v___f_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_1616_);
v___x_1619_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_1616_);
if (lean_obj_tag(v___x_1619_) == 1)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec_ref(v___f_1615_);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
v___x_1621_ = lean_task_pure(v___x_1620_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; uint8_t v_closed_1623_; 
lean_dec(v___x_1619_);
v___x_1622_ = lean_st_ref_get(v___y_1616_);
v_closed_1623_ = lean_ctor_get_uint8(v___x_1622_, sizeof(void*)*5);
if (v_closed_1623_ == 0)
{
lean_object* v_pendingConsumer_1624_; 
v_pendingConsumer_1624_ = lean_ctor_get(v___x_1622_, 1);
lean_inc(v_pendingConsumer_1624_);
if (lean_obj_tag(v_pendingConsumer_1624_) == 0)
{
lean_object* v_pendingProducer_1625_; lean_object* v_interestWaiter_1626_; lean_object* v_knownSize_1627_; lean_object* v_pendingIncompleteChunk_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1644_; 
v_pendingProducer_1625_ = lean_ctor_get(v___x_1622_, 0);
v_interestWaiter_1626_ = lean_ctor_get(v___x_1622_, 2);
v_knownSize_1627_ = lean_ctor_get(v___x_1622_, 3);
v_pendingIncompleteChunk_1628_ = lean_ctor_get(v___x_1622_, 4);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v___x_1622_, 1);
lean_dec(v_unused_1645_);
v___x_1630_ = v___x_1622_;
v_isShared_1631_ = v_isSharedCheck_1644_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1628_);
lean_inc(v_knownSize_1627_);
lean_inc(v_interestWaiter_1626_);
lean_inc(v_pendingProducer_1625_);
lean_dec(v___x_1622_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1644_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1632_ = lean_io_promise_new();
lean_inc(v___x_1632_);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v___x_1634_);
v___x_1636_ = v___x_1630_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_pendingProducer_1625_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_interestWaiter_1626_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_knownSize_1627_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_pendingIncompleteChunk_1628_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, sizeof(void*)*5, v_closed_1623_);
v___x_1636_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1637_ = lean_st_ref_set(v___y_1616_, v___x_1636_);
v___x_1638_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_1616_);
v___x_1639_ = 1;
v___x_1640_ = lean_io_promise_result_opt(v___x_1632_);
lean_dec(v___x_1632_);
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = lean_task_map(v___f_1615_, v___x_1640_, v___x_1641_, v___x_1639_);
return v___x_1642_;
}
}
}
else
{
lean_object* v___x_1646_; 
lean_dec_ref(v_pendingConsumer_1624_);
lean_dec(v___x_1622_);
lean_dec_ref(v___f_1615_);
v___x_1646_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3);
return v___x_1646_;
}
}
else
{
lean_object* v___x_1647_; 
lean_dec(v___x_1622_);
lean_dec_ref(v___f_1615_);
v___x_1647_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4);
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object* v___f_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(v___f_1648_, v___y_1649_);
lean_dec(v___y_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object* v_stream_1655_){
_start:
{
lean_object* v___f_1657_; lean_object* v___x_1658_; 
v___f_1657_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1));
v___x_1658_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_1655_, v___f_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object* v_stream_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object* v_x_1662_){
_start:
{
if (lean_obj_tag(v_x_1662_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
v_a_1664_ = lean_ctor_get(v_x_1662_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_x_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v_x_1662_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v_x_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1674_; 
v_a_1673_ = lean_ctor_get(v_x_1662_, 0);
lean_inc(v_a_1673_);
lean_dec_ref(v_x_1662_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_a_1673_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object* v_x_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv(lean_object* v_stream_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v___f_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; 
v___x_1681_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1679_);
v___f_1682_ = ((lean_object*)(l_Std_Http_Body_Stream_recv___closed__0));
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = 0;
v___x_1687_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1685_, v___x_1686_, v___x_1684_, v___f_1682_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object* v_stream_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_Http_Body_Stream_recv(v_stream_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(uint8_t v___x_1691_, lean_object* v_knownSize_1692_, lean_object* v_____r_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1696_ = lean_box(0);
v___x_1697_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
lean_ctor_set(v___x_1697_, 3, v_knownSize_1692_);
lean_ctor_set(v___x_1697_, 4, v___x_1696_);
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*5, v___x_1691_);
v___x_1698_ = lean_st_ref_set(v___y_1694_, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(lean_object* v___x_1701_, lean_object* v_knownSize_1702_, lean_object* v_____r_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v___x_2149__boxed_1706_; lean_object* v_res_1707_; 
v___x_2149__boxed_1706_ = lean_unbox(v___x_1701_);
v_res_1707_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(v___x_2149__boxed_1706_, v_knownSize_1702_, v_____r_1703_, v___y_1704_);
lean_dec(v___y_1704_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(lean_object* v___f_1708_, lean_object* v___y_1709_, lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v___x_1712_; 
lean_dec_ref(v___f_1708_);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_x_1710_);
return v___x_1712_;
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1714_; 
v_a_1713_ = lean_ctor_get(v_x_1710_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v_x_1710_);
lean_inc(v___y_1709_);
v___x_1714_ = lean_apply_3(v___f_1708_, v_a_1713_, v___y_1709_, lean_box(0));
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed(lean_object* v___f_1715_, lean_object* v___y_1716_, lean_object* v_x_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(v___f_1715_, v___y_1716_, v_x_1717_);
lean_dec(v___y_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object* v_pendingProducer_1720_, uint8_t v_closed_1721_, lean_object* v___f_1722_, lean_object* v_____r_1723_, lean_object* v___y_1724_){
_start:
{
if (lean_obj_tag(v_pendingProducer_1720_) == 1)
{
lean_object* v_val_1726_; lean_object* v_done_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___f_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_val_1726_ = lean_ctor_get(v_pendingProducer_1720_, 0);
v_done_1727_ = lean_ctor_get(v_val_1726_, 1);
v___x_1728_ = lean_box(v_closed_1721_);
v___x_1729_ = lean_io_promise_resolve(v___x_1728_, v_done_1727_);
lean_inc(v___y_1724_);
v___f_1730_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1730_, 0, v___f_1722_);
lean_closure_set(v___f_1730_, 1, v___y_1724_);
v___x_1731_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_1732_ = lean_unsigned_to_nat(0u);
v___x_1733_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1732_, v_closed_1721_, v___x_1731_, v___f_1730_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_box(0);
lean_inc(v___y_1724_);
v___x_1735_ = lean_apply_3(v___f_1722_, v___x_1734_, v___y_1724_, lean_box(0));
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object* v_pendingProducer_1736_, lean_object* v_closed_1737_, lean_object* v___f_1738_, lean_object* v_____r_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v_closed_boxed_1742_; lean_object* v_res_1743_; 
v_closed_boxed_1742_ = lean_unbox(v_closed_1737_);
v_res_1743_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(v_pendingProducer_1736_, v_closed_boxed_1742_, v___f_1738_, v_____r_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec(v_pendingProducer_1736_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object* v_interestWaiter_1744_, uint8_t v_closed_1745_, lean_object* v___f_1746_, lean_object* v_____r_1747_, lean_object* v___y_1748_){
_start:
{
if (lean_obj_tag(v_interestWaiter_1744_) == 1)
{
lean_object* v_val_1750_; uint8_t v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_val_1750_ = lean_ctor_get(v_interestWaiter_1744_, 0);
v___x_1751_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1750_, v_closed_1745_);
lean_inc(v___y_1748_);
v___f_1752_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1752_, 0, v___f_1746_);
lean_closure_set(v___f_1752_, 1, v___y_1748_);
v___x_1753_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1754_, v_closed_1745_, v___x_1753_, v___f_1752_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_box(0);
lean_inc(v___y_1748_);
v___x_1757_ = lean_apply_3(v___f_1746_, v___x_1756_, v___y_1748_, lean_box(0));
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(lean_object* v_interestWaiter_1758_, lean_object* v_closed_1759_, lean_object* v___f_1760_, lean_object* v_____r_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v_closed_boxed_1764_; lean_object* v_res_1765_; 
v_closed_boxed_1764_ = lean_unbox(v_closed_1759_);
v_res_1765_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_1758_, v_closed_boxed_1764_, v___f_1760_, v_____r_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec(v_interestWaiter_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(lean_object* v___f_1766_, lean_object* v_a_1767_, lean_object* v_x_1768_){
_start:
{
if (lean_obj_tag(v_x_1768_) == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref(v___f_1766_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_x_1768_);
return v___x_1770_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v_x_1768_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v_x_1768_);
lean_inc(v_a_1767_);
v___x_1772_ = lean_apply_3(v___f_1766_, v_a_1771_, v_a_1767_, lean_box(0));
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed(lean_object* v___f_1773_, lean_object* v_a_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(v___f_1773_, v_a_1774_, v_x_1775_);
lean_dec(v_a_1774_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(lean_object* v_a_1778_, lean_object* v_x_1779_){
_start:
{
if (lean_obj_tag(v_x_1779_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1789_; 
v_a_1781_ = lean_ctor_get(v_x_1779_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_x_1779_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1783_ = v_x_1779_;
v_isShared_1784_ = v_isSharedCheck_1789_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v_x_1779_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1789_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
}
else
{
lean_object* v_a_1790_; uint8_t v_closed_1791_; 
v_a_1790_ = lean_ctor_get(v_x_1779_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v_x_1779_);
v_closed_1791_ = lean_ctor_get_uint8(v_a_1790_, sizeof(void*)*5);
if (v_closed_1791_ == 0)
{
lean_object* v_pendingProducer_1792_; lean_object* v_pendingConsumer_1793_; lean_object* v_interestWaiter_1794_; lean_object* v_knownSize_1795_; uint8_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___f_1798_; lean_object* v___x_1799_; lean_object* v___f_1800_; lean_object* v___x_1801_; lean_object* v___f_1802_; 
v_pendingProducer_1792_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_pendingProducer_1792_);
v_pendingConsumer_1793_ = lean_ctor_get(v_a_1790_, 1);
lean_inc(v_pendingConsumer_1793_);
v_interestWaiter_1794_ = lean_ctor_get(v_a_1790_, 2);
lean_inc_n(v_interestWaiter_1794_, 2);
v_knownSize_1795_ = lean_ctor_get(v_a_1790_, 3);
lean_inc(v_knownSize_1795_);
lean_dec(v_a_1790_);
v___x_1796_ = 1;
v___x_1797_ = lean_box(v___x_1796_);
v___f_1798_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1798_, 0, v___x_1797_);
lean_closure_set(v___f_1798_, 1, v_knownSize_1795_);
v___x_1799_ = lean_box(v_closed_1791_);
v___f_1800_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1800_, 0, v_pendingProducer_1792_);
lean_closure_set(v___f_1800_, 1, v___x_1799_);
lean_closure_set(v___f_1800_, 2, v___f_1798_);
v___x_1801_ = lean_box(v_closed_1791_);
lean_inc_ref(v___f_1800_);
v___f_1802_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1802_, 0, v_interestWaiter_1794_);
lean_closure_set(v___f_1802_, 1, v___x_1801_);
lean_closure_set(v___f_1802_, 2, v___f_1800_);
if (lean_obj_tag(v_pendingConsumer_1793_) == 1)
{
lean_object* v_val_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec_ref(v___f_1800_);
lean_dec(v_interestWaiter_1794_);
v_val_1803_ = lean_ctor_get(v_pendingConsumer_1793_, 0);
lean_inc(v_val_1803_);
lean_dec_ref(v_pendingConsumer_1793_);
v___x_1804_ = lean_box(0);
v___x_1805_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_1803_, v___x_1804_);
lean_dec(v_val_1803_);
lean_inc(v_a_1778_);
v___f_1806_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1806_, 0, v___f_1802_);
lean_closure_set(v___f_1806_, 1, v_a_1778_);
v___x_1807_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1808_, v_closed_1791_, v___x_1807_, v___f_1806_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec_ref(v___f_1802_);
lean_dec(v_pendingConsumer_1793_);
v___x_1810_ = lean_box(0);
v___x_1811_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_1794_, v_closed_1791_, v___f_1800_, v___x_1810_, v_a_1778_);
lean_dec(v_interestWaiter_1794_);
return v___x_1811_;
}
}
else
{
lean_object* v___x_1812_; 
lean_dec(v_a_1790_);
v___x_1812_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_1812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed(lean_object* v_a_1813_, lean_object* v_x_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(v_a_1813_, v_x_1814_);
lean_dec(v_a_1813_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(lean_object* v_a_1817_){
_start:
{
lean_object* v___x_1819_; lean_object* v___f_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1819_ = lean_st_ref_get(v_a_1817_);
lean_inc(v_a_1817_);
v___f_1820_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1820_, 0, v_a_1817_);
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = 0;
v___x_1825_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1823_, v___x_1824_, v___x_1822_, v___f_1820_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed(lean_object* v_a_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v_a_1826_);
lean_dec(v_a_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close(lean_object* v_stream_1830_){
_start:
{
lean_object* v___f_1832_; lean_object* v___x_1833_; 
v___f_1832_ = ((lean_object*)(l_Std_Http_Body_Stream_close___closed__0));
v___x_1833_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1830_, v___f_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object* v_stream_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Std_Http_Body_Stream_close(v_stream_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object* v_____do__lift_1837_, lean_object* v___y_1838_){
_start:
{
uint8_t v_closed_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_closed_1840_ = lean_ctor_get_uint8(v_____do__lift_1837_, sizeof(void*)*5);
v___x_1841_ = lean_box(v_closed_1840_);
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object* v_____do__lift_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v_____do__lift_1844_);
return v_res_1847_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__1(void){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1849_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__2(void){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_1850_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__6(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___f_1857_; lean_object* v___f_1858_; 
v___x_1856_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_1857_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___f_1858_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1858_, 0, v___f_1857_);
lean_closure_set(v___f_1858_, 1, v___x_1856_);
return v___f_1858_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__11(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___f_1868_; lean_object* v___f_1869_; 
v___x_1867_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_1868_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__10));
v___f_1869_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1869_, 0, v___f_1868_);
lean_closure_set(v___f_1869_, 1, v___x_1867_);
return v___f_1869_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__12(void){
_start:
{
lean_object* v___f_1870_; lean_object* v___x_1871_; 
v___f_1870_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__11, &l_Std_Http_Body_Stream_isClosed___closed__11_once, _init_l_Std_Http_Body_Stream_isClosed___closed__11);
v___x_1871_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1871_, 0, lean_box(0));
lean_closure_set(v___x_1871_, 1, lean_box(0));
lean_closure_set(v___x_1871_, 2, lean_box(0));
lean_closure_set(v___x_1871_, 3, v___f_1870_);
return v___x_1871_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__13(void){
_start:
{
lean_object* v___f_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___f_1872_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__0));
v___x_1873_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_1874_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_1875_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_1875_, 0, lean_box(0));
lean_closure_set(v___x_1875_, 1, lean_box(0));
lean_closure_set(v___x_1875_, 2, lean_box(0));
lean_closure_set(v___x_1875_, 3, v___x_1874_);
lean_closure_set(v___x_1875_, 4, lean_box(0));
lean_closure_set(v___x_1875_, 5, lean_box(0));
lean_closure_set(v___x_1875_, 6, v___x_1873_);
lean_closure_set(v___x_1875_, 7, v___f_1872_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed(lean_object* v_stream_1876_){
_start:
{
lean_object* v___x_1878_; lean_object* v___f_1879_; lean_object* v___f_1880_; lean_object* v___x_1881_; lean_object* v___x_29__overap_1882_; lean_object* v___x_1883_; 
v___x_1878_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_1879_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_1880_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_1881_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__13, &l_Std_Http_Body_Stream_isClosed___closed__13_once, _init_l_Std_Http_Body_Stream_isClosed___closed__13);
v___x_29__overap_1882_ = l_Std_Mutex_atomically___redArg(v___x_1878_, v___f_1879_, v___f_1880_, v_stream_1876_, v___x_1881_);
v___x_1883_ = lean_apply_1(v___x_29__overap_1882_, lean_box(0));
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___boxed(lean_object* v_stream_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Std_Http_Body_Stream_isClosed(v_stream_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0(lean_object* v_____do__lift_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_knownSize_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_knownSize_1890_ = lean_ctor_get(v_____do__lift_1887_, 3);
lean_inc(v_knownSize_1890_);
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_knownSize_1890_);
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(lean_object* v_____do__lift_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v_____do__lift_1893_);
return v_res_1896_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_getKnownSize___closed__1(void){
_start:
{
lean_object* v___f_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___f_1898_ = ((lean_object*)(l_Std_Http_Body_Stream_getKnownSize___closed__0));
v___x_1899_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_1900_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_1901_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_1901_, 0, lean_box(0));
lean_closure_set(v___x_1901_, 1, lean_box(0));
lean_closure_set(v___x_1901_, 2, lean_box(0));
lean_closure_set(v___x_1901_, 3, v___x_1900_);
lean_closure_set(v___x_1901_, 4, lean_box(0));
lean_closure_set(v___x_1901_, 5, lean_box(0));
lean_closure_set(v___x_1901_, 6, v___x_1899_);
lean_closure_set(v___x_1901_, 7, v___f_1898_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize(lean_object* v_stream_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v___f_1905_; lean_object* v___f_1906_; lean_object* v___x_1907_; lean_object* v___x_29__overap_1908_; lean_object* v___x_1909_; 
v___x_1904_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_1905_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_1906_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_1907_ = lean_obj_once(&l_Std_Http_Body_Stream_getKnownSize___closed__1, &l_Std_Http_Body_Stream_getKnownSize___closed__1_once, _init_l_Std_Http_Body_Stream_getKnownSize___closed__1);
v___x_29__overap_1908_ = l_Std_Mutex_atomically___redArg(v___x_1904_, v___f_1905_, v___f_1906_, v_stream_1902_, v___x_1907_);
v___x_1909_ = lean_apply_1(v___x_29__overap_1908_, lean_box(0));
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___boxed(lean_object* v_stream_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0(lean_object* v_size_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v_pendingProducer_1917_; lean_object* v_pendingConsumer_1918_; lean_object* v_interestWaiter_1919_; uint8_t v_closed_1920_; lean_object* v_pendingIncompleteChunk_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1930_; 
v___x_1916_ = lean_st_ref_take(v___y_1914_);
v_pendingProducer_1917_ = lean_ctor_get(v___x_1916_, 0);
v_pendingConsumer_1918_ = lean_ctor_get(v___x_1916_, 1);
v_interestWaiter_1919_ = lean_ctor_get(v___x_1916_, 2);
v_closed_1920_ = lean_ctor_get_uint8(v___x_1916_, sizeof(void*)*5);
v_pendingIncompleteChunk_1921_ = lean_ctor_get(v___x_1916_, 4);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v___x_1916_, 3);
lean_dec(v_unused_1931_);
v___x_1923_ = v___x_1916_;
v_isShared_1924_ = v_isSharedCheck_1930_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1921_);
lean_inc(v_interestWaiter_1919_);
lean_inc(v_pendingConsumer_1918_);
lean_inc(v_pendingProducer_1917_);
lean_dec(v___x_1916_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1930_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 3, v_size_1913_);
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_pendingProducer_1917_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_pendingConsumer_1918_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_interestWaiter_1919_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_size_1913_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v_pendingIncompleteChunk_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*5, v_closed_1920_);
v___x_1926_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_st_ref_set(v___y_1914_, v___x_1926_);
v___x_1928_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(lean_object* v_size_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_1932_, v___y_1933_);
lean_dec(v___y_1933_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize(lean_object* v_stream_1936_, lean_object* v_size_1937_){
_start:
{
lean_object* v___f_1939_; lean_object* v___x_1940_; lean_object* v___f_1941_; lean_object* v___f_1942_; lean_object* v___x_25__overap_1943_; lean_object* v___x_1944_; 
v___f_1939_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1939_, 0, v_size_1937_);
v___x_1940_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_1941_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_1942_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_25__overap_1943_ = l_Std_Mutex_atomically___redArg(v___x_1940_, v___f_1941_, v___f_1942_, v_stream_1936_, v___f_1939_);
v___x_1944_ = lean_apply_1(v___x_25__overap_1943_, lean_box(0));
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___boxed(lean_object* v_stream_1945_, lean_object* v_size_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_1945_, v_size_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object* v_pendingProducer_1949_, lean_object* v_pendingConsumer_1950_, uint8_t v_closed_1951_, lean_object* v_knownSize_1952_, lean_object* v_pendingIncompleteChunk_1953_, lean_object* v_a_1954_, lean_object* v_x_1955_){
_start:
{
if (lean_obj_tag(v_x_1955_) == 0)
{
lean_object* v___x_1957_; 
lean_dec(v_pendingIncompleteChunk_1953_);
lean_dec(v_knownSize_1952_);
lean_dec(v_pendingConsumer_1950_);
lean_dec(v_pendingProducer_1949_);
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v_x_1955_);
return v___x_1957_;
}
else
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1968_; 
v_isSharedCheck_1968_ = !lean_is_exclusive(v_x_1955_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v_x_1955_, 0);
lean_dec(v_unused_1969_);
v___x_1959_ = v_x_1955_;
v_isShared_1960_ = v_isSharedCheck_1968_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v_x_1955_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1968_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1962_, 0, v_pendingProducer_1949_);
lean_ctor_set(v___x_1962_, 1, v_pendingConsumer_1950_);
lean_ctor_set(v___x_1962_, 2, v___x_1961_);
lean_ctor_set(v___x_1962_, 3, v_knownSize_1952_);
lean_ctor_set(v___x_1962_, 4, v_pendingIncompleteChunk_1953_);
lean_ctor_set_uint8(v___x_1962_, sizeof(void*)*5, v_closed_1951_);
v___x_1963_ = lean_st_ref_set(v_a_1954_, v___x_1962_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1963_);
v___x_1965_ = v___x_1959_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object* v_pendingProducer_1970_, lean_object* v_pendingConsumer_1971_, lean_object* v_closed_1972_, lean_object* v_knownSize_1973_, lean_object* v_pendingIncompleteChunk_1974_, lean_object* v_a_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v_closed_boxed_1978_; lean_object* v_res_1979_; 
v_closed_boxed_1978_ = lean_unbox(v_closed_1972_);
v_res_1979_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_1970_, v_pendingConsumer_1971_, v_closed_boxed_1978_, v_knownSize_1973_, v_pendingIncompleteChunk_1974_, v_a_1975_, v_x_1976_);
lean_dec(v_a_1975_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object* v_a_1980_, lean_object* v_x_1981_){
_start:
{
if (lean_obj_tag(v_x_1981_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1991_; 
v_a_1983_ = lean_ctor_get(v_x_1981_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_x_1981_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1985_ = v_x_1981_;
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v_x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v_interestWaiter_1993_; 
v_a_1992_ = lean_ctor_get(v_x_1981_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v_x_1981_);
v_interestWaiter_1993_ = lean_ctor_get(v_a_1992_, 2);
lean_inc(v_interestWaiter_1993_);
if (lean_obj_tag(v_interestWaiter_1993_) == 1)
{
lean_object* v_pendingProducer_1994_; lean_object* v_pendingConsumer_1995_; uint8_t v_closed_1996_; lean_object* v_knownSize_1997_; lean_object* v_pendingIncompleteChunk_1998_; lean_object* v_val_1999_; uint8_t v___x_2000_; uint8_t v___x_2001_; lean_object* v___x_2002_; lean_object* v___f_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; 
v_pendingProducer_1994_ = lean_ctor_get(v_a_1992_, 0);
lean_inc(v_pendingProducer_1994_);
v_pendingConsumer_1995_ = lean_ctor_get(v_a_1992_, 1);
lean_inc(v_pendingConsumer_1995_);
v_closed_1996_ = lean_ctor_get_uint8(v_a_1992_, sizeof(void*)*5);
v_knownSize_1997_ = lean_ctor_get(v_a_1992_, 3);
lean_inc(v_knownSize_1997_);
v_pendingIncompleteChunk_1998_ = lean_ctor_get(v_a_1992_, 4);
lean_inc(v_pendingIncompleteChunk_1998_);
lean_dec(v_a_1992_);
v_val_1999_ = lean_ctor_get(v_interestWaiter_1993_, 0);
lean_inc(v_val_1999_);
lean_dec_ref(v_interestWaiter_1993_);
v___x_2000_ = 1;
v___x_2001_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1999_, v___x_2000_);
lean_dec(v_val_1999_);
v___x_2002_ = lean_box(v_closed_1996_);
lean_inc(v_a_1980_);
v___f_2003_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed), 8, 6);
lean_closure_set(v___f_2003_, 0, v_pendingProducer_1994_);
lean_closure_set(v___f_2003_, 1, v_pendingConsumer_1995_);
lean_closure_set(v___f_2003_, 2, v___x_2002_);
lean_closure_set(v___f_2003_, 3, v_knownSize_1997_);
lean_closure_set(v___f_2003_, 4, v_pendingIncompleteChunk_1998_);
lean_closure_set(v___f_2003_, 5, v_a_1980_);
v___x_2004_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = 0;
v___x_2007_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2005_, v___x_2006_, v___x_2004_, v___f_2003_);
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; 
lean_dec(v_interestWaiter_1993_);
lean_dec(v_a_1992_);
v___x_2008_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_2008_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object* v_a_2009_, lean_object* v_x_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_2009_, v_x_2010_);
lean_dec(v_a_2009_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object* v_a_2013_){
_start:
{
lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2015_ = lean_st_ref_get(v_a_2013_);
lean_inc(v_a_2013_);
v___f_2016_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2016_, 0, v_a_2013_);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = 0;
v___x_2021_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2019_, v___x_2020_, v___x_2018_, v___f_2016_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object* v_a_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_2022_);
lean_dec(v_a_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object* v_promise_2025_, lean_object* v_x_2026_){
_start:
{
if (lean_obj_tag(v_x_2026_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2036_; 
v_a_2028_ = lean_ctor_get(v_x_2026_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_x_2026_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2030_ = v_x_2026_;
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v_x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = lean_io_promise_resolve(v_x_2026_, v_promise_2025_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_2040_, lean_object* v_x_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(v_promise_2040_, v_x_2041_);
lean_dec(v_promise_2040_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object* v_lose_2044_, lean_object* v___y_2045_, lean_object* v___f_2046_, lean_object* v_x_2047_){
_start:
{
if (lean_obj_tag(v_x_2047_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v___f_2046_);
lean_dec_ref(v_lose_2044_);
v_a_2049_ = lean_ctor_get(v_x_2047_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_x_2047_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2051_ = v_x_2047_;
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v_x_2047_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
}
else
{
lean_object* v_a_2058_; uint8_t v___x_2059_; 
v_a_2058_ = lean_ctor_get(v_x_2047_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v_x_2047_);
v___x_2059_ = lean_unbox(v_a_2058_);
lean_dec(v_a_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
lean_dec_ref(v___f_2046_);
lean_inc(v___y_2045_);
v___x_2060_ = lean_apply_2(v_lose_2044_, v___y_2045_, lean_box(0));
return v___x_2060_;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; 
lean_dec_ref(v_lose_2044_);
v___x_2061_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2045_);
v___x_2062_ = lean_unsigned_to_nat(0u);
v___x_2063_ = 0;
v___x_2064_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2062_, v___x_2063_, v___x_2061_, v___f_2046_);
return v___x_2064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object* v_lose_2065_, lean_object* v___y_2066_, lean_object* v___f_2067_, lean_object* v_x_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(v_lose_2065_, v___y_2066_, v___f_2067_, v_x_2068_);
lean_dec(v___y_2066_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object* v_w_2071_, lean_object* v_lose_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_finished_2075_; lean_object* v_promise_2076_; lean_object* v___x_2077_; lean_object* v___f_2078_; lean_object* v___f_2079_; uint8_t v___y_2081_; uint8_t v___x_2091_; 
v_finished_2075_ = lean_ctor_get(v_w_2071_, 0);
lean_inc(v_finished_2075_);
v_promise_2076_ = lean_ctor_get(v_w_2071_, 1);
lean_inc(v_promise_2076_);
lean_dec_ref(v_w_2071_);
v___x_2077_ = lean_st_ref_take(v_finished_2075_);
v___f_2078_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2078_, 0, v_promise_2076_);
lean_inc(v___y_2073_);
v___f_2079_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2079_, 0, v_lose_2072_);
lean_closure_set(v___f_2079_, 1, v___y_2073_);
lean_closure_set(v___f_2079_, 2, v___f_2078_);
v___x_2091_ = lean_unbox(v___x_2077_);
lean_dec(v___x_2077_);
if (v___x_2091_ == 0)
{
uint8_t v___x_2092_; 
v___x_2092_ = 1;
v___y_2081_ = v___x_2092_;
goto v___jp_2080_;
}
else
{
uint8_t v___x_2093_; 
v___x_2093_ = 0;
v___y_2081_ = v___x_2093_;
goto v___jp_2080_;
}
v___jp_2080_:
{
uint8_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2082_ = 1;
v___x_2083_ = lean_box(v___x_2082_);
v___x_2084_ = lean_st_ref_set(v_finished_2075_, v___x_2083_);
lean_dec(v_finished_2075_);
v___x_2085_ = lean_box(v___y_2081_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = 0;
v___x_2090_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2088_, v___x_2089_, v___x_2087_, v___f_2079_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object* v_w_2094_, lean_object* v_lose_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_2094_, v_lose_2095_, v___y_2096_);
lean_dec(v___y_2096_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object* v___y_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v_x_2100_);
return v___x_2102_;
}
else
{
lean_object* v___x_2103_; 
lean_dec_ref(v_x_2100_);
v___x_2103_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_2099_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object* v___y_2104_, lean_object* v_x_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_2104_, v_x_2105_);
lean_dec(v___y_2104_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object* v_waiter_2108_, lean_object* v_pendingProducer_2109_, lean_object* v_interestWaiter_2110_, uint8_t v_closed_2111_, lean_object* v_knownSize_2112_, lean_object* v_pendingIncompleteChunk_2113_, uint8_t v_a_2114_, lean_object* v_____r_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___f_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_waiter_2108_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2120_, 0, v_pendingProducer_2109_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
lean_ctor_set(v___x_2120_, 2, v_interestWaiter_2110_);
lean_ctor_set(v___x_2120_, 3, v_knownSize_2112_);
lean_ctor_set(v___x_2120_, 4, v_pendingIncompleteChunk_2113_);
lean_ctor_set_uint8(v___x_2120_, sizeof(void*)*5, v_closed_2111_);
v___x_2121_ = lean_st_ref_set(v___y_2116_, v___x_2120_);
lean_inc(v___y_2116_);
v___f_2122_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2122_, 0, v___y_2116_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2121_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2125_, v_a_2114_, v___x_2124_, v___f_2122_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object* v_waiter_2127_, lean_object* v_pendingProducer_2128_, lean_object* v_interestWaiter_2129_, lean_object* v_closed_2130_, lean_object* v_knownSize_2131_, lean_object* v_pendingIncompleteChunk_2132_, lean_object* v_a_2133_, lean_object* v_____r_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
uint8_t v_closed_boxed_2137_; uint8_t v_a_6061__boxed_2138_; lean_object* v_res_2139_; 
v_closed_boxed_2137_ = lean_unbox(v_closed_2130_);
v_a_6061__boxed_2138_ = lean_unbox(v_a_2133_);
v_res_2139_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2127_, v_pendingProducer_2128_, v_interestWaiter_2129_, v_closed_boxed_2137_, v_knownSize_2131_, v_pendingIncompleteChunk_2132_, v_a_6061__boxed_2138_, v_____r_2134_, v___y_2135_);
lean_dec(v___y_2135_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object* v_waiter_2144_, uint8_t v_a_2145_, lean_object* v___y_2146_, lean_object* v_x_2147_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v_waiter_2144_);
v_a_2149_ = lean_ctor_get(v_x_2147_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_x_2147_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2151_ = v_x_2147_;
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v_x_2147_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v_pendingProducer_2159_; lean_object* v_pendingConsumer_2160_; lean_object* v_interestWaiter_2161_; uint8_t v_closed_2162_; lean_object* v_knownSize_2163_; lean_object* v_pendingIncompleteChunk_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___f_2167_; 
v_a_2158_ = lean_ctor_get(v_x_2147_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v_x_2147_);
v_pendingProducer_2159_ = lean_ctor_get(v_a_2158_, 0);
lean_inc_n(v_pendingProducer_2159_, 2);
v_pendingConsumer_2160_ = lean_ctor_get(v_a_2158_, 1);
lean_inc(v_pendingConsumer_2160_);
v_interestWaiter_2161_ = lean_ctor_get(v_a_2158_, 2);
lean_inc_n(v_interestWaiter_2161_, 2);
v_closed_2162_ = lean_ctor_get_uint8(v_a_2158_, sizeof(void*)*5);
v_knownSize_2163_ = lean_ctor_get(v_a_2158_, 3);
lean_inc_n(v_knownSize_2163_, 2);
v_pendingIncompleteChunk_2164_ = lean_ctor_get(v_a_2158_, 4);
lean_inc_n(v_pendingIncompleteChunk_2164_, 2);
lean_dec(v_a_2158_);
v___x_2165_ = lean_box(v_closed_2162_);
v___x_2166_ = lean_box(v_a_2145_);
lean_inc_ref(v_waiter_2144_);
v___f_2167_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__0___boxed), 10, 7);
lean_closure_set(v___f_2167_, 0, v_waiter_2144_);
lean_closure_set(v___f_2167_, 1, v_pendingProducer_2159_);
lean_closure_set(v___f_2167_, 2, v_interestWaiter_2161_);
lean_closure_set(v___f_2167_, 3, v___x_2165_);
lean_closure_set(v___f_2167_, 4, v_knownSize_2163_);
lean_closure_set(v___f_2167_, 5, v_pendingIncompleteChunk_2164_);
lean_closure_set(v___f_2167_, 6, v___x_2166_);
if (lean_obj_tag(v_pendingConsumer_2160_) == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec_ref(v___f_2167_);
v___x_2168_ = lean_box(0);
v___x_2169_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2144_, v_pendingProducer_2159_, v_interestWaiter_2161_, v_closed_2162_, v_knownSize_2163_, v_pendingIncompleteChunk_2164_, v_a_2145_, v___x_2168_, v___y_2146_);
return v___x_2169_;
}
else
{
lean_object* v___f_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref(v_pendingConsumer_2160_);
lean_dec(v_pendingIncompleteChunk_2164_);
lean_dec(v_knownSize_2163_);
lean_dec(v_interestWaiter_2161_);
lean_dec(v_pendingProducer_2159_);
lean_dec_ref(v_waiter_2144_);
lean_inc(v___y_2146_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2170_, 0, v___f_2167_);
lean_closure_set(v___f_2170_, 1, v___y_2146_);
v___x_2171_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1));
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2172_, v_a_2145_, v___x_2171_, v___f_2170_);
return v___x_2173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object* v_waiter_2174_, lean_object* v_a_2175_, lean_object* v___y_2176_, lean_object* v_x_2177_, lean_object* v___y_2178_){
_start:
{
uint8_t v_a_6102__boxed_2179_; lean_object* v_res_2180_; 
v_a_6102__boxed_2179_ = lean_unbox(v_a_2175_);
v_res_2180_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v_waiter_2174_, v_a_6102__boxed_2179_, v___y_2176_, v_x_2177_);
lean_dec(v___y_2176_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object* v___x_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2181_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object* v___x_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_2186_, v___y_2187_);
lean_dec(v___y_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object* v___y_2192_, lean_object* v_waiter_2193_, lean_object* v_x_2194_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v_waiter_2193_);
v_a_2196_ = lean_ctor_get(v_x_2194_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_x_2194_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2198_ = v_x_2194_;
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v_x_2194_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2221_; 
v_a_2205_ = lean_ctor_get(v_x_2194_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_x_2194_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2207_ = v_x_2194_;
v_isShared_2208_ = v_isSharedCheck_2221_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v_x_2194_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2221_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
uint8_t v___x_2209_; 
v___x_2209_ = lean_unbox(v_a_2205_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___f_2211_; lean_object* v___x_2213_; 
v___x_2210_ = lean_st_ref_get(v___y_2192_);
lean_inc(v___y_2192_);
lean_inc(v_a_2205_);
v___f_2211_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2211_, 0, v_waiter_2193_);
lean_closure_set(v___f_2211_, 1, v_a_2205_);
lean_closure_set(v___f_2211_, 2, v___y_2192_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2210_);
v___x_2213_ = v___x_2207_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2210_);
v___x_2213_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = lean_unbox(v_a_2205_);
lean_dec(v_a_2205_);
v___x_2217_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2215_, v___x_2216_, v___x_2214_, v___f_2211_);
return v___x_2217_;
}
}
else
{
lean_object* v___f_2219_; lean_object* v___x_2220_; 
lean_del_object(v___x_2207_);
lean_dec(v_a_2205_);
v___f_2219_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_2220_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_waiter_2193_, v___f_2219_, v___y_2192_);
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object* v___y_2222_, lean_object* v_waiter_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v___y_2222_, v_waiter_2223_, v_x_2224_);
lean_dec(v___y_2222_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object* v___y_2227_, lean_object* v___f_2228_, lean_object* v_x_2229_){
_start:
{
if (lean_obj_tag(v_x_2229_) == 0)
{
lean_object* v___x_2231_; 
lean_dec_ref(v___f_2228_);
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_x_2229_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; lean_object* v___x_2235_; 
lean_dec_ref(v_x_2229_);
v___x_2232_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_2227_);
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = 0;
v___x_2235_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2233_, v___x_2234_, v___x_2232_, v___f_2228_);
return v___x_2235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object* v___y_2236_, lean_object* v___f_2237_, lean_object* v_x_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_2236_, v___f_2237_, v_x_2238_);
lean_dec(v___y_2236_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object* v_waiter_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; 
v___x_2244_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2242_);
lean_inc_n(v___y_2242_, 2);
v___f_2245_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__4___boxed), 4, 2);
lean_closure_set(v___f_2245_, 0, v___y_2242_);
lean_closure_set(v___f_2245_, 1, v_waiter_2241_);
v___f_2246_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2246_, 0, v___y_2242_);
lean_closure_set(v___f_2246_, 1, v___f_2245_);
v___x_2247_ = lean_unsigned_to_nat(0u);
v___x_2248_ = 0;
v___x_2249_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2247_, v___x_2248_, v___x_2244_, v___f_2246_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object* v_waiter_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_2250_, v___y_2251_);
lean_dec(v___y_2251_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object* v_stream_2254_, lean_object* v_waiter_2255_){
_start:
{
lean_object* v___f_2257_; lean_object* v___x_2258_; 
v___f_2257_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2257_, 0, v_waiter_2255_);
v___x_2258_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2254_, v___f_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object* v_stream_2259_, lean_object* v_waiter_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_2259_, v_waiter_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object* v_stream_2264_){
_start:
{
lean_object* v___f_2265_; lean_object* v___f_2266_; lean_object* v___f_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___f_2265_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_2264_, 2);
v___f_2266_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2266_, 0, v_stream_2264_);
v___f_2267_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_2268_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2268_, 0, lean_box(0));
lean_closure_set(v___x_2268_, 1, lean_box(0));
lean_closure_set(v___x_2268_, 2, v_stream_2264_);
lean_closure_set(v___x_2268_, 3, v___f_2267_);
v___x_2269_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2269_, 0, lean_box(0));
lean_closure_set(v___x_2269_, 1, lean_box(0));
lean_closure_set(v___x_2269_, 2, v_stream_2264_);
lean_closure_set(v___x_2269_, 3, v___f_2265_);
v___x_2270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___f_2266_);
lean_ctor_set(v___x_2270_, 2, v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(lean_object* v_step_2271_, lean_object* v_acc_2272_, lean_object* v___f_2273_, lean_object* v_x_2274_){
_start:
{
if (lean_obj_tag(v_x_2274_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v___f_2273_);
lean_dec(v_acc_2272_);
lean_dec_ref(v_step_2271_);
v_a_2276_ = lean_ctor_get(v_x_2274_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_x_2274_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2278_ = v_x_2274_;
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v_x_2274_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
return v___x_2282_;
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2298_; 
v_a_2285_ = lean_ctor_get(v_x_2274_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_x_2274_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2287_ = v_x_2274_;
v_isShared_2288_ = v_isSharedCheck_2298_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v_x_2274_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2298_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
if (lean_obj_tag(v_a_2285_) == 1)
{
lean_object* v_val_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; 
lean_del_object(v___x_2287_);
v_val_2289_ = lean_ctor_get(v_a_2285_, 0);
lean_inc(v_val_2289_);
lean_dec_ref(v_a_2285_);
v___x_2290_ = lean_apply_3(v_step_2271_, v_val_2289_, v_acc_2272_, lean_box(0));
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = 0;
v___x_2293_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2291_, v___x_2292_, v___x_2290_, v___f_2273_);
return v___x_2293_;
}
else
{
lean_object* v___x_2295_; 
lean_dec(v_a_2285_);
lean_dec_ref(v___f_2273_);
lean_dec_ref(v_step_2271_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v_acc_2272_);
v___x_2295_ = v___x_2287_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_acc_2272_);
v___x_2295_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed(lean_object* v_step_2299_, lean_object* v_acc_2300_, lean_object* v___f_2301_, lean_object* v_x_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(v_step_2299_, v_acc_2300_, v___f_2301_, v_x_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(lean_object* v_step_2305_, lean_object* v_stream_2306_, lean_object* v_x_2307_){
_start:
{
if (lean_obj_tag(v_x_2307_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_stream_2306_);
lean_dec_ref(v_step_2305_);
v_a_2309_ = lean_ctor_get(v_x_2307_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_x_2307_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2311_ = v_x_2307_;
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v_x_2307_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
return v___x_2315_;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2335_; 
v_a_2318_ = lean_ctor_get(v_x_2307_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_x_2307_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2320_ = v_x_2307_;
v_isShared_2321_ = v_isSharedCheck_2335_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v_x_2307_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2335_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
if (lean_obj_tag(v_a_2318_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v_stream_2306_);
lean_dec_ref(v_step_2305_);
v_a_2322_ = lean_ctor_get(v_a_2318_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_a_2318_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2324_ = v_a_2318_;
v_isShared_2325_ = v_isSharedCheck_2332_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v_a_2318_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2332_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v_a_2322_);
v___x_2327_ = v___x_2320_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2327_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
lean_del_object(v___x_2320_);
v_a_2333_ = lean_ctor_get(v_a_2318_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v_a_2318_);
v___x_2334_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2305_, v_stream_2306_, v_a_2333_);
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed(lean_object* v_step_2336_, lean_object* v_stream_2337_, lean_object* v_x_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(v_step_2336_, v_stream_2337_, v_x_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(lean_object* v_step_2341_, lean_object* v_stream_2342_, lean_object* v_acc_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v___f_2346_; lean_object* v___f_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; 
lean_inc_ref(v_stream_2342_);
v___x_2345_ = l_Std_Http_Body_Stream_recv(v_stream_2342_);
lean_inc_ref(v_step_2341_);
v___f_2346_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2346_, 0, v_step_2341_);
lean_closure_set(v___f_2346_, 1, v_stream_2342_);
v___f_2347_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2347_, 0, v_step_2341_);
lean_closure_set(v___f_2347_, 1, v_acc_2343_);
lean_closure_set(v___f_2347_, 2, v___f_2346_);
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = 0;
v___x_2350_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2348_, v___x_2349_, v___x_2345_, v___f_2347_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___boxed(lean_object* v_step_2351_, lean_object* v_stream_2352_, lean_object* v_acc_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2351_, v_stream_2352_, v_acc_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(lean_object* v_00_u03b2_2356_, lean_object* v_step_2357_, lean_object* v_stream_2358_, lean_object* v_acc_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2357_, v_stream_2358_, v_acc_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___boxed(lean_object* v_00_u03b2_2362_, lean_object* v_step_2363_, lean_object* v_stream_2364_, lean_object* v_acc_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(v_00_u03b2_2362_, v_step_2363_, v_stream_2364_, v_acc_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_2368_, lean_object* v_acc_2369_, lean_object* v_step_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2370_, v_stream_2368_, v_acc_2369_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_2373_, lean_object* v_acc_2374_, lean_object* v_step_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_2373_, v_acc_2374_, v_step_2375_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_2378_, lean_object* v_stream_2379_, lean_object* v_acc_2380_, lean_object* v_step_2381_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2381_, v_stream_2379_, v_acc_2380_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_2384_, lean_object* v_stream_2385_, lean_object* v_acc_2386_, lean_object* v_step_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_2384_, v_stream_2385_, v_acc_2386_, v_step_2387_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(lean_object* v_x_2390_){
_start:
{
if (lean_obj_tag(v_x_2390_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2400_; 
v_a_2392_ = lean_ctor_get(v_x_2390_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_x_2390_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2394_ = v_x_2390_;
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v_x_2390_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
return v___x_2398_;
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2411_; 
v_a_2401_ = lean_ctor_get(v_x_2390_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_x_2390_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2403_ = v_x_2390_;
v_isShared_2404_ = v_isSharedCheck_2411_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v_x_2390_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2411_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_token_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v_token_2405_ = lean_ctor_get(v_a_2401_, 1);
lean_inc_ref(v_token_2405_);
lean_dec(v_a_2401_);
v___x_2406_ = l_Std_CancellationToken_selector(v_token_2405_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2406_);
v___x_2408_ = v___x_2403_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_x_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(v_x_2412_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___y_2415_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed(lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(v___y_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(lean_object* v_x_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1));
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed(lean_object* v_x_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(v_x_2425_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(lean_object* v_stream_2428_, lean_object* v___f_2429_, lean_object* v___f_2430_, lean_object* v___f_2431_, lean_object* v_x_2432_){
_start:
{
if (lean_obj_tag(v_x_2432_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2442_; 
lean_dec_ref(v___f_2431_);
lean_dec_ref(v___f_2430_);
lean_dec_ref(v___f_2429_);
lean_dec_ref(v_stream_2428_);
v_a_2434_ = lean_ctor_get(v_x_2432_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_x_2432_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2436_ = v_x_2432_;
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v_x_2432_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; 
v_a_2443_ = lean_ctor_get(v_x_2432_, 0);
lean_inc(v_a_2443_);
lean_dec_ref(v_x_2432_);
v___x_2444_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2428_);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
lean_ctor_set(v___x_2445_, 1, v___f_2429_);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v_a_2443_);
lean_ctor_set(v___x_2446_, 1, v___f_2430_);
v___x_2447_ = lean_unsigned_to_nat(2u);
v___x_2448_ = lean_mk_empty_array_with_capacity(v___x_2447_);
v___x_2449_ = lean_array_push(v___x_2448_, v___x_2445_);
v___x_2450_ = lean_array_push(v___x_2449_, v___x_2446_);
v___x_2451_ = l_Std_Async_Selectable_one___redArg(v___x_2450_);
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = 0;
v___x_2454_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2452_, v___x_2453_, v___x_2451_, v___f_2431_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed(lean_object* v_stream_2455_, lean_object* v___f_2456_, lean_object* v___f_2457_, lean_object* v___f_2458_, lean_object* v_x_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(v_stream_2455_, v___f_2456_, v___f_2457_, v___f_2458_, v_x_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(lean_object* v_step_2462_, lean_object* v_acc_2463_, lean_object* v_a_2464_, lean_object* v___f_2465_, lean_object* v_x_2466_){
_start:
{
if (lean_obj_tag(v_x_2466_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v___f_2465_);
lean_dec(v_acc_2463_);
lean_dec_ref(v_step_2462_);
v_a_2468_ = lean_ctor_get(v_x_2466_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_x_2466_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2470_ = v_x_2466_;
v_isShared_2471_ = v_isSharedCheck_2476_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v_x_2466_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2476_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
return v___x_2474_;
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2490_; 
v_a_2477_ = lean_ctor_get(v_x_2466_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_x_2466_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2479_ = v_x_2466_;
v_isShared_2480_ = v_isSharedCheck_2490_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v_x_2466_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2490_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
if (lean_obj_tag(v_a_2477_) == 1)
{
lean_object* v_val_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; 
lean_del_object(v___x_2479_);
v_val_2481_ = lean_ctor_get(v_a_2477_, 0);
lean_inc(v_val_2481_);
lean_dec_ref(v_a_2477_);
lean_inc_ref(v_a_2464_);
v___x_2482_ = lean_apply_4(v_step_2462_, v_val_2481_, v_acc_2463_, v_a_2464_, lean_box(0));
v___x_2483_ = lean_unsigned_to_nat(0u);
v___x_2484_ = 0;
v___x_2485_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2483_, v___x_2484_, v___x_2482_, v___f_2465_);
return v___x_2485_;
}
else
{
lean_object* v___x_2487_; 
lean_dec(v_a_2477_);
lean_dec_ref(v___f_2465_);
lean_dec_ref(v_step_2462_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v_acc_2463_);
v___x_2487_ = v___x_2479_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_acc_2463_);
v___x_2487_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
return v___x_2488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed(lean_object* v_step_2491_, lean_object* v_acc_2492_, lean_object* v_a_2493_, lean_object* v___f_2494_, lean_object* v_x_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(v_step_2491_, v_acc_2492_, v_a_2493_, v___f_2494_, v_x_2495_);
lean_dec_ref(v_a_2493_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed(lean_object* v_step_2501_, lean_object* v_stream_2502_, lean_object* v_a_2503_, lean_object* v_x_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(v_step_2501_, v_stream_2502_, v_a_2503_, v_x_2504_);
lean_dec_ref(v_a_2503_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(lean_object* v_step_2507_, lean_object* v_stream_2508_, lean_object* v_acc_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v___f_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; lean_object* v___f_2518_; lean_object* v___f_2519_; lean_object* v___f_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; lean_object* v___x_2523_; 
v___f_2512_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0));
lean_inc_ref_n(v_a_2510_, 3);
v___x_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2513_, 0, v_a_2510_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
v___x_2515_ = lean_unsigned_to_nat(0u);
v___x_2516_ = 0;
v___x_2517_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2515_, v___x_2516_, v___x_2514_, v___f_2512_);
v___f_2518_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1));
v___f_2519_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2));
lean_inc_ref(v_stream_2508_);
lean_inc_ref(v_step_2507_);
v___f_2520_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2520_, 0, v_step_2507_);
lean_closure_set(v___f_2520_, 1, v_stream_2508_);
lean_closure_set(v___f_2520_, 2, v_a_2510_);
v___f_2521_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_2521_, 0, v_step_2507_);
lean_closure_set(v___f_2521_, 1, v_acc_2509_);
lean_closure_set(v___f_2521_, 2, v_a_2510_);
lean_closure_set(v___f_2521_, 3, v___f_2520_);
v___f_2522_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_2522_, 0, v_stream_2508_);
lean_closure_set(v___f_2522_, 1, v___f_2518_);
lean_closure_set(v___f_2522_, 2, v___f_2519_);
lean_closure_set(v___f_2522_, 3, v___f_2521_);
v___x_2523_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2515_, v___x_2516_, v___x_2517_, v___f_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(lean_object* v_step_2524_, lean_object* v_stream_2525_, lean_object* v_a_2526_, lean_object* v_x_2527_){
_start:
{
if (lean_obj_tag(v_x_2527_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v_stream_2525_);
lean_dec_ref(v_step_2524_);
v_a_2529_ = lean_ctor_get(v_x_2527_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_x_2527_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2531_ = v_x_2527_;
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v_x_2527_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
return v___x_2535_;
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2555_; 
v_a_2538_ = lean_ctor_get(v_x_2527_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_x_2527_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2540_ = v_x_2527_;
v_isShared_2541_ = v_isSharedCheck_2555_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v_x_2527_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2555_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
if (lean_obj_tag(v_a_2538_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v_stream_2525_);
lean_dec_ref(v_step_2524_);
v_a_2542_ = lean_ctor_get(v_a_2538_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_a_2538_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2544_ = v_a_2538_;
v_isShared_2545_ = v_isSharedCheck_2552_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v_a_2538_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2552_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v_a_2542_);
v___x_2547_ = v___x_2540_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2549_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2547_);
v___x_2549_ = v___x_2544_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2554_; 
lean_del_object(v___x_2540_);
v_a_2553_ = lean_ctor_get(v_a_2538_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v_a_2538_);
v___x_2554_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2524_, v_stream_2525_, v_a_2553_, v_a_2526_);
return v___x_2554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___boxed(lean_object* v_step_2556_, lean_object* v_stream_2557_, lean_object* v_acc_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2556_, v_stream_2557_, v_acc_2558_, v_a_2559_);
lean_dec_ref(v_a_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(lean_object* v_00_u03b2_2562_, lean_object* v_step_2563_, lean_object* v_stream_2564_, lean_object* v_acc_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2563_, v_stream_2564_, v_acc_2565_, v_a_2566_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___boxed(lean_object* v_00_u03b2_2569_, lean_object* v_step_2570_, lean_object* v_stream_2571_, lean_object* v_acc_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(v_00_u03b2_2569_, v_step_2570_, v_stream_2571_, v_acc_2572_, v_a_2573_);
lean_dec_ref(v_a_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_2576_, lean_object* v_acc_2577_, lean_object* v_step_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2578_, v_stream_2576_, v_acc_2577_, v_a_2579_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_2582_, lean_object* v_acc_2583_, lean_object* v_step_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_2582_, v_acc_2583_, v_step_2584_, v_a_2585_);
lean_dec_ref(v_a_2585_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_2588_, lean_object* v_stream_2589_, lean_object* v_acc_2590_, lean_object* v_step_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2591_, v_stream_2589_, v_acc_2590_, v_a_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_2595_, lean_object* v_stream_2596_, lean_object* v_acc_2597_, lean_object* v_step_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_2595_, v_stream_2596_, v_acc_2597_, v_step_2598_, v_a_2599_);
lean_dec_ref(v_a_2599_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v_x_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1));
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v_x_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v_x_2607_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___y_2610_);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed(lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(v___y_2614_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(lean_object* v_x_2617_){
_start:
{
if (lean_obj_tag(v_x_2617_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2627_; 
v_a_2619_ = lean_ctor_get(v_x_2617_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_x_2617_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2621_ = v_x_2617_;
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v_x_2617_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
return v___x_2625_;
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2638_; 
v_a_2628_ = lean_ctor_get(v_x_2617_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_x_2617_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2630_ = v_x_2617_;
v_isShared_2631_ = v_isSharedCheck_2638_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v_x_2617_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2638_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v_token_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v_token_2632_ = lean_ctor_get(v_a_2628_, 1);
lean_inc_ref(v_token_2632_);
lean_dec(v_a_2628_);
v___x_2633_ = l_Std_CancellationToken_selector(v_token_2632_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2633_);
v___x_2635_ = v___x_2630_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed(lean_object* v_x_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(v_x_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v_stream_2642_, lean_object* v___f_2643_, lean_object* v___f_2644_, lean_object* v_x_2645_){
_start:
{
if (lean_obj_tag(v_x_2645_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2655_; 
lean_dec_ref(v___f_2644_);
lean_dec_ref(v___f_2643_);
lean_dec_ref(v_stream_2642_);
v_a_2647_ = lean_ctor_get(v_x_2645_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_x_2645_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2649_ = v_x_2645_;
v_isShared_2650_ = v_isSharedCheck_2655_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v_x_2645_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2655_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_a_2656_ = lean_ctor_get(v_x_2645_, 0);
lean_inc(v_a_2656_);
lean_dec_ref(v_x_2645_);
v___x_2657_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2642_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v___f_2643_);
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v_a_2656_);
lean_ctor_set(v___x_2659_, 1, v___f_2644_);
v___x_2660_ = lean_unsigned_to_nat(2u);
v___x_2661_ = lean_mk_empty_array_with_capacity(v___x_2660_);
v___x_2662_ = lean_array_push(v___x_2661_, v___x_2658_);
v___x_2663_ = lean_array_push(v___x_2662_, v___x_2659_);
v___x_2664_ = l_Std_Async_Selectable_one___redArg(v___x_2663_);
return v___x_2664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v_stream_2665_, lean_object* v___f_2666_, lean_object* v___f_2667_, lean_object* v_x_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_2665_, v___f_2666_, v___f_2667_, v_x_2668_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(lean_object* v___f_2671_, lean_object* v___f_2672_, lean_object* v___f_2673_, lean_object* v_stream_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; lean_object* v___x_2681_; lean_object* v___f_2682_; lean_object* v___x_2683_; 
lean_inc_ref(v___y_2675_);
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___y_2675_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
v___x_2679_ = lean_unsigned_to_nat(0u);
v___x_2680_ = 0;
v___x_2681_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2679_, v___x_2680_, v___x_2678_, v___f_2671_);
v___f_2682_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2682_, 0, v_stream_2674_);
lean_closure_set(v___f_2682_, 1, v___f_2672_);
lean_closure_set(v___f_2682_, 2, v___f_2673_);
v___x_2683_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2679_, v___x_2680_, v___x_2681_, v___f_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4___boxed(lean_object* v___f_2684_, lean_object* v___f_2685_, lean_object* v___f_2686_, lean_object* v_stream_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(v___f_2684_, v___f_2685_, v___f_2686_, v_stream_2687_, v___y_2688_);
lean_dec_ref(v___y_2688_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v_toPure_2701_, lean_object* v_result_2702_, lean_object* v_maximumSize_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_stream_2707_, lean_object* v_toBind_2708_, lean_object* v_____do__lift_2709_){
_start:
{
if (lean_obj_tag(v_____do__lift_2709_) == 0)
{
lean_object* v___x_2710_; 
lean_dec(v_toBind_2708_);
lean_dec_ref(v_stream_2707_);
lean_dec(v_inst_2706_);
lean_dec_ref(v_inst_2705_);
lean_dec_ref(v_inst_2704_);
lean_dec(v_maximumSize_2703_);
v___x_2710_ = lean_apply_2(v_toPure_2701_, lean_box(0), v_result_2702_);
return v___x_2710_;
}
else
{
lean_object* v_val_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_toPure_2701_);
v_val_2711_ = lean_ctor_get(v_____do__lift_2709_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_____do__lift_2709_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2713_ = v_____do__lift_2709_;
v_isShared_2714_ = v_isSharedCheck_2742_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_val_2711_);
lean_dec(v_____do__lift_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2742_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_data_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; lean_object* v_result_2720_; 
v_data_2715_ = lean_ctor_get(v_val_2711_, 0);
lean_inc_ref(v_data_2715_);
lean_dec(v_val_2711_);
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = lean_byte_array_size(v_result_2702_);
v___x_2718_ = lean_byte_array_size(v_data_2715_);
v___x_2719_ = 0;
v_result_2720_ = lean_byte_array_copy_slice(v_data_2715_, v___x_2716_, v_result_2702_, v___x_2717_, v___x_2718_, v___x_2719_);
lean_dec_ref(v_data_2715_);
if (lean_obj_tag(v_maximumSize_2703_) == 1)
{
lean_object* v_val_2721_; lean_object* v___x_2722_; uint64_t v___x_2723_; uint64_t v___x_2724_; uint8_t v___x_2725_; 
v_val_2721_ = lean_ctor_get(v_maximumSize_2703_, 0);
v___x_2722_ = lean_byte_array_size(v_result_2720_);
v___x_2723_ = lean_uint64_of_nat(v___x_2722_);
v___x_2724_ = lean_unbox_uint64(v_val_2721_);
v___x_2725_ = lean_uint64_dec_lt(v___x_2724_, v___x_2723_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; 
lean_del_object(v___x_2713_);
lean_dec(v_toBind_2708_);
v___x_2726_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2704_, v_inst_2705_, v_inst_2706_, v_stream_2707_, v_maximumSize_2703_, v_result_2720_);
return v___x_2726_;
}
else
{
lean_object* v_throw_2727_; lean_object* v___f_2728_; lean_object* v___x_2729_; uint64_t v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
lean_inc(v_val_2721_);
v_throw_2727_ = lean_ctor_get(v_inst_2705_, 0);
lean_inc(v_throw_2727_);
v___f_2728_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0), 7, 6);
lean_closure_set(v___f_2728_, 0, v_inst_2704_);
lean_closure_set(v___f_2728_, 1, v_inst_2705_);
lean_closure_set(v___f_2728_, 2, v_inst_2706_);
lean_closure_set(v___f_2728_, 3, v_stream_2707_);
lean_closure_set(v___f_2728_, 4, v_maximumSize_2703_);
lean_closure_set(v___f_2728_, 5, v_result_2720_);
v___x_2729_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0));
v___x_2730_ = lean_unbox_uint64(v_val_2721_);
lean_dec(v_val_2721_);
v___x_2731_ = lean_uint64_to_nat(v___x_2730_);
v___x_2732_ = l_Nat_reprFast(v___x_2731_);
v___x_2733_ = lean_string_append(v___x_2729_, v___x_2732_);
lean_dec_ref(v___x_2732_);
v___x_2734_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1));
v___x_2735_ = lean_string_append(v___x_2733_, v___x_2734_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set_tag(v___x_2713_, 18);
lean_ctor_set(v___x_2713_, 0, v___x_2735_);
v___x_2737_ = v___x_2713_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = lean_apply_2(v_throw_2727_, lean_box(0), v___x_2737_);
v___x_2739_ = lean_apply_4(v_toBind_2708_, lean_box(0), lean_box(0), v___x_2738_, v___f_2728_);
return v___x_2739_;
}
}
}
else
{
lean_object* v___x_2741_; 
lean_del_object(v___x_2713_);
lean_dec(v_toBind_2708_);
v___x_2741_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2704_, v_inst_2705_, v_inst_2706_, v_stream_2707_, v_maximumSize_2703_, v_result_2720_);
return v___x_2741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_inst_2745_, lean_object* v_stream_2746_, lean_object* v_maximumSize_2747_, lean_object* v_result_2748_){
_start:
{
lean_object* v_toApplicative_2749_; lean_object* v_toBind_2750_; lean_object* v_toPure_2751_; lean_object* v___x_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; 
v_toApplicative_2749_ = lean_ctor_get(v_inst_2743_, 0);
v_toBind_2750_ = lean_ctor_get(v_inst_2743_, 1);
lean_inc_n(v_toBind_2750_, 2);
v_toPure_2751_ = lean_ctor_get(v_toApplicative_2749_, 1);
lean_inc(v_toPure_2751_);
lean_inc(v_inst_2745_);
lean_inc_ref(v_stream_2746_);
v___x_2752_ = lean_apply_1(v_inst_2745_, v_stream_2746_);
v___f_2753_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 9, 8);
lean_closure_set(v___f_2753_, 0, v_toPure_2751_);
lean_closure_set(v___f_2753_, 1, v_result_2748_);
lean_closure_set(v___f_2753_, 2, v_maximumSize_2747_);
lean_closure_set(v___f_2753_, 3, v_inst_2743_);
lean_closure_set(v___f_2753_, 4, v_inst_2744_);
lean_closure_set(v___f_2753_, 5, v_inst_2745_);
lean_closure_set(v___f_2753_, 6, v_stream_2746_);
lean_closure_set(v___f_2753_, 7, v_toBind_2750_);
v___x_2754_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v___x_2752_, v___f_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_inst_2755_, lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_stream_2758_, lean_object* v_maximumSize_2759_, lean_object* v_result_2760_, lean_object* v_____r_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2755_, v_inst_2756_, v_inst_2757_, v_stream_2758_, v_maximumSize_2759_, v_result_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_2763_, lean_object* v_inst_2764_, lean_object* v_inst_2765_, lean_object* v_inst_2766_, lean_object* v_stream_2767_, lean_object* v_maximumSize_2768_, lean_object* v_result_2769_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2764_, v_inst_2765_, v_inst_2766_, v_stream_2767_, v_maximumSize_2768_, v_result_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_2771_, lean_object* v_inst_2772_, lean_object* v_toPure_2773_, lean_object* v_result_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_apply_1(v_inst_2771_, v_result_2774_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v_toPure_2773_);
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2785_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2785_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v_throw_2780_; lean_object* v___x_2782_; 
v_throw_2780_ = lean_ctor_get(v_inst_2772_, 0);
lean_inc(v_throw_2780_);
lean_dec_ref(v_inst_2772_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set_tag(v___x_2778_, 18);
v___x_2782_ = v___x_2778_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2776_);
v___x_2782_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_apply_2(v_throw_2780_, lean_box(0), v___x_2782_);
return v___x_2783_;
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2787_; 
lean_dec_ref(v_inst_2772_);
v_a_2786_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2775_);
v___x_2787_ = lean_apply_2(v_toPure_2773_, lean_box(0), v_a_2786_);
return v___x_2787_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_2788_, lean_object* v_inst_2789_, lean_object* v_inst_2790_, lean_object* v_inst_2791_, lean_object* v_stream_2792_, lean_object* v_maximumSize_2793_){
_start:
{
lean_object* v_toApplicative_2794_; lean_object* v_toBind_2795_; lean_object* v_toPure_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___f_2799_; lean_object* v___x_2800_; 
v_toApplicative_2794_ = lean_ctor_get(v_inst_2789_, 0);
v_toBind_2795_ = lean_ctor_get(v_inst_2789_, 1);
lean_inc(v_toBind_2795_);
v_toPure_2796_ = lean_ctor_get(v_toApplicative_2794_, 1);
lean_inc(v_toPure_2796_);
v___x_2797_ = l_ByteArray_empty;
lean_inc_ref(v_inst_2790_);
v___x_2798_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2789_, v_inst_2790_, v_inst_2791_, v_stream_2792_, v_maximumSize_2793_, v___x_2797_);
v___f_2799_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2799_, 0, v_inst_2788_);
lean_closure_set(v___f_2799_, 1, v_inst_2790_);
lean_closure_set(v___f_2799_, 2, v_toPure_2796_);
v___x_2800_ = lean_apply_4(v_toBind_2795_, lean_box(0), lean_box(0), v___x_2798_, v___f_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_2801_, lean_object* v_m_2802_, lean_object* v_inst_2803_, lean_object* v_inst_2804_, lean_object* v_inst_2805_, lean_object* v_inst_2806_, lean_object* v_stream_2807_, lean_object* v_maximumSize_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_2803_, v_inst_2804_, v_inst_2805_, v_inst_2806_, v_stream_2807_, v_maximumSize_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t v_incomplete_2815_, lean_object* v_chunk_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v_pendingProducer_2821_; lean_object* v_pendingConsumer_2822_; lean_object* v_interestWaiter_2823_; uint8_t v_closed_2824_; lean_object* v_knownSize_2825_; lean_object* v_pendingIncompleteChunk_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2867_; 
v___x_2819_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_2817_);
v___x_2820_ = lean_st_ref_get(v___y_2817_);
v_pendingProducer_2821_ = lean_ctor_get(v___x_2820_, 0);
v_pendingConsumer_2822_ = lean_ctor_get(v___x_2820_, 1);
v_interestWaiter_2823_ = lean_ctor_get(v___x_2820_, 2);
v_closed_2824_ = lean_ctor_get_uint8(v___x_2820_, sizeof(void*)*5);
v_knownSize_2825_ = lean_ctor_get(v___x_2820_, 3);
v_pendingIncompleteChunk_2826_ = lean_ctor_get(v___x_2820_, 4);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2828_ = v___x_2820_;
v_isShared_2829_ = v_isSharedCheck_2867_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_pendingIncompleteChunk_2826_);
lean_inc(v_knownSize_2825_);
lean_inc(v_interestWaiter_2823_);
lean_inc(v_pendingConsumer_2822_);
lean_inc(v_pendingProducer_2821_);
lean_dec(v___x_2820_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2867_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___y_2831_; 
if (v_closed_2824_ == 0)
{
if (lean_obj_tag(v_pendingIncompleteChunk_2826_) == 0)
{
v___y_2831_ = v_chunk_2816_;
goto v___jp_2830_;
}
else
{
lean_object* v_val_2845_; lean_object* v_data_2846_; lean_object* v_extensions_2847_; lean_object* v_data_2848_; lean_object* v_extensions_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2865_; 
v_val_2845_ = lean_ctor_get(v_pendingIncompleteChunk_2826_, 0);
lean_inc(v_val_2845_);
lean_dec_ref(v_pendingIncompleteChunk_2826_);
v_data_2846_ = lean_ctor_get(v_val_2845_, 0);
lean_inc_ref(v_data_2846_);
v_extensions_2847_ = lean_ctor_get(v_val_2845_, 1);
lean_inc_ref(v_extensions_2847_);
lean_dec(v_val_2845_);
v_data_2848_ = lean_ctor_get(v_chunk_2816_, 0);
v_extensions_2849_ = lean_ctor_get(v_chunk_2816_, 1);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_chunk_2816_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2851_ = v_chunk_2816_;
v_isShared_2852_ = v_isSharedCheck_2865_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_extensions_2849_);
lean_inc(v_data_2848_);
lean_dec(v_chunk_2816_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2865_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2853_ = lean_unsigned_to_nat(0u);
v___x_2854_ = lean_byte_array_size(v_data_2846_);
v___x_2855_ = lean_byte_array_size(v_data_2848_);
v___x_2856_ = lean_byte_array_copy_slice(v_data_2848_, v___x_2853_, v_data_2846_, v___x_2854_, v___x_2855_, v_closed_2824_);
lean_dec_ref(v_data_2848_);
v___x_2857_ = lean_array_get_size(v_extensions_2847_);
v___x_2858_ = lean_nat_dec_eq(v___x_2857_, v___x_2853_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v_extensions_2849_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_extensions_2847_);
lean_ctor_set(v___x_2851_, 0, v___x_2856_);
v___x_2860_ = v___x_2851_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_extensions_2847_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
v___y_2831_ = v___x_2860_;
goto v___jp_2830_;
}
}
else
{
lean_object* v___x_2863_; 
lean_dec_ref(v_extensions_2847_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2856_);
v___x_2863_ = v___x_2851_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_extensions_2849_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
v___y_2831_ = v___x_2863_;
goto v___jp_2830_;
}
}
}
}
}
else
{
lean_object* v___x_2866_; 
lean_del_object(v___x_2828_);
lean_dec(v_pendingIncompleteChunk_2826_);
lean_dec(v_knownSize_2825_);
lean_dec(v_interestWaiter_2823_);
lean_dec(v_pendingConsumer_2822_);
lean_dec(v_pendingProducer_2821_);
lean_dec_ref(v_chunk_2816_);
v___x_2866_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_2866_;
}
v___jp_2830_:
{
if (v_incomplete_2815_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2832_ = lean_box(0);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 4, v___x_2832_);
v___x_2834_ = v___x_2828_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_pendingProducer_2821_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_pendingConsumer_2822_);
lean_ctor_set(v_reuseFailAlloc_2838_, 2, v_interestWaiter_2823_);
lean_ctor_set(v_reuseFailAlloc_2838_, 3, v_knownSize_2825_);
lean_ctor_set(v_reuseFailAlloc_2838_, 4, v___x_2832_);
lean_ctor_set_uint8(v_reuseFailAlloc_2838_, sizeof(void*)*5, v_closed_2824_);
v___x_2834_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = lean_st_ref_set(v___y_2817_, v___x_2834_);
v___x_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___y_2831_);
v___x_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___y_2831_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 4, v___x_2839_);
v___x_2841_ = v___x_2828_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_pendingProducer_2821_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_pendingConsumer_2822_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v_interestWaiter_2823_);
lean_ctor_set(v_reuseFailAlloc_2844_, 3, v_knownSize_2825_);
lean_ctor_set(v_reuseFailAlloc_2844_, 4, v___x_2839_);
lean_ctor_set_uint8(v_reuseFailAlloc_2844_, sizeof(void*)*5, v_closed_2824_);
v___x_2841_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_st_ref_set(v___y_2817_, v___x_2841_);
v___x_2843_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0));
return v___x_2843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_incomplete_2868_, lean_object* v_chunk_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
uint8_t v_incomplete_boxed_2872_; lean_object* v_res_2873_; 
v_incomplete_boxed_2872_ = lean_unbox(v_incomplete_2868_);
v_res_2873_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_incomplete_boxed_2872_, v_chunk_2869_, v___y_2870_);
lean_dec(v___y_2870_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_2874_, lean_object* v_chunk_2875_, uint8_t v_incomplete_2876_){
_start:
{
lean_object* v___x_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_box(v_incomplete_2876_);
v___f_2879_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2879_, 0, v___x_2878_);
lean_closure_set(v___f_2879_, 1, v_chunk_2875_);
v___x_2880_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_2874_, v___f_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_2881_, lean_object* v_chunk_2882_, lean_object* v_incomplete_2883_, lean_object* v_a_2884_){
_start:
{
uint8_t v_incomplete_boxed_2885_; lean_object* v_res_2886_; 
v_incomplete_boxed_2885_ = lean_unbox(v_incomplete_2883_);
v_res_2886_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_2881_, v_chunk_2882_, v_incomplete_boxed_2885_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_2893_){
_start:
{
if (lean_obj_tag(v_x_2893_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2903_; 
v_a_2895_ = lean_ctor_get(v_x_2893_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_x_2893_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2897_ = v_x_2893_;
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v_x_2893_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
return v___x_2901_;
}
}
}
else
{
lean_object* v___x_2904_; 
lean_dec_ref(v_x_2893_);
v___x_2904_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_2904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_2905_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_2918_, lean_object* v_x_2919_){
_start:
{
if (lean_obj_tag(v_x_2919_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v___f_2918_);
v_a_2923_ = lean_ctor_get(v_x_2919_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_x_2919_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2925_ = v_x_2919_;
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v_x_2919_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
}
}
else
{
lean_object* v_a_2932_; 
v_a_2932_ = lean_ctor_get(v_x_2919_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v_x_2919_);
if (lean_obj_tag(v_a_2932_) == 1)
{
lean_object* v_val_2933_; uint8_t v___x_2934_; 
v_val_2933_ = lean_ctor_get(v_a_2932_, 0);
lean_inc(v_val_2933_);
lean_dec_ref(v_a_2932_);
v___x_2934_ = lean_unbox(v_val_2933_);
lean_dec(v_val_2933_);
if (v___x_2934_ == 1)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_box(0);
v___x_2936_ = lean_apply_2(v___f_2918_, v___x_2935_, lean_box(0));
return v___x_2936_;
}
else
{
lean_dec_ref(v___f_2918_);
goto v___jp_2921_;
}
}
else
{
lean_dec(v_a_2932_);
lean_dec_ref(v___f_2918_);
goto v___jp_2921_;
}
}
v___jp_2921_:
{
lean_object* v___x_2922_; 
v___x_2922_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_2937_, lean_object* v_x_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_2937_, v_x_2938_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_a_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_2943_, lean_object* v_x_2944_){
_start:
{
if (lean_obj_tag(v_x_2944_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2954_; 
v_a_2946_ = lean_ctor_get(v_x_2944_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_x_2944_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2948_ = v_x_2944_;
v_isShared_2949_ = v_isSharedCheck_2954_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v_x_2944_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2954_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
}
}
else
{
lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2965_; 
v_isSharedCheck_2965_ = !lean_is_exclusive(v_x_2944_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; 
v_unused_2966_ = lean_ctor_get(v_x_2944_, 0);
lean_dec(v_unused_2966_);
v___x_2956_ = v_x_2944_;
v_isShared_2957_ = v_isSharedCheck_2965_;
goto v_resetjp_2955_;
}
else
{
lean_dec(v_x_2944_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2965_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2958_ = lean_box(v___x_2943_);
v___x_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___x_2959_);
v___x_2961_ = v___x_2956_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_2967_, lean_object* v_x_2968_, lean_object* v___y_2969_){
_start:
{
uint8_t v___x_5677__boxed_2970_; lean_object* v_res_2971_; 
v___x_5677__boxed_2970_ = lean_unbox(v___x_2967_);
v_res_2971_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5677__boxed_2970_, v_x_2968_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_2972_, lean_object* v_x_2973_){
_start:
{
if (lean_obj_tag(v_x_2973_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2983_; 
v_a_2975_ = lean_ctor_get(v_x_2973_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_x_2973_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2977_ = v_x_2973_;
v_isShared_2978_ = v_isSharedCheck_2983_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v_x_2973_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2983_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
}
}
else
{
lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2994_; 
v_isSharedCheck_2994_ = !lean_is_exclusive(v_x_2973_);
if (v_isSharedCheck_2994_ == 0)
{
lean_object* v_unused_2995_; 
v_unused_2995_ = lean_ctor_get(v_x_2973_, 0);
lean_dec(v_unused_2995_);
v___x_2985_ = v_x_2973_;
v_isShared_2986_ = v_isSharedCheck_2994_;
goto v_resetjp_2984_;
}
else
{
lean_dec(v_x_2973_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2994_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2987_ = lean_box(v_a_2972_);
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2988_);
v___x_2990_ = v___x_2985_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_2996_, lean_object* v_x_2997_, lean_object* v___y_2998_){
_start:
{
uint8_t v_a_5729__boxed_2999_; lean_object* v_res_3000_; 
v_a_5729__boxed_2999_ = lean_unbox(v_a_2996_);
v_res_3000_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5729__boxed_2999_, v_x_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_3001_, lean_object* v_interestWaiter_3002_, uint8_t v_closed_3003_, lean_object* v_knownSize_3004_, lean_object* v_pendingIncompleteChunk_3005_, lean_object* v___y_3006_, lean_object* v_chunk_3007_, lean_object* v___f_3008_, lean_object* v_x_3009_){
_start:
{
if (lean_obj_tag(v_x_3009_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3019_; 
lean_dec_ref(v___f_3008_);
lean_dec(v_pendingIncompleteChunk_3005_);
lean_dec(v_knownSize_3004_);
lean_dec(v_interestWaiter_3002_);
lean_dec(v_pendingProducer_3001_);
v_a_3011_ = lean_ctor_get(v_x_3009_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_x_3009_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3013_ = v_x_3009_;
v_isShared_3014_ = v_isSharedCheck_3019_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v_x_3009_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3019_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
return v___x_3017_;
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3046_; 
v_a_3020_ = lean_ctor_get(v_x_3009_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_x_3009_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3022_ = v_x_3009_;
v_isShared_3023_ = v_isSharedCheck_3046_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v_x_3009_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3046_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_unbox(v_a_3020_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___f_3028_; lean_object* v___x_3030_; 
lean_dec_ref(v___f_3008_);
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3026_, 0, v_pendingProducer_3001_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
lean_ctor_set(v___x_3026_, 2, v_interestWaiter_3002_);
lean_ctor_set(v___x_3026_, 3, v_knownSize_3004_);
lean_ctor_set(v___x_3026_, 4, v_pendingIncompleteChunk_3005_);
lean_ctor_set_uint8(v___x_3026_, sizeof(void*)*5, v_closed_3003_);
v___x_3027_ = lean_st_ref_set(v___y_3006_, v___x_3026_);
lean_inc(v_a_3020_);
v___f_3028_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3028_, 0, v_a_3020_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3027_);
v___x_3030_ = v___x_3022_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3027_);
v___x_3030_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; 
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = lean_unbox(v_a_3020_);
lean_dec(v_a_3020_);
v___x_3034_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3032_, v___x_3033_, v___x_3031_, v___f_3028_);
return v___x_3034_;
}
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
lean_dec(v_a_3020_);
v___x_3036_ = lean_box(0);
v___x_3037_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_3004_, v_chunk_3007_);
v___x_3038_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3038_, 0, v_pendingProducer_3001_);
lean_ctor_set(v___x_3038_, 1, v___x_3036_);
lean_ctor_set(v___x_3038_, 2, v_interestWaiter_3002_);
lean_ctor_set(v___x_3038_, 3, v___x_3037_);
lean_ctor_set(v___x_3038_, 4, v_pendingIncompleteChunk_3005_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*5, v_closed_3003_);
v___x_3039_ = lean_st_ref_set(v___y_3006_, v___x_3038_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3039_);
v___x_3041_ = v___x_3022_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3043_, v_closed_3003_, v___x_3042_, v___f_3008_);
return v___x_3044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_3047_, lean_object* v_interestWaiter_3048_, lean_object* v_closed_3049_, lean_object* v_knownSize_3050_, lean_object* v_pendingIncompleteChunk_3051_, lean_object* v___y_3052_, lean_object* v_chunk_3053_, lean_object* v___f_3054_, lean_object* v_x_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v_closed_boxed_3057_; lean_object* v_res_3058_; 
v_closed_boxed_3057_ = lean_unbox(v_closed_3049_);
v_res_3058_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_3047_, v_interestWaiter_3048_, v_closed_boxed_3057_, v_knownSize_3050_, v_pendingIncompleteChunk_3051_, v___y_3052_, v_chunk_3053_, v___f_3054_, v_x_3055_);
lean_dec_ref(v_chunk_3053_);
lean_dec(v___y_3052_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v_chunk_3077_, lean_object* v___y_3078_, lean_object* v_a_3079_, lean_object* v___f_3080_, lean_object* v_x_3081_){
_start:
{
if (lean_obj_tag(v_x_3081_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v___f_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_chunk_3077_);
v_a_3083_ = lean_ctor_get(v_x_3081_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_x_3081_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3085_ = v_x_3081_;
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v_x_3081_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
return v___x_3089_;
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3145_; 
v_a_3092_ = lean_ctor_get(v_x_3081_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_x_3081_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3094_ = v_x_3081_;
v_isShared_3095_ = v_isSharedCheck_3145_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v_x_3081_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3145_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
uint8_t v_closed_3096_; 
v_closed_3096_ = lean_ctor_get_uint8(v_a_3092_, sizeof(void*)*5);
if (v_closed_3096_ == 0)
{
lean_object* v_pendingConsumer_3097_; 
v_pendingConsumer_3097_ = lean_ctor_get(v_a_3092_, 1);
lean_inc(v_pendingConsumer_3097_);
if (lean_obj_tag(v_pendingConsumer_3097_) == 1)
{
lean_object* v_pendingProducer_3098_; lean_object* v_interestWaiter_3099_; lean_object* v_knownSize_3100_; lean_object* v_pendingIncompleteChunk_3101_; lean_object* v_val_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v___f_3080_);
lean_dec(v_a_3079_);
v_pendingProducer_3098_ = lean_ctor_get(v_a_3092_, 0);
lean_inc(v_pendingProducer_3098_);
v_interestWaiter_3099_ = lean_ctor_get(v_a_3092_, 2);
lean_inc(v_interestWaiter_3099_);
v_knownSize_3100_ = lean_ctor_get(v_a_3092_, 3);
lean_inc(v_knownSize_3100_);
v_pendingIncompleteChunk_3101_ = lean_ctor_get(v_a_3092_, 4);
lean_inc(v_pendingIncompleteChunk_3101_);
lean_dec(v_a_3092_);
v_val_3102_ = lean_ctor_get(v_pendingConsumer_3097_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_pendingConsumer_3097_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3104_ = v_pendingConsumer_3097_;
v_isShared_3105_ = v_isSharedCheck_3120_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_val_3102_);
lean_dec(v_pendingConsumer_3097_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3120_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
lean_inc_ref(v_chunk_3077_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v_chunk_3077_);
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_chunk_3077_);
v___x_3107_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
uint8_t v___x_3108_; lean_object* v___f_3109_; lean_object* v___x_3110_; lean_object* v___f_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3108_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_3102_, v___x_3107_);
lean_dec(v_val_3102_);
v___f_3109_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_3110_ = lean_box(v_closed_3096_);
lean_inc(v___y_3078_);
v___f_3111_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 10, 8);
lean_closure_set(v___f_3111_, 0, v_pendingProducer_3098_);
lean_closure_set(v___f_3111_, 1, v_interestWaiter_3099_);
lean_closure_set(v___f_3111_, 2, v___x_3110_);
lean_closure_set(v___f_3111_, 3, v_knownSize_3100_);
lean_closure_set(v___f_3111_, 4, v_pendingIncompleteChunk_3101_);
lean_closure_set(v___f_3111_, 5, v___y_3078_);
lean_closure_set(v___f_3111_, 6, v_chunk_3077_);
lean_closure_set(v___f_3111_, 7, v___f_3109_);
v___x_3112_ = lean_box(v___x_3108_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3112_);
v___x_3114_ = v___x_3094_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3116_, v_closed_3096_, v___x_3115_, v___f_3111_);
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_pendingProducer_3121_; 
v_pendingProducer_3121_ = lean_ctor_get(v_a_3092_, 0);
if (lean_obj_tag(v_pendingProducer_3121_) == 0)
{
lean_object* v_interestWaiter_3122_; lean_object* v_knownSize_3123_; lean_object* v_pendingIncompleteChunk_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3140_; 
v_interestWaiter_3122_ = lean_ctor_get(v_a_3092_, 2);
v_knownSize_3123_ = lean_ctor_get(v_a_3092_, 3);
v_pendingIncompleteChunk_3124_ = lean_ctor_get(v_a_3092_, 4);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_a_3092_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; lean_object* v_unused_3142_; 
v_unused_3141_ = lean_ctor_get(v_a_3092_, 1);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v_a_3092_, 0);
lean_dec(v_unused_3142_);
v___x_3126_ = v_a_3092_;
v_isShared_3127_ = v_isSharedCheck_3140_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_pendingIncompleteChunk_3124_);
lean_inc(v_knownSize_3123_);
lean_inc(v_interestWaiter_3122_);
lean_dec(v_a_3092_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3140_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v_chunk_3077_);
lean_ctor_set(v___x_3128_, 1, v_a_3079_);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3129_);
v___x_3131_ = v___x_3126_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_pendingConsumer_3097_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_interestWaiter_3122_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v_knownSize_3123_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v_pendingIncompleteChunk_3124_);
lean_ctor_set_uint8(v_reuseFailAlloc_3139_, sizeof(void*)*5, v_closed_3096_);
v___x_3131_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3132_ = lean_st_ref_set(v___y_3078_, v___x_3131_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3132_);
v___x_3134_ = v___x_3094_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
v___x_3136_ = lean_unsigned_to_nat(0u);
v___x_3137_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3136_, v_closed_3096_, v___x_3135_, v___f_3080_);
return v___x_3137_;
}
}
}
}
else
{
lean_object* v___x_3143_; 
lean_dec(v_pendingConsumer_3097_);
lean_del_object(v___x_3094_);
lean_dec(v_a_3092_);
lean_dec_ref(v___f_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_chunk_3077_);
v___x_3143_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_3143_;
}
}
}
else
{
lean_object* v___x_3144_; 
lean_del_object(v___x_3094_);
lean_dec(v_a_3092_);
lean_dec_ref(v___f_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_chunk_3077_);
v___x_3144_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_3144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v_chunk_3146_, lean_object* v___y_3147_, lean_object* v_a_3148_, lean_object* v___f_3149_, lean_object* v_x_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v_chunk_3146_, v___y_3147_, v_a_3148_, v___f_3149_, v_x_3150_);
lean_dec(v___y_3147_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_3153_, lean_object* v___f_3154_, lean_object* v_x_3155_){
_start:
{
if (lean_obj_tag(v_x_3155_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3165_; 
lean_dec_ref(v___f_3154_);
v_a_3157_ = lean_ctor_get(v_x_3155_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_x_3155_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3159_ = v_x_3155_;
v_isShared_3160_ = v_isSharedCheck_3165_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v_x_3155_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3165_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3163_; 
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
}
else
{
lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3177_; 
v_isSharedCheck_3177_ = !lean_is_exclusive(v_x_3155_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v_x_3155_, 0);
lean_dec(v_unused_3178_);
v___x_3167_ = v_x_3155_;
v_isShared_3168_ = v_isSharedCheck_3177_;
goto v_resetjp_3166_;
}
else
{
lean_dec(v_x_3155_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3177_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_st_ref_get(v___y_3153_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v___x_3169_);
v___x_3171_ = v___x_3167_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; lean_object* v___x_3175_; 
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
v___x_3173_ = lean_unsigned_to_nat(0u);
v___x_3174_ = 0;
v___x_3175_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3173_, v___x_3174_, v___x_3172_, v___f_3154_);
return v___x_3175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_3179_, lean_object* v___f_3180_, lean_object* v_x_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_3179_, v___f_3180_, v_x_3181_);
lean_dec(v___y_3179_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_3184_, lean_object* v_a_3185_, lean_object* v___f_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; lean_object* v___x_3194_; 
v___x_3189_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3187_);
lean_inc_n(v___y_3187_, 2);
v___f_3190_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_3190_, 0, v_chunk_3184_);
lean_closure_set(v___f_3190_, 1, v___y_3187_);
lean_closure_set(v___f_3190_, 2, v_a_3185_);
lean_closure_set(v___f_3190_, 3, v___f_3186_);
v___f_3191_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_3191_, 0, v___y_3187_);
lean_closure_set(v___f_3191_, 1, v___f_3190_);
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = 0;
v___x_3194_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3192_, v___x_3193_, v___x_3189_, v___f_3191_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_3195_, lean_object* v_a_3196_, lean_object* v___f_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_3195_, v_a_3196_, v___f_3197_, v___y_3198_);
lean_dec(v___y_3198_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_3206_, lean_object* v___f_3207_, lean_object* v___f_3208_, lean_object* v_stream_3209_, lean_object* v_chunk_3210_, lean_object* v___f_3211_, lean_object* v_x_3212_){
_start:
{
if (lean_obj_tag(v_x_3212_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v___f_3211_);
lean_dec_ref(v_chunk_3210_);
lean_dec_ref(v_stream_3209_);
lean_dec_ref(v___f_3208_);
lean_dec_ref(v___f_3207_);
v_a_3214_ = lean_ctor_get(v_x_3212_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_x_3212_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3216_ = v_x_3212_;
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v_x_3212_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
return v___x_3220_;
}
}
}
else
{
lean_object* v_a_3223_; 
v_a_3223_ = lean_ctor_get(v_x_3212_, 0);
lean_inc(v_a_3223_);
lean_dec_ref(v_x_3212_);
if (lean_obj_tag(v_a_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3232_; 
lean_dec_ref(v___f_3211_);
lean_dec_ref(v_chunk_3210_);
lean_dec_ref(v_stream_3209_);
lean_dec_ref(v___f_3208_);
lean_dec_ref(v___f_3207_);
v_a_3224_ = lean_ctor_get(v_a_3223_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_a_3223_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3226_ = v_a_3223_;
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v_a_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
return v___x_3230_;
}
}
}
else
{
lean_object* v_a_3233_; 
v_a_3233_ = lean_ctor_get(v_a_3223_, 0);
lean_inc(v_a_3233_);
lean_dec_ref(v_a_3223_);
if (lean_obj_tag(v_a_3233_) == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
lean_dec_ref(v___f_3211_);
lean_dec_ref(v_chunk_3210_);
lean_dec_ref(v_stream_3209_);
v___x_3234_ = lean_io_promise_result_opt(v_a_3206_);
v___x_3235_ = lean_unsigned_to_nat(0u);
v___x_3236_ = 0;
v___x_3237_ = lean_task_map(v___f_3207_, v___x_3234_, v___x_3235_, v___x_3236_);
v___x_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
v___x_3239_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3235_, v___x_3236_, v___x_3238_, v___f_3208_);
return v___x_3239_;
}
else
{
lean_object* v_val_3240_; uint8_t v___x_3241_; 
lean_dec_ref(v___f_3208_);
lean_dec_ref(v___f_3207_);
v_val_3240_ = lean_ctor_get(v_a_3233_, 0);
lean_inc(v_val_3240_);
lean_dec_ref(v_a_3233_);
v___x_3241_ = lean_unbox(v_val_3240_);
lean_dec(v_val_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; 
lean_dec_ref(v___f_3211_);
v___x_3242_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3209_, v_chunk_3210_);
return v___x_3242_;
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_dec_ref(v_chunk_3210_);
lean_dec_ref(v_stream_3209_);
v___x_3243_ = lean_box(0);
v___x_3244_ = lean_apply_2(v___f_3211_, v___x_3243_, lean_box(0));
return v___x_3244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_3245_, lean_object* v___f_3246_, lean_object* v___f_3247_, lean_object* v_stream_3248_, lean_object* v_chunk_3249_, lean_object* v___f_3250_, lean_object* v_x_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_3245_, v___f_3246_, v___f_3247_, v_stream_3248_, v_chunk_3249_, v___f_3250_, v_x_3251_);
lean_dec(v_a_3245_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_3254_, lean_object* v___f_3255_, lean_object* v_stream_3256_, lean_object* v___f_3257_, lean_object* v___f_3258_, lean_object* v___f_3259_, lean_object* v_x_3260_){
_start:
{
if (lean_obj_tag(v_x_3260_) == 0)
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v___f_3259_);
lean_dec_ref(v___f_3258_);
lean_dec_ref(v___f_3257_);
lean_dec_ref(v_stream_3256_);
lean_dec_ref(v___f_3255_);
lean_dec_ref(v_chunk_3254_);
v_a_3262_ = lean_ctor_get(v_x_3260_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_x_3260_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3264_ = v_x_3260_;
v_isShared_3265_ = v_isSharedCheck_3270_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v_x_3260_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3270_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
return v___x_3268_;
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___f_3272_; lean_object* v___x_3273_; lean_object* v___f_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; 
v_a_3271_ = lean_ctor_get(v_x_3260_, 0);
lean_inc_n(v_a_3271_, 2);
lean_dec_ref(v_x_3260_);
lean_inc_ref(v_chunk_3254_);
v___f_3272_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_3272_, 0, v_chunk_3254_);
lean_closure_set(v___f_3272_, 1, v_a_3271_);
lean_closure_set(v___f_3272_, 2, v___f_3255_);
lean_inc_ref(v_stream_3256_);
v___x_3273_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3256_, v___f_3272_);
v___f_3274_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3274_, 0, v_a_3271_);
lean_closure_set(v___f_3274_, 1, v___f_3257_);
lean_closure_set(v___f_3274_, 2, v___f_3258_);
lean_closure_set(v___f_3274_, 3, v_stream_3256_);
lean_closure_set(v___f_3274_, 4, v_chunk_3254_);
lean_closure_set(v___f_3274_, 5, v___f_3259_);
v___x_3275_ = lean_unsigned_to_nat(0u);
v___x_3276_ = 0;
v___x_3277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3275_, v___x_3276_, v___x_3273_, v___f_3274_);
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_3278_, lean_object* v___f_3279_, lean_object* v_stream_3280_, lean_object* v___f_3281_, lean_object* v___f_3282_, lean_object* v___f_3283_, lean_object* v_x_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_3278_, v___f_3279_, v_stream_3280_, v___f_3281_, v___f_3282_, v___f_3283_, v_x_3284_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_3287_, lean_object* v_chunk_3288_){
_start:
{
lean_object* v___x_3290_; lean_object* v___f_3291_; lean_object* v___f_3292_; lean_object* v___f_3293_; lean_object* v___f_3294_; lean_object* v___f_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; 
v___x_3290_ = lean_io_promise_new();
v___f_3291_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_3292_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_3293_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_3294_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_3295_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_3295_, 0, v_chunk_3288_);
lean_closure_set(v___f_3295_, 1, v___f_3291_);
lean_closure_set(v___f_3295_, 2, v_stream_3287_);
lean_closure_set(v___f_3295_, 3, v___f_3294_);
lean_closure_set(v___f_3295_, 4, v___f_3293_);
lean_closure_set(v___f_3295_, 5, v___f_3292_);
v___x_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3290_);
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
v___x_3298_ = lean_unsigned_to_nat(0u);
v___x_3299_ = 0;
v___x_3300_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3298_, v___x_3299_, v___x_3297_, v___f_3295_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_3301_, lean_object* v_chunk_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3301_, v_chunk_3302_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_3305_, lean_object* v_x_3306_){
_start:
{
if (lean_obj_tag(v_x_3306_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v_stream_3305_);
v_a_3308_ = lean_ctor_get(v_x_3306_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v_x_3306_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3310_ = v_x_3306_;
v_isShared_3311_ = v_isSharedCheck_3316_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v_x_3306_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3316_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3314_; 
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
return v___x_3314_;
}
}
}
else
{
lean_object* v_a_3317_; 
v_a_3317_ = lean_ctor_get(v_x_3306_, 0);
lean_inc(v_a_3317_);
lean_dec_ref(v_x_3306_);
if (lean_obj_tag(v_a_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3326_; 
lean_dec_ref(v_stream_3305_);
v_a_3318_ = lean_ctor_get(v_a_3317_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_a_3317_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3320_ = v_a_3317_;
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v_a_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
}
}
else
{
lean_object* v_a_3327_; 
v_a_3327_ = lean_ctor_get(v_a_3317_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v_a_3317_);
if (lean_obj_tag(v_a_3327_) == 0)
{
lean_object* v___x_3328_; 
lean_dec_ref(v_stream_3305_);
v___x_3328_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_3328_;
}
else
{
lean_object* v_val_3329_; lean_object* v_data_3330_; lean_object* v_extensions_3331_; uint8_t v___x_3332_; 
v_val_3329_ = lean_ctor_get(v_a_3327_, 0);
lean_inc(v_val_3329_);
lean_dec_ref(v_a_3327_);
v_data_3330_ = lean_ctor_get(v_val_3329_, 0);
v_extensions_3331_ = lean_ctor_get(v_val_3329_, 1);
v___x_3332_ = l_ByteArray_isEmpty(v_data_3330_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; 
v___x_3333_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3305_, v_val_3329_);
return v___x_3333_;
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; 
v___x_3334_ = lean_array_get_size(v_extensions_3331_);
v___x_3335_ = lean_unsigned_to_nat(0u);
v___x_3336_ = lean_nat_dec_eq(v___x_3334_, v___x_3335_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; 
v___x_3337_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3305_, v_val_3329_);
return v___x_3337_;
}
else
{
lean_object* v___x_3338_; 
lean_dec(v_val_3329_);
lean_dec_ref(v_stream_3305_);
v___x_3338_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_3338_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object* v_stream_3339_, lean_object* v_x_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_3339_, v_x_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object* v_stream_3343_, lean_object* v_chunk_3344_, uint8_t v_incomplete_3345_){
_start:
{
lean_object* v___x_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; lean_object* v___x_3353_; 
lean_inc_ref(v_stream_3343_);
v___x_3347_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3343_, v_chunk_3344_, v_incomplete_3345_);
v___f_3348_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3348_, 0, v_stream_3343_);
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3347_);
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
v___x_3351_ = lean_unsigned_to_nat(0u);
v___x_3352_ = 0;
v___x_3353_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3351_, v___x_3352_, v___x_3350_, v___f_3348_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object* v_stream_3354_, lean_object* v_chunk_3355_, lean_object* v_incomplete_3356_, lean_object* v_a_3357_){
_start:
{
uint8_t v_incomplete_boxed_3358_; lean_object* v_res_3359_; 
v_incomplete_boxed_3358_ = lean_unbox(v_incomplete_3356_);
v_res_3359_ = l_Std_Http_Body_Stream_send(v_stream_3354_, v_chunk_3355_, v_incomplete_boxed_3358_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object* v_x_3360_){
_start:
{
uint8_t v___y_3363_; 
if (lean_obj_tag(v_x_3360_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3375_; 
v_a_3367_ = lean_ctor_get(v_x_3360_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_x_3360_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3369_ = v_x_3360_;
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v_x_3360_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
return v___x_3373_;
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v_pendingConsumer_3377_; 
v_a_3376_ = lean_ctor_get(v_x_3360_, 0);
lean_inc(v_a_3376_);
lean_dec_ref(v_x_3360_);
v_pendingConsumer_3377_ = lean_ctor_get(v_a_3376_, 1);
lean_inc(v_pendingConsumer_3377_);
lean_dec(v_a_3376_);
if (lean_obj_tag(v_pendingConsumer_3377_) == 0)
{
uint8_t v___x_3378_; 
v___x_3378_ = 0;
v___y_3363_ = v___x_3378_;
goto v___jp_3362_;
}
else
{
uint8_t v___x_3379_; 
lean_dec_ref(v_pendingConsumer_3377_);
v___x_3379_ = 1;
v___y_3363_ = v___x_3379_;
goto v___jp_3362_;
}
}
v___jp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3364_ = lean_box(v___y_3363_);
v___x_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object* v_x_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object* v_a_3384_){
_start:
{
lean_object* v___x_3386_; lean_object* v___f_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; lean_object* v___x_3392_; 
v___x_3386_ = lean_st_ref_get(v_a_3384_);
v___f_3387_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = 0;
v___x_3392_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3390_, v___x_3391_, v___x_3389_, v___f_3387_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object* v_a_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_3393_);
lean_dec(v_a_3393_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object* v___y_3396_, lean_object* v_x_3397_){
_start:
{
if (lean_obj_tag(v_x_3397_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3407_; 
v_a_3399_ = lean_ctor_get(v_x_3397_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_x_3397_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3401_ = v_x_3397_;
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v_x_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
}
}
else
{
lean_object* v___x_3408_; 
lean_dec_ref(v_x_3397_);
v___x_3408_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_3396_);
return v___x_3408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object* v___y_3409_, lean_object* v_x_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_3409_, v_x_3410_);
lean_dec(v___y_3409_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object* v___y_3413_){
_start:
{
lean_object* v___x_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; lean_object* v___x_3419_; 
v___x_3415_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3413_);
lean_inc(v___y_3413_);
v___f_3416_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3416_, 0, v___y_3413_);
v___x_3417_ = lean_unsigned_to_nat(0u);
v___x_3418_ = 0;
v___x_3419_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3417_, v___x_3418_, v___x_3415_, v___f_3416_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_3420_);
lean_dec(v___y_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object* v_stream_3424_){
_start:
{
lean_object* v___f_3426_; lean_object* v___x_3427_; 
v___f_3426_ = ((lean_object*)(l_Std_Http_Body_Stream_hasInterest___closed__0));
v___x_3427_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3424_, v___f_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object* v_stream_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Std_Http_Body_Stream_hasInterest(v_stream_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object* v_lose_3431_, lean_object* v___y_3432_, uint8_t v___x_3433_, lean_object* v_promise_3434_, lean_object* v_x_3435_){
_start:
{
if (lean_obj_tag(v_x_3435_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v_lose_3431_);
v_a_3437_ = lean_ctor_get(v_x_3435_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_x_3435_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3439_ = v_x_3435_;
v_isShared_3440_ = v_isSharedCheck_3445_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v_x_3435_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3445_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3459_; 
v_a_3446_ = lean_ctor_get(v_x_3435_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_x_3435_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3448_ = v_x_3435_;
v_isShared_3449_ = v_isSharedCheck_3459_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v_x_3435_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3459_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
uint8_t v___x_3450_; 
v___x_3450_ = lean_unbox(v_a_3446_);
lean_dec(v_a_3446_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
lean_del_object(v___x_3448_);
lean_inc(v___y_3432_);
v___x_3451_ = lean_apply_2(v_lose_3431_, v___y_3432_, lean_box(0));
return v___x_3451_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3454_; 
lean_dec_ref(v_lose_3431_);
v___x_3452_ = lean_box(v___x_3433_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3452_);
v___x_3454_ = v___x_3448_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3455_ = lean_io_promise_resolve(v___x_3454_, v_promise_3434_);
v___x_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
v___x_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object* v_lose_3460_, lean_object* v___y_3461_, lean_object* v___x_3462_, lean_object* v_promise_3463_, lean_object* v_x_3464_, lean_object* v___y_3465_){
_start:
{
uint8_t v___x_4623__boxed_3466_; lean_object* v_res_3467_; 
v___x_4623__boxed_3466_ = lean_unbox(v___x_3462_);
v_res_3467_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_3460_, v___y_3461_, v___x_4623__boxed_3466_, v_promise_3463_, v_x_3464_);
lean_dec(v_promise_3463_);
lean_dec(v___y_3461_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_3468_, lean_object* v_lose_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_finished_3472_; lean_object* v_promise_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___f_3477_; uint8_t v___y_3479_; uint8_t v___x_3488_; 
v_finished_3472_ = lean_ctor_get(v_w_3468_, 0);
lean_inc(v_finished_3472_);
v_promise_3473_ = lean_ctor_get(v_w_3468_, 1);
lean_inc(v_promise_3473_);
lean_dec_ref(v_w_3468_);
v___x_3474_ = lean_st_ref_take(v_finished_3472_);
v___x_3475_ = 0;
v___x_3476_ = lean_box(v___x_3475_);
lean_inc(v___y_3470_);
v___f_3477_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3477_, 0, v_lose_3469_);
lean_closure_set(v___f_3477_, 1, v___y_3470_);
lean_closure_set(v___f_3477_, 2, v___x_3476_);
lean_closure_set(v___f_3477_, 3, v_promise_3473_);
v___x_3488_ = lean_unbox(v___x_3474_);
lean_dec(v___x_3474_);
if (v___x_3488_ == 0)
{
uint8_t v___x_3489_; 
v___x_3489_ = 1;
v___y_3479_ = v___x_3489_;
goto v___jp_3478_;
}
else
{
v___y_3479_ = v___x_3475_;
goto v___jp_3478_;
}
v___jp_3478_:
{
uint8_t v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3480_ = 1;
v___x_3481_ = lean_box(v___x_3480_);
v___x_3482_ = lean_st_ref_set(v_finished_3472_, v___x_3481_);
lean_dec(v_finished_3472_);
v___x_3483_ = lean_box(v___y_3479_);
v___x_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
v___x_3486_ = lean_unsigned_to_nat(0u);
v___x_3487_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3486_, v___x_3475_, v___x_3485_, v___f_3477_);
return v___x_3487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object* v_w_3490_, lean_object* v_lose_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_3490_, v_lose_3491_, v___y_3492_);
lean_dec(v___y_3492_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object* v_w_3495_, lean_object* v_lose_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_finished_3499_; lean_object* v_promise_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___f_3504_; uint8_t v___y_3506_; uint8_t v___x_3515_; 
v_finished_3499_ = lean_ctor_get(v_w_3495_, 0);
lean_inc(v_finished_3499_);
v_promise_3500_ = lean_ctor_get(v_w_3495_, 1);
lean_inc(v_promise_3500_);
lean_dec_ref(v_w_3495_);
v___x_3501_ = lean_st_ref_take(v_finished_3499_);
v___x_3502_ = 1;
v___x_3503_ = lean_box(v___x_3502_);
lean_inc(v___y_3497_);
v___f_3504_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3504_, 0, v_lose_3496_);
lean_closure_set(v___f_3504_, 1, v___y_3497_);
lean_closure_set(v___f_3504_, 2, v___x_3503_);
lean_closure_set(v___f_3504_, 3, v_promise_3500_);
v___x_3515_ = lean_unbox(v___x_3501_);
lean_dec(v___x_3501_);
if (v___x_3515_ == 0)
{
v___y_3506_ = v___x_3502_;
goto v___jp_3505_;
}
else
{
uint8_t v___x_3516_; 
v___x_3516_ = 0;
v___y_3506_ = v___x_3516_;
goto v___jp_3505_;
}
v___jp_3505_:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; lean_object* v___x_3514_; 
v___x_3507_ = lean_box(v___x_3502_);
v___x_3508_ = lean_st_ref_set(v_finished_3499_, v___x_3507_);
lean_dec(v_finished_3499_);
v___x_3509_ = lean_box(v___y_3506_);
v___x_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
v___x_3512_ = lean_unsigned_to_nat(0u);
v___x_3513_ = 0;
v___x_3514_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3512_, v___x_3513_, v___x_3511_, v___f_3504_);
return v___x_3514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_3517_, lean_object* v_lose_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_3517_, v_lose_3518_, v___y_3519_);
lean_dec(v___y_3519_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_3538_){
_start:
{
if (lean_obj_tag(v_x_3538_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3548_; 
v_a_3540_ = lean_ctor_get(v_x_3538_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_x_3538_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3542_ = v_x_3538_;
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v_x_3538_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
return v___x_3546_;
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v_pendingConsumer_3550_; 
v_a_3549_ = lean_ctor_get(v_x_3538_, 0);
lean_inc(v_a_3549_);
lean_dec_ref(v_x_3538_);
v_pendingConsumer_3550_ = lean_ctor_get(v_a_3549_, 1);
if (lean_obj_tag(v_pendingConsumer_3550_) == 0)
{
uint8_t v_closed_3551_; 
v_closed_3551_ = lean_ctor_get_uint8(v_a_3549_, sizeof(void*)*5);
lean_dec(v_a_3549_);
if (v_closed_3551_ == 0)
{
lean_object* v___x_3552_; 
v___x_3552_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_3552_;
}
else
{
lean_object* v___x_3553_; 
v___x_3553_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_3553_;
}
}
else
{
lean_object* v___x_3554_; 
lean_dec(v_a_3549_);
v___x_3554_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_3554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_3555_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_3565_, lean_object* v___y_3566_, lean_object* v_x_3567_){
_start:
{
if (lean_obj_tag(v_x_3567_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3577_; 
lean_dec_ref(v_waiter_3565_);
v_a_3569_ = lean_ctor_get(v_x_3567_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_x_3567_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3571_ = v_x_3567_;
v_isShared_3572_ = v_isSharedCheck_3577_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v_x_3567_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3577_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3608_; 
v_a_3578_ = lean_ctor_get(v_x_3567_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_x_3567_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3580_ = v_x_3567_;
v_isShared_3581_ = v_isSharedCheck_3608_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v_x_3567_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3608_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_pendingConsumer_3582_; 
v_pendingConsumer_3582_ = lean_ctor_get(v_a_3578_, 1);
lean_inc(v_pendingConsumer_3582_);
if (lean_obj_tag(v_pendingConsumer_3582_) == 0)
{
uint8_t v_closed_3583_; 
v_closed_3583_ = lean_ctor_get_uint8(v_a_3578_, sizeof(void*)*5);
if (v_closed_3583_ == 0)
{
lean_object* v_interestWaiter_3584_; 
v_interestWaiter_3584_ = lean_ctor_get(v_a_3578_, 2);
if (lean_obj_tag(v_interestWaiter_3584_) == 0)
{
lean_object* v_pendingProducer_3585_; lean_object* v_knownSize_3586_; lean_object* v_pendingIncompleteChunk_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3600_; 
v_pendingProducer_3585_ = lean_ctor_get(v_a_3578_, 0);
v_knownSize_3586_ = lean_ctor_get(v_a_3578_, 3);
v_pendingIncompleteChunk_3587_ = lean_ctor_get(v_a_3578_, 4);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_a_3578_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; lean_object* v_unused_3602_; 
v_unused_3601_ = lean_ctor_get(v_a_3578_, 2);
lean_dec(v_unused_3601_);
v_unused_3602_ = lean_ctor_get(v_a_3578_, 1);
lean_dec(v_unused_3602_);
v___x_3589_ = v_a_3578_;
v_isShared_3590_ = v_isSharedCheck_3600_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_pendingIncompleteChunk_3587_);
lean_inc(v_knownSize_3586_);
lean_inc(v_pendingProducer_3585_);
lean_dec(v_a_3578_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3600_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3591_, 0, v_waiter_3565_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 2, v___x_3591_);
v___x_3593_ = v___x_3589_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_pendingProducer_3585_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_pendingConsumer_3582_);
lean_ctor_set(v_reuseFailAlloc_3599_, 2, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3599_, 3, v_knownSize_3586_);
lean_ctor_set(v_reuseFailAlloc_3599_, 4, v_pendingIncompleteChunk_3587_);
lean_ctor_set_uint8(v_reuseFailAlloc_3599_, sizeof(void*)*5, v_closed_3583_);
v___x_3593_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3594_ = lean_st_ref_set(v___y_3566_, v___x_3593_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3594_);
v___x_3596_ = v___x_3580_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; 
v___x_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
return v___x_3597_;
}
}
}
}
else
{
lean_object* v___x_3603_; 
lean_del_object(v___x_3580_);
lean_dec(v_a_3578_);
lean_dec_ref(v_waiter_3565_);
v___x_3603_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_3603_;
}
}
else
{
lean_object* v___f_3604_; lean_object* v___x_3605_; 
lean_del_object(v___x_3580_);
lean_dec(v_a_3578_);
v___f_3604_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_3605_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_3565_, v___f_3604_, v___y_3566_);
return v___x_3605_;
}
}
else
{
lean_object* v___f_3606_; lean_object* v___x_3607_; 
lean_dec_ref(v_pendingConsumer_3582_);
lean_del_object(v___x_3580_);
lean_dec(v_a_3578_);
v___f_3606_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_3607_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_3565_, v___f_3606_, v___y_3566_);
return v___x_3607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_3609_, lean_object* v___y_3610_, lean_object* v_x_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_3609_, v___y_3610_, v_x_3611_);
lean_dec(v___y_3610_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_3614_, lean_object* v___f_3615_, lean_object* v_x_3616_){
_start:
{
if (lean_obj_tag(v_x_3616_) == 0)
{
lean_object* v___x_3618_; 
lean_dec_ref(v___f_3615_);
v___x_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3618_, 0, v_x_3616_);
return v___x_3618_;
}
else
{
lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3630_; 
v_isSharedCheck_3630_ = !lean_is_exclusive(v_x_3616_);
if (v_isSharedCheck_3630_ == 0)
{
lean_object* v_unused_3631_; 
v_unused_3631_ = lean_ctor_get(v_x_3616_, 0);
lean_dec(v_unused_3631_);
v___x_3620_ = v_x_3616_;
v_isShared_3621_ = v_isSharedCheck_3630_;
goto v_resetjp_3619_;
}
else
{
lean_dec(v_x_3616_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3630_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3622_ = lean_st_ref_get(v___y_3614_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 0, v___x_3622_);
v___x_3624_ = v___x_3620_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; lean_object* v___x_3628_; 
v___x_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
v___x_3626_ = lean_unsigned_to_nat(0u);
v___x_3627_ = 0;
v___x_3628_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3626_, v___x_3627_, v___x_3625_, v___f_3615_);
return v___x_3628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_3632_, lean_object* v___f_3633_, lean_object* v_x_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_3632_, v___f_3633_, v_x_3634_);
lean_dec(v___y_3632_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v___x_3640_; lean_object* v___f_3641_; lean_object* v___f_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; lean_object* v___x_3645_; 
v___x_3640_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3638_);
lean_inc_n(v___y_3638_, 2);
v___f_3641_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_3641_, 0, v_waiter_3637_);
lean_closure_set(v___f_3641_, 1, v___y_3638_);
v___f_3642_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3642_, 0, v___y_3638_);
lean_closure_set(v___f_3642_, 1, v___f_3641_);
v___x_3643_ = lean_unsigned_to_nat(0u);
v___x_3644_ = 0;
v___x_3645_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3643_, v___x_3644_, v___x_3640_, v___f_3642_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_3646_, v___y_3647_);
lean_dec(v___y_3647_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_3650_, lean_object* v_waiter_3651_){
_start:
{
lean_object* v___f_3653_; lean_object* v___x_3654_; 
v___f_3653_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3653_, 0, v_waiter_3651_);
v___x_3654_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3650_, v___f_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_3655_, lean_object* v_waiter_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_3655_, v_waiter_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_3659_, lean_object* v___f_3660_, lean_object* v_x_3661_){
_start:
{
if (lean_obj_tag(v_x_3661_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3671_; 
lean_dec_ref(v___f_3660_);
v_a_3663_ = lean_ctor_get(v_x_3661_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v_x_3661_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3665_ = v_x_3661_;
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v_x_3661_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
return v___x_3669_;
}
}
}
else
{
lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3683_; 
v_isSharedCheck_3683_ = !lean_is_exclusive(v_x_3661_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v_x_3661_, 0);
lean_dec(v_unused_3684_);
v___x_3673_ = v_x_3661_;
v_isShared_3674_ = v_isSharedCheck_3683_;
goto v_resetjp_3672_;
}
else
{
lean_dec(v_x_3661_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3683_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3675_ = lean_st_ref_get(v___y_3659_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3675_);
v___x_3677_ = v___x_3673_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; lean_object* v___x_3681_; 
v___x_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = 0;
v___x_3681_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3679_, v___x_3680_, v___x_3678_, v___f_3660_);
return v___x_3681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_3685_, lean_object* v___f_3686_, lean_object* v_x_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_3685_, v___f_3686_, v_x_3687_);
lean_dec(v___y_3685_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v___x_3693_; lean_object* v___f_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; lean_object* v___x_3697_; 
v___x_3693_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3691_);
lean_inc(v___y_3691_);
v___f_3694_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_3694_, 0, v___y_3691_);
lean_closure_set(v___f_3694_, 1, v___f_3690_);
v___x_3695_ = lean_unsigned_to_nat(0u);
v___x_3696_ = 0;
v___x_3697_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3695_, v___x_3696_, v___x_3693_, v___f_3694_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_3698_, v___y_3699_);
lean_dec(v___y_3699_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_3705_){
_start:
{
lean_object* v___f_3706_; lean_object* v___f_3707_; lean_object* v___f_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___f_3706_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_3705_, 2);
v___f_3707_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3707_, 0, v_stream_3705_);
v___f_3708_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_3709_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_3709_, 0, lean_box(0));
lean_closure_set(v___x_3709_, 1, lean_box(0));
lean_closure_set(v___x_3709_, 2, v_stream_3705_);
lean_closure_set(v___x_3709_, 3, v___f_3708_);
v___x_3710_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_3710_, 0, lean_box(0));
lean_closure_set(v___x_3710_, 1, lean_box(0));
lean_closure_set(v___x_3710_, 2, v_stream_3705_);
lean_closure_set(v___x_3710_, 3, v___f_3706_);
v___x_3711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___f_3707_);
lean_ctor_set(v___x_3711_, 2, v___x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v___y_3712_){
_start:
{
if (lean_obj_tag(v___y_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
v_a_3713_ = lean_ctor_get(v___y_3712_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___y_3712_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___y_3712_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___y_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3729_; 
v_a_3721_ = lean_ctor_get(v___y_3712_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___y_3712_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3723_ = v___y_3712_;
v_isShared_3724_ = v_isSharedCheck_3729_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___y_3712_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3729_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_fst_3725_; lean_object* v___x_3727_; 
v_fst_3725_ = lean_ctor_get(v_a_3721_, 0);
lean_inc(v_fst_3725_);
lean_dec(v_a_3721_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v_fst_3725_);
v___x_3727_ = v___x_3723_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_fst_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_a_3730_, lean_object* v_x_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Std_Http_Body_Stream_close(v_a_3730_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_a_3734_, lean_object* v_x_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Std_Http_Body_stream___lam__1(v_a_3734_, v_x_3735_);
lean_dec(v_x_3735_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v___x_3738_, lean_object* v___f_3739_, lean_object* v___x_3740_, lean_object* v___f_3741_){
_start:
{
uint8_t v___x_3743_; lean_object* v___x_3744_; lean_object* v___y_3746_; 
v___x_3743_ = 0;
lean_inc(v___x_3740_);
v___x_3744_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_3738_, v___f_3739_, v___x_3740_, v___x_3743_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3748_; 
lean_dec_ref(v___f_3741_);
lean_dec(v___x_3740_);
v_a_3748_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3748_);
lean_dec_ref(v___x_3744_);
if (lean_obj_tag(v_a_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
v_a_3749_ = lean_ctor_get(v_a_3748_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_a_3748_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v_a_3748_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v_a_3748_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
v___y_3746_ = v___x_3754_;
goto v___jp_3745_;
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3765_; 
v_a_3757_ = lean_ctor_get(v_a_3748_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_a_3748_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3759_ = v_a_3748_;
v_isShared_3760_ = v_isSharedCheck_3765_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v_a_3748_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3765_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_fst_3761_; lean_object* v___x_3763_; 
v_fst_3761_ = lean_ctor_get(v_a_3757_, 0);
lean_inc(v_fst_3761_);
lean_dec(v_a_3757_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v_fst_3761_);
v___x_3763_ = v___x_3759_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_fst_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
v___y_3746_ = v___x_3763_;
goto v___jp_3745_;
}
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3774_; 
v_a_3766_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3768_ = v___x_3744_;
v_isShared_3769_ = v_isSharedCheck_3774_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3744_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3774_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3770_; lean_object* v___x_3772_; 
v___x_3770_ = lean_task_map(v___f_3741_, v_a_3766_, v___x_3740_, v___x_3743_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v___x_3770_);
v___x_3772_ = v___x_3768_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
v___jp_3745_:
{
lean_object* v___x_3747_; 
v___x_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3747_, 0, v___y_3746_);
return v___x_3747_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v___x_3775_, lean_object* v___f_3776_, lean_object* v___x_3777_, lean_object* v___f_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Std_Http_Body_stream___lam__2(v___x_3775_, v___f_3776_, v___x_3777_, v___f_3778_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_x_3781_, lean_object* v_x_3782_){
_start:
{
if (lean_obj_tag(v_x_3782_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3792_; 
lean_dec_ref(v_x_3781_);
v_a_3784_ = lean_ctor_get(v_x_3782_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v_x_3782_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3786_ = v_x_3782_;
v_isShared_3787_ = v_isSharedCheck_3792_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v_x_3782_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3792_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
return v___x_3790_;
}
}
}
else
{
lean_object* v___x_3793_; 
lean_dec_ref(v_x_3782_);
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_x_3781_);
return v___x_3793_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_x_3794_, lean_object* v_x_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Std_Http_Body_stream___lam__3(v_x_3794_, v_x_3795_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_3798_, lean_object* v___f_3799_, lean_object* v_x_3800_){
_start:
{
if (lean_obj_tag(v_x_3800_) == 0)
{
lean_object* v___x_3802_; 
lean_dec_ref(v___f_3799_);
lean_dec_ref(v_gen_3798_);
v___x_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3802_, 0, v_x_3800_);
return v___x_3802_;
}
else
{
lean_object* v_a_3803_; lean_object* v___f_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___f_3807_; lean_object* v___x_3808_; lean_object* v___f_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; 
v_a_3803_ = lean_ctor_get(v_x_3800_, 0);
lean_inc_n(v_a_3803_, 2);
v___f_3804_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3804_, 0, v_a_3803_);
v___x_3805_ = lean_apply_1(v_gen_3798_, v_a_3803_);
v___x_3806_ = lean_unsigned_to_nat(0u);
v___f_3807_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 5, 4);
lean_closure_set(v___f_3807_, 0, v___x_3805_);
lean_closure_set(v___f_3807_, 1, v___f_3804_);
lean_closure_set(v___f_3807_, 2, v___x_3806_);
lean_closure_set(v___f_3807_, 3, v___f_3799_);
v___x_3808_ = lean_io_as_task(v___f_3807_, v___x_3806_);
lean_dec_ref(v___x_3808_);
v___f_3809_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3809_, 0, v_x_3800_);
v___x_3810_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_3811_ = 0;
v___x_3812_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3806_, v___x_3811_, v___x_3810_, v___f_3809_);
return v___x_3812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_3813_, lean_object* v___f_3814_, lean_object* v_x_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Std_Http_Body_stream___lam__4(v_gen_3813_, v___f_3814_, v_x_3815_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object* v_gen_3819_){
_start:
{
lean_object* v___x_3821_; lean_object* v___f_3822_; lean_object* v___f_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; lean_object* v___x_3826_; 
v___x_3821_ = l_Std_Http_Body_mkStream();
v___f_3822_ = ((lean_object*)(l_Std_Http_Body_stream___closed__0));
v___f_3823_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3823_, 0, v_gen_3819_);
lean_closure_set(v___f_3823_, 1, v___f_3822_);
v___x_3824_ = lean_unsigned_to_nat(0u);
v___x_3825_ = 0;
v___x_3826_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3824_, v___x_3825_, v___x_3821_, v___f_3823_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Std_Http_Body_stream(v_gen_3827_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v___x_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___x_3833_; lean_object* v_pendingProducer_3834_; lean_object* v_pendingConsumer_3835_; lean_object* v_interestWaiter_3836_; uint8_t v_closed_3837_; lean_object* v_pendingIncompleteChunk_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3847_; 
v___x_3833_ = lean_st_ref_take(v___y_3831_);
v_pendingProducer_3834_ = lean_ctor_get(v___x_3833_, 0);
v_pendingConsumer_3835_ = lean_ctor_get(v___x_3833_, 1);
v_interestWaiter_3836_ = lean_ctor_get(v___x_3833_, 2);
v_closed_3837_ = lean_ctor_get_uint8(v___x_3833_, sizeof(void*)*5);
v_pendingIncompleteChunk_3838_ = lean_ctor_get(v___x_3833_, 4);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3847_ == 0)
{
lean_object* v_unused_3848_; 
v_unused_3848_ = lean_ctor_get(v___x_3833_, 3);
lean_dec(v_unused_3848_);
v___x_3840_ = v___x_3833_;
v_isShared_3841_ = v_isSharedCheck_3847_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_pendingIncompleteChunk_3838_);
lean_inc(v_interestWaiter_3836_);
lean_inc(v_pendingConsumer_3835_);
lean_inc(v_pendingProducer_3834_);
lean_dec(v___x_3833_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3847_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 3, v___x_3830_);
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_pendingProducer_3834_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_pendingConsumer_3835_);
lean_ctor_set(v_reuseFailAlloc_3846_, 2, v_interestWaiter_3836_);
lean_ctor_set(v_reuseFailAlloc_3846_, 3, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3846_, 4, v_pendingIncompleteChunk_3838_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, sizeof(void*)*5, v_closed_3837_);
v___x_3843_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3844_ = lean_st_ref_set(v___y_3831_, v___x_3843_);
v___x_3845_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_3845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v___x_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Std_Http_Body_fromBytes___lam__0(v___x_3849_, v___y_3850_);
lean_dec(v___y_3850_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1(lean_object* v___x_3853_, lean_object* v_content_3854_, lean_object* v_s_3855_, lean_object* v_x_3856_){
_start:
{
if (lean_obj_tag(v_x_3856_) == 0)
{
lean_object* v___x_3858_; 
lean_dec_ref(v_s_3855_);
lean_dec_ref(v_content_3854_);
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v_x_3856_);
return v___x_3858_;
}
else
{
lean_object* v___x_3859_; uint8_t v___x_3860_; 
lean_dec_ref(v_x_3856_);
v___x_3859_ = lean_unsigned_to_nat(0u);
v___x_3860_ = lean_nat_dec_lt(v___x_3859_, v___x_3853_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec_ref(v_s_3855_);
lean_dec_ref(v_content_3854_);
v___x_3861_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_3861_;
}
else
{
lean_object* v___x_3862_; uint8_t v___x_3863_; lean_object* v___x_3864_; 
v___x_3862_ = l_Std_Http_Chunk_ofByteArray(v_content_3854_);
v___x_3863_ = 0;
v___x_3864_ = l_Std_Http_Body_Stream_send(v_s_3855_, v___x_3862_, v___x_3863_);
return v___x_3864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1___boxed(lean_object* v___x_3865_, lean_object* v_content_3866_, lean_object* v_s_3867_, lean_object* v_x_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Std_Http_Body_fromBytes___lam__1(v___x_3865_, v_content_3866_, v_s_3867_, v_x_3868_);
lean_dec(v___x_3865_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object* v_content_3871_, lean_object* v_s_3872_){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___f_3877_; lean_object* v___x_3878_; lean_object* v___f_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; lean_object* v___x_3882_; 
v___x_3874_ = lean_byte_array_size(v_content_3871_);
v___x_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
v___x_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
v___f_3877_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3877_, 0, v___x_3876_);
lean_inc_ref(v_s_3872_);
v___x_3878_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_3872_, v___f_3877_);
v___f_3879_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3879_, 0, v___x_3874_);
lean_closure_set(v___f_3879_, 1, v_content_3871_);
lean_closure_set(v___f_3879_, 2, v_s_3872_);
v___x_3880_ = lean_unsigned_to_nat(0u);
v___x_3881_ = 0;
v___x_3882_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3880_, v___x_3881_, v___x_3878_, v___f_3879_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object* v_content_3883_, lean_object* v_s_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Std_Http_Body_fromBytes___lam__2(v_content_3883_, v_s_3884_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_3887_){
_start:
{
lean_object* v___f_3889_; lean_object* v___x_3890_; 
v___f_3889_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3889_, 0, v_content_3887_);
v___x_3890_ = l_Std_Http_Body_stream(v___f_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Std_Http_Body_fromBytes(v_content_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_a_3894_, lean_object* v___f_3895_, lean_object* v_x_3896_){
_start:
{
if (lean_obj_tag(v_x_3896_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3906_; 
lean_dec_ref(v___f_3895_);
lean_dec_ref(v_a_3894_);
v_a_3898_ = lean_ctor_get(v_x_3896_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_x_3896_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3900_ = v_x_3896_;
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v_x_3896_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
}
}
else
{
lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; lean_object* v___x_3910_; 
lean_dec_ref(v_x_3896_);
v___x_3907_ = l_Std_Http_Body_Stream_close(v_a_3894_);
v___x_3908_ = lean_unsigned_to_nat(0u);
v___x_3909_ = 0;
v___x_3910_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3908_, v___x_3909_, v___x_3907_, v___f_3895_);
return v___x_3910_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_a_3911_, lean_object* v___f_3912_, lean_object* v_x_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Std_Http_Body_empty___lam__2(v_a_3911_, v___f_3912_, v_x_3913_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0(lean_object* v_x_3922_){
_start:
{
if (lean_obj_tag(v_x_3922_) == 0)
{
lean_object* v___x_3924_; 
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v_x_3922_);
return v___x_3924_;
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3926_; lean_object* v___f_3927_; lean_object* v___x_3928_; lean_object* v___f_3929_; lean_object* v___f_3930_; uint8_t v___x_3931_; lean_object* v___x_3932_; 
v_a_3925_ = lean_ctor_get(v_x_3922_, 0);
lean_inc_n(v_a_3925_, 2);
v___x_3926_ = lean_unsigned_to_nat(0u);
v___f_3927_ = ((lean_object*)(l_Std_Http_Body_empty___lam__0___closed__2));
v___x_3928_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_3925_, v___f_3927_);
v___f_3929_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3929_, 0, v_x_3922_);
v___f_3930_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3930_, 0, v_a_3925_);
lean_closure_set(v___f_3930_, 1, v___f_3929_);
v___x_3931_ = 0;
v___x_3932_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3926_, v___x_3931_, v___x_3928_, v___f_3930_);
return v___x_3932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0___boxed(lean_object* v_x_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Std_Http_Body_empty___lam__0(v_x_3933_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___x_3938_; lean_object* v___f_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; lean_object* v___x_3942_; 
v___x_3938_ = l_Std_Http_Body_mkStream();
v___f_3939_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_3940_ = lean_unsigned_to_nat(0u);
v___x_3941_ = 0;
v___x_3942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3940_, v___x_3941_, v___x_3938_, v___f_3939_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Std_Http_Body_empty();
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_3967_, lean_object* v_f_3968_){
_start:
{
lean_object* v_line_3969_; lean_object* v_body_3970_; lean_object* v_extensions_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3979_; 
v_line_3969_ = lean_ctor_get(v_f_3968_, 0);
v_body_3970_ = lean_ctor_get(v_f_3968_, 1);
v_extensions_3971_ = lean_ctor_get(v_f_3968_, 2);
v_isSharedCheck_3979_ = !lean_is_exclusive(v_f_3968_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3973_ = v_f_3968_;
v_isShared_3974_ = v_isSharedCheck_3979_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_extensions_3971_);
lean_inc(v_body_3970_);
lean_inc(v_line_3969_);
lean_dec(v_f_3968_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3979_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3977_; 
v___x_3975_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_3967_, v_body_3970_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 1, v___x_3975_);
v___x_3977_ = v___x_3973_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_line_3969_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v___x_3975_);
lean_ctor_set(v_reuseFailAlloc_3978_, 2, v_extensions_3971_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_3983_, lean_object* v_x_3984_){
_start:
{
if (lean_obj_tag(v_x_3984_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3994_; 
lean_dec_ref(v___x_3983_);
v_a_3986_ = lean_ctor_get(v_x_3984_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v_x_3984_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3988_ = v_x_3984_;
v_isShared_3989_ = v_isSharedCheck_3994_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v_x_3984_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3994_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
return v___x_3992_;
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4014_; 
v_a_3995_ = lean_ctor_get(v_x_3984_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_x_3984_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3997_ = v_x_3984_;
v_isShared_3998_ = v_isSharedCheck_4014_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v_x_3984_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4014_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v_line_3999_; lean_object* v_body_4000_; lean_object* v_extensions_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4013_; 
v_line_3999_ = lean_ctor_get(v_a_3995_, 0);
v_body_4000_ = lean_ctor_get(v_a_3995_, 1);
v_extensions_4001_ = lean_ctor_get(v_a_3995_, 2);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_a_3995_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4003_ = v_a_3995_;
v_isShared_4004_ = v_isSharedCheck_4013_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_extensions_4001_);
lean_inc(v_body_4000_);
lean_inc(v_line_3999_);
lean_dec(v_a_3995_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4013_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4005_; lean_object* v___x_4007_; 
v___x_4005_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_3983_, v_body_4000_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 1, v___x_4005_);
v___x_4007_ = v___x_4003_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_line_3999_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v___x_4005_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_extensions_4001_);
v___x_4007_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4009_; 
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 0, v___x_4007_);
v___x_4009_ = v___x_3997_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
return v___x_4010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_4015_, lean_object* v_x_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_4015_, v_x_4016_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_4019_, lean_object* v_action_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; uint8_t v___x_4025_; lean_object* v___x_4026_; 
lean_inc_ref(v___y_4021_);
v___x_4023_ = lean_apply_2(v_action_4020_, v___y_4021_, lean_box(0));
v___x_4024_ = lean_unsigned_to_nat(0u);
v___x_4025_ = 0;
v___x_4026_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4024_, v___x_4025_, v___x_4023_, v___f_4019_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_4027_, lean_object* v_action_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_4027_, v_action_4028_, v___y_4029_);
lean_dec_ref(v___y_4029_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_4037_, lean_object* v_action_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; 
v___x_4041_ = lean_apply_1(v_action_4038_, lean_box(0));
v___x_4042_ = lean_unsigned_to_nat(0u);
v___x_4043_ = 0;
v___x_4044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4042_, v___x_4043_, v___x_4041_, v___f_4037_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_4045_, lean_object* v_action_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_4045_, v_action_4046_, v___y_4047_);
lean_dec_ref(v___y_4047_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_4053_, lean_object* v_x_4054_){
_start:
{
if (lean_obj_tag(v_x_4054_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4064_; 
v_a_4056_ = lean_ctor_get(v_x_4054_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_x_4054_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4058_ = v_x_4054_;
v_isShared_4059_ = v_isSharedCheck_4064_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v_x_4054_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4064_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4062_; 
v___x_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
return v___x_4062_;
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4074_; 
v_a_4065_ = lean_ctor_get(v_x_4054_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_x_4054_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4067_ = v_x_4054_;
v_isShared_4068_ = v_isSharedCheck_4074_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v_x_4054_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4074_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4071_; 
v___x_4069_ = l_Std_Http_Request_Builder_body___redArg(v_builder_4053_, v_a_4065_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v___x_4069_);
v___x_4071_ = v___x_4067_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4069_);
v___x_4071_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4072_; 
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_4075_, lean_object* v_x_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_4075_, v_x_4076_);
lean_dec_ref(v_builder_4075_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_4079_, lean_object* v_gen_4080_){
_start:
{
lean_object* v___x_4082_; lean_object* v___f_4083_; lean_object* v___x_4084_; uint8_t v___x_4085_; lean_object* v___x_4086_; 
v___x_4082_ = l_Std_Http_Body_stream(v_gen_4080_);
v___f_4083_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4083_, 0, v_builder_4079_);
v___x_4084_ = lean_unsigned_to_nat(0u);
v___x_4085_ = 0;
v___x_4086_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4084_, v___x_4085_, v___x_4082_, v___f_4083_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_4087_, lean_object* v_gen_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Std_Http_Request_Builder_stream(v_builder_4087_, v_gen_4088_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_4091_, lean_object* v_x_4092_){
_start:
{
if (lean_obj_tag(v_x_4092_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4102_; 
v_a_4094_ = lean_ctor_get(v_x_4092_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_x_4092_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4096_ = v_x_4092_;
v_isShared_4097_ = v_isSharedCheck_4102_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v_x_4092_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4102_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
return v___x_4100_;
}
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4112_; 
v_a_4103_ = lean_ctor_get(v_x_4092_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v_x_4092_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4105_ = v_x_4092_;
v_isShared_4106_ = v_isSharedCheck_4112_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v_x_4092_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4112_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4107_; lean_object* v___x_4109_; 
v___x_4107_ = l_Std_Http_Response_Builder_body___redArg(v_builder_4091_, v_a_4103_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v___x_4107_);
v___x_4109_ = v___x_4105_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4110_; 
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
return v___x_4110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_4113_, lean_object* v_x_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_4113_, v_x_4114_);
lean_dec_ref(v_builder_4113_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_4117_, lean_object* v_gen_4118_){
_start:
{
lean_object* v___x_4120_; lean_object* v___f_4121_; lean_object* v___x_4122_; uint8_t v___x_4123_; lean_object* v___x_4124_; 
v___x_4120_ = l_Std_Http_Body_stream(v_gen_4118_);
v___f_4121_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4121_, 0, v_builder_4117_);
v___x_4122_ = lean_unsigned_to_nat(0u);
v___x_4123_ = 0;
v___x_4124_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4122_, v___x_4123_, v___x_4120_, v___f_4121_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_4125_, lean_object* v_gen_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Std_Http_Response_Builder_stream(v_builder_4125_, v_gen_4126_);
return v_res_4128_;
}
}
lean_object* runtime_initialize_Std_Sync(uint8_t builtin);
lean_object* runtime_initialize_Std_Async(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Chunk(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Any(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Basic(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Body_Stream(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync(uint8_t builtin);
lean_object* initialize_Std_Async(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Chunk(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Body_Basic(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Body_Any(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Body_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Body_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Body_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Body_Stream(builtin);
}
#ifdef __cplusplus
}
#endif

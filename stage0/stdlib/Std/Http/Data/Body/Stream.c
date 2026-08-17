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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonadFinally___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody___redArg(lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Http_Chunk_ofByteArray(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value;
static const lean_string_object l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Http"};
static const lean_object* l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value;
static const lean_string_object l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Body"};
static const lean_object* l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value;
static const lean_string_object l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Stream"};
static const lean_object* l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value;
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value_aux_0),((lean_object*)&l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(62, 74, 245, 198, 196, 207, 141, 173)}};
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value_aux_1),((lean_object*)&l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(80, 237, 62, 34, 135, 9, 103, 192)}};
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value_aux_2),((lean_object*)&l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(35, 197, 133, 196, 74, 182, 137, 145)}};
static const lean_object* l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instImpl_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instTypeNameStream = (const lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_mkStream___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 8, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_Body_mkStream___closed__0 = (const lean_object*)&l_Std_Http_Body_mkStream___closed__0_value;
static const lean_closure_object l_Std_Http_Body_mkStream___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_mkStream___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_mkStream___closed__1 = (const lean_object*)&l_Std_Http_Body_mkStream___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream();
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_tryRecv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_tryRecv___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_tryRecv___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_tryRecv___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Stream_tryRecv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_tryRecv___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_tryRecv___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Stream_tryRecv___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_tryRecv___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___boxed(lean_object*);
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
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_closeIfAbandoned___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_closeIfAbandoned___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_closeIfAbandoned___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_closeIfAbandoned___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_stream___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_stream___lam__6___closed__0 = (const lean_object*)&l_Std_Http_Body_stream___lam__6___closed__0_value;
static const lean_closure_object l_Std_Http_Body_stream___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_stream___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_stream___lam__6___closed__0_value)} };
static const lean_object* l_Std_Http_Body_stream___lam__6___closed__1 = (const lean_object*)&l_Std_Http_Body_stream___lam__6___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_empty___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_empty___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_empty___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_empty___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_empty___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Body_empty___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Body_empty___lam__0___closed__1_value;
static const lean_closure_object l_Std_Http_Body_empty___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_stream___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_empty___lam__0___closed__1_value)} };
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
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_promise_8_);
return v___x_9_;
}
else
{
lean_object* v_finished_10_; lean_object* v___x_11_; 
v_finished_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_finished_10_);
lean_dec_ref_known(v_t_6_, 1);
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
lean_object* v_finished_44_; lean_object* v_promise_45_; lean_object* v___x_46_; uint8_t v___y_48_; uint8_t v___x_55_; 
v_finished_44_ = lean_ctor_get(v_w_41_, 0);
v_promise_45_ = lean_ctor_get(v_w_41_, 1);
v___x_46_ = lean_st_ref_take(v_finished_44_);
v___x_55_ = lean_unbox(v___x_46_);
lean_dec(v___x_46_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = 1;
v___y_48_ = v___x_56_;
goto v___jp_47_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = 0;
v___y_48_ = v___x_57_;
goto v___jp_47_;
}
v___jp_47_:
{
uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = 1;
v___x_50_ = lean_box(v___x_49_);
v___x_51_ = lean_st_ref_put(v_finished_44_, v___x_50_);
if (v___y_48_ == 0)
{
lean_object* v___x_52_; uint8_t v___x_53_; 
lean_dec_ref(v_x_40_);
v___x_52_ = lean_apply_1(v_lose_42_, lean_box(0));
v___x_53_ = lean_unbox(v___x_52_);
return v___x_53_;
}
else
{
lean_object* v___x_54_; 
lean_dec_ref(v_lose_42_);
v___x_54_ = lean_io_promise_resolve(v_x_40_, v_promise_45_);
return v___y_48_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0___boxed(lean_object* v_x_58_, lean_object* v_w_59_, lean_object* v_lose_60_, lean_object* v___y_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_58_, v_w_59_, v_lose_60_);
lean_dec_ref(v_w_59_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(uint8_t v___x_64_){
_start:
{
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed(lean_object* v___x_66_, lean_object* v___y_67_){
_start:
{
uint8_t v___x_380__boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v___x_380__boxed_68_ = lean_unbox(v___x_66_);
v_res_69_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(v___x_380__boxed_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(lean_object* v_c_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_c_74_) == 0)
{
lean_object* v_promise_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_promise_77_ = lean_ctor_get(v_c_74_, 0);
v___x_78_ = lean_io_promise_resolve(v_x_75_, v_promise_77_);
v___x_79_ = 1;
return v___x_79_;
}
else
{
lean_object* v_finished_80_; lean_object* v_lose_81_; uint8_t v___x_82_; 
v_finished_80_ = lean_ctor_get(v_c_74_, 0);
v_lose_81_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_82_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_75_, v_finished_80_, v_lose_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed(lean_object* v_c_83_, lean_object* v_x_84_, lean_object* v_a_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_c_83_, v_x_84_);
lean_dec_ref(v_c_83_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(uint8_t v_x_88_, lean_object* v_w_89_, lean_object* v_lose_90_){
_start:
{
lean_object* v_finished_92_; lean_object* v_promise_93_; lean_object* v___x_94_; uint8_t v___y_96_; uint8_t v___x_105_; 
v_finished_92_ = lean_ctor_get(v_w_89_, 0);
v_promise_93_ = lean_ctor_get(v_w_89_, 1);
v___x_94_ = lean_st_ref_take(v_finished_92_);
v___x_105_ = lean_unbox(v___x_94_);
lean_dec(v___x_94_);
if (v___x_105_ == 0)
{
uint8_t v___x_106_; 
v___x_106_ = 1;
v___y_96_ = v___x_106_;
goto v___jp_95_;
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
v___y_96_ = v___x_107_;
goto v___jp_95_;
}
v___jp_95_:
{
uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = 1;
v___x_98_ = lean_box(v___x_97_);
v___x_99_ = lean_st_ref_put(v_finished_92_, v___x_98_);
if (v___y_96_ == 0)
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_apply_1(v_lose_90_, lean_box(0));
v___x_101_ = lean_unbox(v___x_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec_ref(v_lose_90_);
v___x_102_ = lean_box(v_x_88_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
v___x_104_ = lean_io_promise_resolve(v___x_103_, v_promise_93_);
return v___y_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0___boxed(lean_object* v_x_108_, lean_object* v_w_109_, lean_object* v_lose_110_, lean_object* v___y_111_){
_start:
{
uint8_t v_x_boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v_x_boxed_112_ = lean_unbox(v_x_108_);
v_res_113_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_boxed_112_, v_w_109_, v_lose_110_);
lean_dec_ref(v_w_109_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(lean_object* v_waiter_115_, uint8_t v_x_116_){
_start:
{
lean_object* v_lose_118_; uint8_t v___x_119_; 
v_lose_118_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_119_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_116_, v_waiter_115_, v_lose_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed(lean_object* v_waiter_120_, lean_object* v_x_121_, lean_object* v_a_122_){
_start:
{
uint8_t v_x_boxed_123_; uint8_t v_res_124_; lean_object* v_r_125_; 
v_x_boxed_123_ = lean_unbox(v_x_121_);
v_res_124_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_waiter_120_, v_x_boxed_123_);
lean_dec_ref(v_waiter_120_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0(lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_147_; 
v_a_139_ = lean_ctor_get(v_x_137_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_147_ == 0)
{
v___x_141_ = v_x_137_;
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v_x_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_156_; 
v_a_148_ = lean_ctor_get(v_x_137_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_156_ == 0)
{
v___x_150_ = v_x_137_;
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v_x_137_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0___boxed(lean_object* v_x_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_Http_Body_mkStream___lam__0(v_x_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream(){
_start:
{
uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_165_ = 0;
v___x_166_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__0));
v___x_167_ = l_Std_Mutex_new___redArg(v___x_166_);
v___f_168_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__1));
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_171_, v___x_165_, v___x_170_, v___f_168_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___boxed(lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_Http_Body_mkStream();
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object* v_knownSize_175_, lean_object* v_chunk_176_){
_start:
{
if (lean_obj_tag(v_knownSize_175_) == 1)
{
lean_object* v_val_177_; 
v_val_177_ = lean_ctor_get(v_knownSize_175_, 0);
lean_inc(v_val_177_);
if (lean_obj_tag(v_val_177_) == 1)
{
lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_195_; 
v_isSharedCheck_195_ = !lean_is_exclusive(v_knownSize_175_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_knownSize_175_, 0);
lean_dec(v_unused_196_);
v___x_179_ = v_knownSize_175_;
v_isShared_180_ = v_isSharedCheck_195_;
goto v_resetjp_178_;
}
else
{
lean_dec(v_knownSize_175_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_195_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_n_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_194_; 
v_n_181_ = lean_ctor_get(v_val_177_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v_val_177_);
if (v_isSharedCheck_194_ == 0)
{
v___x_183_ = v_val_177_;
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_n_181_);
lean_dec(v_val_177_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_data_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v_data_185_ = lean_ctor_get(v_chunk_176_, 0);
v___x_186_ = lean_byte_array_size(v_data_185_);
v___x_187_ = lean_nat_sub(v_n_181_, v___x_186_);
lean_dec(v_n_181_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_187_);
v___x_189_ = v___x_183_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_189_);
v___x_191_ = v___x_179_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
else
{
lean_dec(v_val_177_);
return v_knownSize_175_;
}
}
else
{
return v_knownSize_175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object* v_knownSize_197_, lean_object* v_chunk_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_197_, v_chunk_198_);
lean_dec_ref(v_chunk_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object* v_pendingProducer_200_, lean_object* v_pendingConsumer_201_, uint8_t v_closed_202_, lean_object* v_knownSize_203_, lean_object* v_pendingIncompleteChunk_204_, lean_object* v_closeError_205_, lean_object* v_inst_206_, lean_object* v_interestWaiter_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_209_, 0, v_pendingProducer_200_);
lean_ctor_set(v___x_209_, 1, v_pendingConsumer_201_);
lean_ctor_set(v___x_209_, 2, v_interestWaiter_207_);
lean_ctor_set(v___x_209_, 3, v_knownSize_203_);
lean_ctor_set(v___x_209_, 4, v_pendingIncompleteChunk_204_);
lean_ctor_set(v___x_209_, 5, v_closeError_205_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*6, v_closed_202_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object* v_pendingProducer_212_, lean_object* v_pendingConsumer_213_, lean_object* v_closed_214_, lean_object* v_knownSize_215_, lean_object* v_pendingIncompleteChunk_216_, lean_object* v_closeError_217_, lean_object* v_inst_218_, lean_object* v_interestWaiter_219_, lean_object* v___y_220_){
_start:
{
uint8_t v_closed_boxed_221_; lean_object* v_res_222_; 
v_closed_boxed_221_ = lean_unbox(v_closed_214_);
v_res_222_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(v_pendingProducer_212_, v_pendingConsumer_213_, v_closed_boxed_221_, v_knownSize_215_, v_pendingIncompleteChunk_216_, v_closeError_217_, v_inst_218_, v_interestWaiter_219_, v___y_220_);
lean_dec(v___y_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object* v___f_223_, lean_object* v___y_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_226_; 
lean_inc(v___y_224_);
v___x_226_ = lean_apply_2(v___f_223_, v_a_225_, v___y_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object* v___f_227_, lean_object* v___y_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(v___f_227_, v___y_228_, v_a_229_);
lean_dec(v___y_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object* v_toApplicative_231_, lean_object* v_interestWaiter_232_, lean_object* v_toBind_233_, lean_object* v___f_234_, lean_object* v___f_235_, uint8_t v_a_236_){
_start:
{
if (v_a_236_ == 0)
{
lean_object* v_toPure_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v___f_235_);
v_toPure_237_ = lean_ctor_get(v_toApplicative_231_, 1);
lean_inc(v_toPure_237_);
lean_dec_ref(v_toApplicative_231_);
v___x_238_ = lean_apply_2(v_toPure_237_, lean_box(0), v_interestWaiter_232_);
v___x_239_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v___x_238_, v___f_234_);
return v___x_239_;
}
else
{
lean_object* v_toPure_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v___f_234_);
lean_dec(v_interestWaiter_232_);
v_toPure_240_ = lean_ctor_get(v_toApplicative_231_, 1);
lean_inc(v_toPure_240_);
lean_dec_ref(v_toApplicative_231_);
v___x_241_ = lean_box(0);
v___x_242_ = lean_apply_2(v_toPure_240_, lean_box(0), v___x_241_);
v___x_243_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v___x_242_, v___f_235_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object* v_toApplicative_244_, lean_object* v_interestWaiter_245_, lean_object* v_toBind_246_, lean_object* v___f_247_, lean_object* v___f_248_, lean_object* v_a_249_){
_start:
{
uint8_t v_a_boxed_250_; lean_object* v_res_251_; 
v_a_boxed_250_ = lean_unbox(v_a_249_);
v_res_251_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(v_toApplicative_244_, v_interestWaiter_245_, v_toBind_246_, v___f_247_, v___f_248_, v_a_boxed_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object* v_pendingProducer_252_, uint8_t v_closed_253_, lean_object* v_knownSize_254_, lean_object* v_pendingIncompleteChunk_255_, lean_object* v_closeError_256_, lean_object* v_inst_257_, lean_object* v_interestWaiter_258_, lean_object* v_toApplicative_259_, lean_object* v_toBind_260_, lean_object* v_pendingConsumer_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___f_264_; 
v___x_263_ = lean_box(v_closed_253_);
lean_inc(v_inst_257_);
v___f_264_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed), 9, 7);
lean_closure_set(v___f_264_, 0, v_pendingProducer_252_);
lean_closure_set(v___f_264_, 1, v_pendingConsumer_261_);
lean_closure_set(v___f_264_, 2, v___x_263_);
lean_closure_set(v___f_264_, 3, v_knownSize_254_);
lean_closure_set(v___f_264_, 4, v_pendingIncompleteChunk_255_);
lean_closure_set(v___f_264_, 5, v_closeError_256_);
lean_closure_set(v___f_264_, 6, v_inst_257_);
if (lean_obj_tag(v_interestWaiter_258_) == 0)
{
lean_object* v_toPure_265_; lean_object* v___f_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_inst_257_);
v_toPure_265_ = lean_ctor_get(v_toApplicative_259_, 1);
lean_inc(v_toPure_265_);
lean_dec_ref(v_toApplicative_259_);
lean_inc(v___y_262_);
v___f_266_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_266_, 0, v___f_264_);
lean_closure_set(v___f_266_, 1, v___y_262_);
v___x_267_ = lean_apply_2(v_toPure_265_, lean_box(0), v_interestWaiter_258_);
v___x_268_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___x_267_, v___f_266_);
return v___x_268_;
}
else
{
lean_object* v_val_269_; lean_object* v_finished_270_; lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_val_269_ = lean_ctor_get(v_interestWaiter_258_, 0);
v_finished_270_ = lean_ctor_get(v_val_269_, 0);
lean_inc(v_finished_270_);
lean_inc(v___y_262_);
v___f_271_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_271_, 0, v___f_264_);
lean_closure_set(v___f_271_, 1, v___y_262_);
lean_inc_ref(v___f_271_);
lean_inc(v_toBind_260_);
v___f_272_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_272_, 0, v_toApplicative_259_);
lean_closure_set(v___f_272_, 1, v_interestWaiter_258_);
lean_closure_set(v___f_272_, 2, v_toBind_260_);
lean_closure_set(v___f_272_, 3, v___f_271_);
lean_closure_set(v___f_272_, 4, v___f_271_);
v___x_273_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_273_, 0, lean_box(0));
lean_closure_set(v___x_273_, 1, lean_box(0));
lean_closure_set(v___x_273_, 2, v_finished_270_);
v___x_274_ = lean_apply_2(v_inst_257_, lean_box(0), v___x_273_);
v___x_275_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___x_274_, v___f_272_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object* v_pendingProducer_276_, lean_object* v_closed_277_, lean_object* v_knownSize_278_, lean_object* v_pendingIncompleteChunk_279_, lean_object* v_closeError_280_, lean_object* v_inst_281_, lean_object* v_interestWaiter_282_, lean_object* v_toApplicative_283_, lean_object* v_toBind_284_, lean_object* v_pendingConsumer_285_, lean_object* v___y_286_){
_start:
{
uint8_t v_closed_boxed_287_; lean_object* v_res_288_; 
v_closed_boxed_287_ = lean_unbox(v_closed_277_);
v_res_288_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(v_pendingProducer_276_, v_closed_boxed_287_, v_knownSize_278_, v_pendingIncompleteChunk_279_, v_closeError_280_, v_inst_281_, v_interestWaiter_282_, v_toApplicative_283_, v_toBind_284_, v_pendingConsumer_285_, v___y_286_);
lean_dec(v___y_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(lean_object* v___f_289_, lean_object* v___y_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_292_; 
lean_inc(v___y_290_);
v___x_292_ = lean_apply_2(v___f_289_, v_a_291_, v___y_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(lean_object* v___f_293_, lean_object* v___y_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(v___f_293_, v___y_294_, v_a_295_);
lean_dec(v___y_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(lean_object* v___f_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_300_; 
lean_inc(v_a_298_);
v___x_300_ = lean_apply_2(v___f_297_, v_a_299_, v_a_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(lean_object* v___f_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(v___f_301_, v_a_302_, v_a_303_);
lean_dec(v_a_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(lean_object* v_toApplicative_305_, lean_object* v_pendingConsumer_306_, lean_object* v_toBind_307_, lean_object* v___f_308_, lean_object* v___f_309_, uint8_t v_a_310_){
_start:
{
if (v_a_310_ == 0)
{
lean_object* v_toPure_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v___f_309_);
v_toPure_311_ = lean_ctor_get(v_toApplicative_305_, 1);
lean_inc(v_toPure_311_);
lean_dec_ref(v_toApplicative_305_);
v___x_312_ = lean_apply_2(v_toPure_311_, lean_box(0), v_pendingConsumer_306_);
v___x_313_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_312_, v___f_308_);
return v___x_313_;
}
else
{
lean_object* v_toPure_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v___f_308_);
lean_dec(v_pendingConsumer_306_);
v_toPure_314_ = lean_ctor_get(v_toApplicative_305_, 1);
lean_inc(v_toPure_314_);
lean_dec_ref(v_toApplicative_305_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_apply_2(v_toPure_314_, lean_box(0), v___x_315_);
v___x_317_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_316_, v___f_309_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(lean_object* v_toApplicative_318_, lean_object* v_pendingConsumer_319_, lean_object* v_toBind_320_, lean_object* v___f_321_, lean_object* v___f_322_, lean_object* v_a_323_){
_start:
{
uint8_t v_a_boxed_324_; lean_object* v_res_325_; 
v_a_boxed_324_ = lean_unbox(v_a_323_);
v_res_325_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(v_toApplicative_318_, v_pendingConsumer_319_, v_toBind_320_, v___f_321_, v___f_322_, v_a_boxed_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(lean_object* v_inst_326_, lean_object* v_toApplicative_327_, lean_object* v_toBind_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_pendingProducer_331_; lean_object* v_pendingConsumer_332_; lean_object* v_interestWaiter_333_; uint8_t v_closed_334_; lean_object* v_knownSize_335_; lean_object* v_pendingIncompleteChunk_336_; lean_object* v_closeError_337_; lean_object* v___x_338_; lean_object* v___f_339_; lean_object* v___y_341_; 
v_pendingProducer_331_ = lean_ctor_get(v_a_330_, 0);
lean_inc(v_pendingProducer_331_);
v_pendingConsumer_332_ = lean_ctor_get(v_a_330_, 1);
lean_inc(v_pendingConsumer_332_);
v_interestWaiter_333_ = lean_ctor_get(v_a_330_, 2);
lean_inc(v_interestWaiter_333_);
v_closed_334_ = lean_ctor_get_uint8(v_a_330_, sizeof(void*)*6);
v_knownSize_335_ = lean_ctor_get(v_a_330_, 3);
lean_inc(v_knownSize_335_);
v_pendingIncompleteChunk_336_ = lean_ctor_get(v_a_330_, 4);
lean_inc(v_pendingIncompleteChunk_336_);
v_closeError_337_ = lean_ctor_get(v_a_330_, 5);
lean_inc(v_closeError_337_);
lean_dec_ref(v_a_330_);
v___x_338_ = lean_box(v_closed_334_);
lean_inc(v_toBind_328_);
lean_inc_ref(v_toApplicative_327_);
lean_inc(v_inst_326_);
v___f_339_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_339_, 0, v_pendingProducer_331_);
lean_closure_set(v___f_339_, 1, v___x_338_);
lean_closure_set(v___f_339_, 2, v_knownSize_335_);
lean_closure_set(v___f_339_, 3, v_pendingIncompleteChunk_336_);
lean_closure_set(v___f_339_, 4, v_closeError_337_);
lean_closure_set(v___f_339_, 5, v_inst_326_);
lean_closure_set(v___f_339_, 6, v_interestWaiter_333_);
lean_closure_set(v___f_339_, 7, v_toApplicative_327_);
lean_closure_set(v___f_339_, 8, v_toBind_328_);
if (lean_obj_tag(v_pendingConsumer_332_) == 1)
{
lean_object* v_val_346_; 
v_val_346_ = lean_ctor_get(v_pendingConsumer_332_, 0);
if (lean_obj_tag(v_val_346_) == 1)
{
lean_object* v_finished_347_; lean_object* v_finished_348_; lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_finished_347_ = lean_ctor_get(v_val_346_, 0);
v_finished_348_ = lean_ctor_get(v_finished_347_, 0);
lean_inc(v_finished_348_);
lean_inc(v_a_329_);
v___f_349_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_349_, 0, v___f_339_);
lean_closure_set(v___f_349_, 1, v_a_329_);
lean_inc_ref(v___f_349_);
lean_inc(v_toBind_328_);
v___f_350_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_350_, 0, v_toApplicative_327_);
lean_closure_set(v___f_350_, 1, v_pendingConsumer_332_);
lean_closure_set(v___f_350_, 2, v_toBind_328_);
lean_closure_set(v___f_350_, 3, v___f_349_);
lean_closure_set(v___f_350_, 4, v___f_349_);
v___x_351_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_351_, 0, lean_box(0));
lean_closure_set(v___x_351_, 1, lean_box(0));
lean_closure_set(v___x_351_, 2, v_finished_348_);
v___x_352_ = lean_apply_2(v_inst_326_, lean_box(0), v___x_351_);
v___x_353_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_352_, v___f_350_);
return v___x_353_;
}
else
{
lean_dec(v_inst_326_);
v___y_341_ = v_a_329_;
goto v___jp_340_;
}
}
else
{
lean_dec(v_inst_326_);
v___y_341_ = v_a_329_;
goto v___jp_340_;
}
v___jp_340_:
{
lean_object* v_toPure_342_; lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_toPure_342_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc(v_toPure_342_);
lean_dec_ref(v_toApplicative_327_);
lean_inc(v___y_341_);
v___f_343_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_343_, 0, v___f_339_);
lean_closure_set(v___f_343_, 1, v___y_341_);
v___x_344_ = lean_apply_2(v_toPure_342_, lean_box(0), v_pendingConsumer_332_);
v___x_345_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_344_, v___f_343_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(lean_object* v_inst_354_, lean_object* v_toApplicative_355_, lean_object* v_toBind_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(v_inst_354_, v_toApplicative_355_, v_toBind_356_, v_a_357_, v_a_358_);
lean_dec(v_a_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_toApplicative_363_; lean_object* v_toBind_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_toApplicative_363_ = lean_ctor_get(v_inst_360_, 0);
lean_inc_ref(v_toApplicative_363_);
v_toBind_364_ = lean_ctor_get(v_inst_360_, 1);
lean_inc_n(v_toBind_364_, 2);
lean_dec_ref(v_inst_360_);
lean_inc_n(v_a_362_, 2);
lean_inc(v_inst_361_);
v___f_365_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_365_, 0, v_inst_361_);
lean_closure_set(v___f_365_, 1, v_toApplicative_363_);
lean_closure_set(v___f_365_, 2, v_toBind_364_);
lean_closure_set(v___f_365_, 3, v_a_362_);
v___x_366_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_366_, 0, lean_box(0));
lean_closure_set(v___x_366_, 1, lean_box(0));
lean_closure_set(v___x_366_, 2, v_a_362_);
v___x_367_ = lean_apply_2(v_inst_361_, lean_box(0), v___x_366_);
v___x_368_ = lean_apply_4(v_toBind_364_, lean_box(0), lean_box(0), v___x_367_, v___f_365_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_369_, v_inst_370_, v_a_371_);
lean_dec(v_a_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(lean_object* v_m_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_374_, v_inst_375_, v_a_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(lean_object* v_m_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(v_m_378_, v_inst_379_, v_inst_380_, v_a_381_);
lean_dec(v_a_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object* v_pendingProducer_383_, lean_object* v_pendingConsumer_384_, uint8_t v_closed_385_, lean_object* v_knownSize_386_, lean_object* v_pendingIncompleteChunk_387_, lean_object* v_closeError_388_, lean_object* v_a_389_, lean_object* v_inst_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_box(0);
v___x_393_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_393_, 0, v_pendingProducer_383_);
lean_ctor_set(v___x_393_, 1, v_pendingConsumer_384_);
lean_ctor_set(v___x_393_, 2, v___x_392_);
lean_ctor_set(v___x_393_, 3, v_knownSize_386_);
lean_ctor_set(v___x_393_, 4, v_pendingIncompleteChunk_387_);
lean_ctor_set(v___x_393_, 5, v_closeError_388_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*6, v_closed_385_);
lean_inc(v_a_389_);
v___x_394_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_394_, 0, lean_box(0));
lean_closure_set(v___x_394_, 1, lean_box(0));
lean_closure_set(v___x_394_, 2, v_a_389_);
lean_closure_set(v___x_394_, 3, v___x_393_);
v___x_395_ = lean_apply_2(v_inst_390_, lean_box(0), v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object* v_pendingProducer_396_, lean_object* v_pendingConsumer_397_, lean_object* v_closed_398_, lean_object* v_knownSize_399_, lean_object* v_pendingIncompleteChunk_400_, lean_object* v_closeError_401_, lean_object* v_a_402_, lean_object* v_inst_403_, lean_object* v_a_404_){
_start:
{
uint8_t v_closed_boxed_405_; lean_object* v_res_406_; 
v_closed_boxed_405_ = lean_unbox(v_closed_398_);
v_res_406_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(v_pendingProducer_396_, v_pendingConsumer_397_, v_closed_boxed_405_, v_knownSize_399_, v_pendingIncompleteChunk_400_, v_closeError_401_, v_a_402_, v_inst_403_, v_a_404_);
lean_dec(v_a_402_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(lean_object* v_toApplicative_407_, lean_object* v_a_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_toBind_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_interestWaiter_413_; 
v_interestWaiter_413_ = lean_ctor_get(v_a_412_, 2);
lean_inc(v_interestWaiter_413_);
if (lean_obj_tag(v_interestWaiter_413_) == 1)
{
lean_object* v_toFunctor_414_; lean_object* v_pendingProducer_415_; lean_object* v_pendingConsumer_416_; uint8_t v_closed_417_; lean_object* v_knownSize_418_; lean_object* v_pendingIncompleteChunk_419_; lean_object* v_closeError_420_; lean_object* v_val_421_; lean_object* v_mapConst_422_; lean_object* v___x_423_; lean_object* v___f_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_toFunctor_414_ = lean_ctor_get(v_toApplicative_407_, 0);
lean_inc_ref(v_toFunctor_414_);
lean_dec_ref(v_toApplicative_407_);
v_pendingProducer_415_ = lean_ctor_get(v_a_412_, 0);
lean_inc(v_pendingProducer_415_);
v_pendingConsumer_416_ = lean_ctor_get(v_a_412_, 1);
lean_inc(v_pendingConsumer_416_);
v_closed_417_ = lean_ctor_get_uint8(v_a_412_, sizeof(void*)*6);
v_knownSize_418_ = lean_ctor_get(v_a_412_, 3);
lean_inc(v_knownSize_418_);
v_pendingIncompleteChunk_419_ = lean_ctor_get(v_a_412_, 4);
lean_inc(v_pendingIncompleteChunk_419_);
v_closeError_420_ = lean_ctor_get(v_a_412_, 5);
lean_inc(v_closeError_420_);
lean_dec_ref(v_a_412_);
v_val_421_ = lean_ctor_get(v_interestWaiter_413_, 0);
lean_inc(v_val_421_);
lean_dec_ref_known(v_interestWaiter_413_, 1);
v_mapConst_422_ = lean_ctor_get(v_toFunctor_414_, 1);
lean_inc(v_mapConst_422_);
lean_dec_ref(v_toFunctor_414_);
v___x_423_ = lean_box(v_closed_417_);
lean_inc(v_a_408_);
v___f_424_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_424_, 0, v_pendingProducer_415_);
lean_closure_set(v___f_424_, 1, v_pendingConsumer_416_);
lean_closure_set(v___f_424_, 2, v___x_423_);
lean_closure_set(v___f_424_, 3, v_knownSize_418_);
lean_closure_set(v___f_424_, 4, v_pendingIncompleteChunk_419_);
lean_closure_set(v___f_424_, 5, v_closeError_420_);
lean_closure_set(v___f_424_, 6, v_a_408_);
lean_closure_set(v___f_424_, 7, v_inst_409_);
v___x_425_ = 1;
v___x_426_ = lean_box(v___x_425_);
v___x_427_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_427_, 0, v_val_421_);
lean_closure_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_apply_2(v_inst_410_, lean_box(0), v___x_427_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_apply_4(v_mapConst_422_, lean_box(0), lean_box(0), v___x_429_, v___x_428_);
v___x_431_ = lean_apply_4(v_toBind_411_, lean_box(0), lean_box(0), v___x_430_, v___f_424_);
return v___x_431_;
}
else
{
lean_object* v_toPure_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_interestWaiter_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_toBind_411_);
lean_dec(v_inst_410_);
lean_dec(v_inst_409_);
v_toPure_432_ = lean_ctor_get(v_toApplicative_407_, 1);
lean_inc(v_toPure_432_);
lean_dec_ref(v_toApplicative_407_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_apply_2(v_toPure_432_, lean_box(0), v___x_433_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(lean_object* v_toApplicative_435_, lean_object* v_a_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_toBind_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(v_toApplicative_435_, v_a_436_, v_inst_437_, v_inst_438_, v_toBind_439_, v_a_440_);
lean_dec(v_a_436_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_toApplicative_446_; lean_object* v_toBind_447_; lean_object* v___f_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_toApplicative_446_ = lean_ctor_get(v_inst_442_, 0);
lean_inc_ref(v_toApplicative_446_);
v_toBind_447_ = lean_ctor_get(v_inst_442_, 1);
lean_inc_n(v_toBind_447_, 2);
lean_dec_ref(v_inst_442_);
lean_inc(v_inst_443_);
lean_inc_n(v_a_445_, 2);
v___f_448_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_448_, 0, v_toApplicative_446_);
lean_closure_set(v___f_448_, 1, v_a_445_);
lean_closure_set(v___f_448_, 2, v_inst_443_);
lean_closure_set(v___f_448_, 3, v_inst_444_);
lean_closure_set(v___f_448_, 4, v_toBind_447_);
v___x_449_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_449_, 0, lean_box(0));
lean_closure_set(v___x_449_, 1, lean_box(0));
lean_closure_set(v___x_449_, 2, v_a_445_);
v___x_450_ = lean_apply_2(v_inst_443_, lean_box(0), v___x_449_);
v___x_451_ = lean_apply_4(v_toBind_447_, lean_box(0), lean_box(0), v___x_450_, v___f_448_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_452_, v_inst_453_, v_inst_454_, v_a_455_);
lean_dec(v_a_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(lean_object* v_m_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_458_, v_inst_459_, v_inst_460_, v_a_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(lean_object* v_m_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(v_m_463_, v_inst_464_, v_inst_465_, v_inst_466_, v_a_467_);
lean_dec(v_a_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_469_, lean_object* v_a_470_){
_start:
{
uint8_t v___y_472_; lean_object* v_pendingProducer_476_; 
v_pendingProducer_476_ = lean_ctor_get(v_a_470_, 0);
if (lean_obj_tag(v_pendingProducer_476_) == 0)
{
uint8_t v_closed_477_; 
v_closed_477_ = lean_ctor_get_uint8(v_a_470_, sizeof(void*)*6);
v___y_472_ = v_closed_477_;
goto v___jp_471_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = 1;
v___y_472_ = v___x_478_;
goto v___jp_471_;
}
v___jp_471_:
{
lean_object* v_toPure_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_toPure_473_ = lean_ctor_get(v_toApplicative_469_, 1);
lean_inc(v_toPure_473_);
lean_dec_ref(v_toApplicative_469_);
v___x_474_ = lean_box(v___y_472_);
v___x_475_ = lean_apply_2(v_toPure_473_, lean_box(0), v___x_474_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(v_toApplicative_479_, v_a_480_);
lean_dec_ref(v_a_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_toApplicative_485_; lean_object* v_toBind_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_toApplicative_485_ = lean_ctor_get(v_inst_482_, 0);
lean_inc_ref(v_toApplicative_485_);
v_toBind_486_ = lean_ctor_get(v_inst_482_, 1);
lean_inc(v_toBind_486_);
lean_dec_ref(v_inst_482_);
v___f_487_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_487_, 0, v_toApplicative_485_);
lean_inc(v_a_484_);
v___x_488_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_488_, 0, lean_box(0));
lean_closure_set(v___x_488_, 1, lean_box(0));
lean_closure_set(v___x_488_, 2, v_a_484_);
v___x_489_ = lean_apply_2(v_inst_483_, lean_box(0), v___x_488_);
v___x_490_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v___x_489_, v___f_487_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_491_, v_inst_492_, v_a_493_);
lean_dec(v_a_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(lean_object* v_m_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_496_, v_inst_497_, v_a_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(lean_object* v_m_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(v_m_500_, v_inst_501_, v_inst_502_, v_a_503_);
lean_dec(v_a_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(lean_object* v_toApplicative_505_, lean_object* v_a_506_){
_start:
{
uint8_t v___y_508_; lean_object* v_pendingConsumer_512_; 
v_pendingConsumer_512_ = lean_ctor_get(v_a_506_, 1);
if (lean_obj_tag(v_pendingConsumer_512_) == 0)
{
uint8_t v___x_513_; 
v___x_513_ = 0;
v___y_508_ = v___x_513_;
goto v___jp_507_;
}
else
{
uint8_t v___x_514_; 
v___x_514_ = 1;
v___y_508_ = v___x_514_;
goto v___jp_507_;
}
v___jp_507_:
{
lean_object* v_toPure_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_toPure_509_ = lean_ctor_get(v_toApplicative_505_, 1);
lean_inc(v_toPure_509_);
lean_dec_ref(v_toApplicative_505_);
v___x_510_ = lean_box(v___y_508_);
v___x_511_ = lean_apply_2(v_toPure_509_, lean_box(0), v___x_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(v_toApplicative_515_, v_a_516_);
lean_dec_ref(v_a_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_toApplicative_521_; lean_object* v_toBind_522_; lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_toApplicative_521_ = lean_ctor_get(v_inst_518_, 0);
lean_inc_ref(v_toApplicative_521_);
v_toBind_522_ = lean_ctor_get(v_inst_518_, 1);
lean_inc(v_toBind_522_);
lean_dec_ref(v_inst_518_);
v___f_523_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_523_, 0, v_toApplicative_521_);
lean_inc(v_a_520_);
v___x_524_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_524_, 0, lean_box(0));
lean_closure_set(v___x_524_, 1, lean_box(0));
lean_closure_set(v___x_524_, 2, v_a_520_);
v___x_525_ = lean_apply_2(v_inst_519_, lean_box(0), v___x_524_);
v___x_526_ = lean_apply_4(v_toBind_522_, lean_box(0), lean_box(0), v___x_525_, v___f_523_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_527_, v_inst_528_, v_a_529_);
lean_dec(v_a_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(lean_object* v_m_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_532_, v_inst_533_, v_a_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(lean_object* v_m_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(v_m_536_, v_inst_537_, v_inst_538_, v_a_539_);
lean_dec(v_a_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_541_, lean_object* v_chunk_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_toPure_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_toPure_544_ = lean_ctor_get(v_toApplicative_541_, 1);
lean_inc(v_toPure_544_);
lean_dec_ref(v_toApplicative_541_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_chunk_542_);
v___x_546_ = lean_apply_2(v_toPure_544_, lean_box(0), v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_547_, lean_object* v_done_548_, lean_object* v_inst_549_, lean_object* v_toBind_550_, lean_object* v___f_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_toFunctor_553_; lean_object* v_mapConst_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_toFunctor_553_ = lean_ctor_get(v_toApplicative_547_, 0);
lean_inc_ref(v_toFunctor_553_);
lean_dec_ref(v_toApplicative_547_);
v_mapConst_554_ = lean_ctor_get(v_toFunctor_553_, 1);
lean_inc(v_mapConst_554_);
lean_dec_ref(v_toFunctor_553_);
v___x_555_ = 1;
v___x_556_ = lean_box(v___x_555_);
v___x_557_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_557_, 0, lean_box(0));
lean_closure_set(v___x_557_, 1, v___x_556_);
lean_closure_set(v___x_557_, 2, v_done_548_);
v___x_558_ = lean_apply_2(v_inst_549_, lean_box(0), v___x_557_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_apply_4(v_mapConst_554_, lean_box(0), lean_box(0), v___x_559_, v___x_558_);
v___x_561_ = lean_apply_4(v_toBind_550_, lean_box(0), lean_box(0), v___x_560_, v___f_551_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_562_, lean_object* v_inst_563_, lean_object* v_toBind_564_, lean_object* v_a_565_, lean_object* v_inst_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_pendingProducer_568_; 
v_pendingProducer_568_ = lean_ctor_get(v_a_567_, 0);
if (lean_obj_tag(v_pendingProducer_568_) == 1)
{
lean_object* v_val_569_; lean_object* v_pendingConsumer_570_; lean_object* v_interestWaiter_571_; uint8_t v_closed_572_; lean_object* v_knownSize_573_; lean_object* v_pendingIncompleteChunk_574_; lean_object* v_closeError_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_591_; 
v_val_569_ = lean_ctor_get(v_pendingProducer_568_, 0);
lean_inc(v_val_569_);
v_pendingConsumer_570_ = lean_ctor_get(v_a_567_, 1);
v_interestWaiter_571_ = lean_ctor_get(v_a_567_, 2);
v_closed_572_ = lean_ctor_get_uint8(v_a_567_, sizeof(void*)*6);
v_knownSize_573_ = lean_ctor_get(v_a_567_, 3);
v_pendingIncompleteChunk_574_ = lean_ctor_get(v_a_567_, 4);
v_closeError_575_ = lean_ctor_get(v_a_567_, 5);
v_isSharedCheck_591_ = !lean_is_exclusive(v_a_567_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_a_567_, 0);
lean_dec(v_unused_592_);
v___x_577_ = v_a_567_;
v_isShared_578_ = v_isSharedCheck_591_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_closeError_575_);
lean_inc(v_pendingIncompleteChunk_574_);
lean_inc(v_knownSize_573_);
lean_inc(v_interestWaiter_571_);
lean_inc(v_pendingConsumer_570_);
lean_dec(v_a_567_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_591_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_chunk_579_; lean_object* v_done_580_; lean_object* v___x_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v_chunk_579_ = lean_ctor_get(v_val_569_, 0);
lean_inc_ref_n(v_chunk_579_, 2);
v_done_580_ = lean_ctor_get(v_val_569_, 1);
lean_inc(v_done_580_);
lean_dec(v_val_569_);
v___x_581_ = lean_box(0);
lean_inc_ref(v_toApplicative_562_);
v___f_582_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_582_, 0, v_toApplicative_562_);
lean_closure_set(v___f_582_, 1, v_chunk_579_);
lean_inc(v_toBind_564_);
v___f_583_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_583_, 0, v_toApplicative_562_);
lean_closure_set(v___f_583_, 1, v_done_580_);
lean_closure_set(v___f_583_, 2, v_inst_563_);
lean_closure_set(v___f_583_, 3, v_toBind_564_);
lean_closure_set(v___f_583_, 4, v___f_582_);
v___x_584_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_573_, v_chunk_579_);
lean_dec_ref(v_chunk_579_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 3, v___x_584_);
lean_ctor_set(v___x_577_, 0, v___x_581_);
v___x_586_ = v___x_577_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_pendingConsumer_570_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_interestWaiter_571_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_pendingIncompleteChunk_574_);
lean_ctor_set(v_reuseFailAlloc_590_, 5, v_closeError_575_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*6, v_closed_572_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
lean_inc(v_a_565_);
v___x_587_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_587_, 0, lean_box(0));
lean_closure_set(v___x_587_, 1, lean_box(0));
lean_closure_set(v___x_587_, 2, v_a_565_);
lean_closure_set(v___x_587_, 3, v___x_586_);
v___x_588_ = lean_apply_2(v_inst_566_, lean_box(0), v___x_587_);
v___x_589_ = lean_apply_4(v_toBind_564_, lean_box(0), lean_box(0), v___x_588_, v___f_583_);
return v___x_589_;
}
}
}
else
{
lean_object* v_toPure_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec_ref(v_a_567_);
lean_dec(v_inst_566_);
lean_dec(v_toBind_564_);
lean_dec(v_inst_563_);
v_toPure_593_ = lean_ctor_get(v_toApplicative_562_, 1);
lean_inc(v_toPure_593_);
lean_dec_ref(v_toApplicative_562_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_apply_2(v_toPure_593_, lean_box(0), v___x_594_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_toApplicative_596_, lean_object* v_inst_597_, lean_object* v_toBind_598_, lean_object* v_a_599_, lean_object* v_inst_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(v_toApplicative_596_, v_inst_597_, v_toBind_598_, v_a_599_, v_inst_600_, v_a_601_);
lean_dec(v_a_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_toApplicative_607_; lean_object* v_toBind_608_; lean_object* v___f_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_toApplicative_607_ = lean_ctor_get(v_inst_603_, 0);
lean_inc_ref(v_toApplicative_607_);
v_toBind_608_ = lean_ctor_get(v_inst_603_, 1);
lean_inc_n(v_toBind_608_, 2);
lean_dec_ref(v_inst_603_);
lean_inc(v_inst_604_);
lean_inc_n(v_a_606_, 2);
v___f_609_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_609_, 0, v_toApplicative_607_);
lean_closure_set(v___f_609_, 1, v_inst_605_);
lean_closure_set(v___f_609_, 2, v_toBind_608_);
lean_closure_set(v___f_609_, 3, v_a_606_);
lean_closure_set(v___f_609_, 4, v_inst_604_);
v___x_610_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_610_, 0, lean_box(0));
lean_closure_set(v___x_610_, 1, lean_box(0));
lean_closure_set(v___x_610_, 2, v_a_606_);
v___x_611_ = lean_apply_2(v_inst_604_, lean_box(0), v___x_610_);
v___x_612_ = lean_apply_4(v_toBind_608_, lean_box(0), lean_box(0), v___x_611_, v___f_609_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_613_, v_inst_614_, v_inst_615_, v_a_616_);
lean_dec(v_a_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(lean_object* v_m_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_619_, v_inst_620_, v_inst_621_, v_a_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(lean_object* v_m_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(v_m_624_, v_inst_625_, v_inst_626_, v_inst_627_, v_a_628_);
lean_dec(v_a_628_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0(lean_object* v_toApplicative_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_closeError_634_; 
v_closeError_634_ = lean_ctor_get(v_a_633_, 5);
lean_inc(v_closeError_634_);
lean_dec_ref(v_a_633_);
if (lean_obj_tag(v_closeError_634_) == 1)
{
lean_object* v_val_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_644_; 
v_val_635_ = lean_ctor_get(v_closeError_634_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_closeError_634_);
if (v_isSharedCheck_644_ == 0)
{
v___x_637_ = v_closeError_634_;
v_isShared_638_ = v_isSharedCheck_644_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_val_635_);
lean_dec(v_closeError_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_644_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_toPure_639_; lean_object* v___x_641_; 
v_toPure_639_ = lean_ctor_get(v_toApplicative_632_, 1);
lean_inc(v_toPure_639_);
lean_dec_ref(v_toApplicative_632_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 0);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_val_635_);
v___x_641_ = v_reuseFailAlloc_643_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; 
v___x_642_ = lean_apply_2(v_toPure_639_, lean_box(0), v___x_641_);
return v___x_642_;
}
}
}
else
{
lean_object* v_toPure_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec(v_closeError_634_);
v_toPure_645_ = lean_ctor_get(v_toApplicative_632_, 1);
lean_inc(v_toPure_645_);
lean_dec_ref(v_toApplicative_632_);
v___x_646_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_647_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_646_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(lean_object* v_toApplicative_648_, lean_object* v_a_649_, lean_object* v_inst_650_, lean_object* v_toBind_651_, lean_object* v___f_652_, lean_object* v_a_653_){
_start:
{
if (lean_obj_tag(v_a_653_) == 1)
{
lean_object* v_toPure_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec(v___f_652_);
lean_dec(v_toBind_651_);
lean_dec(v_inst_650_);
v_toPure_654_ = lean_ctor_get(v_toApplicative_648_, 1);
lean_inc(v_toPure_654_);
lean_dec_ref(v_toApplicative_648_);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v_a_653_);
v___x_656_ = lean_apply_2(v_toPure_654_, lean_box(0), v___x_655_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_a_653_);
lean_dec_ref(v_toApplicative_648_);
lean_inc(v_a_649_);
v___x_657_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_657_, 0, lean_box(0));
lean_closure_set(v___x_657_, 1, lean_box(0));
lean_closure_set(v___x_657_, 2, v_a_649_);
v___x_658_ = lean_apply_2(v_inst_650_, lean_box(0), v___x_657_);
v___x_659_ = lean_apply_4(v_toBind_651_, lean_box(0), lean_box(0), v___x_658_, v___f_652_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_660_, lean_object* v_a_661_, lean_object* v_inst_662_, lean_object* v_toBind_663_, lean_object* v___f_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(v_toApplicative_660_, v_a_661_, v_inst_662_, v_toBind_663_, v___f_664_, v_a_665_);
lean_dec(v_a_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_toApplicative_671_; lean_object* v_toBind_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_toApplicative_671_ = lean_ctor_get(v_inst_667_, 0);
v_toBind_672_ = lean_ctor_get(v_inst_667_, 1);
lean_inc_n(v_toBind_672_, 2);
lean_inc_ref_n(v_toApplicative_671_, 2);
v___f_673_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_673_, 0, v_toApplicative_671_);
lean_inc(v_inst_668_);
lean_inc(v_a_670_);
v___f_674_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_674_, 0, v_toApplicative_671_);
lean_closure_set(v___f_674_, 1, v_a_670_);
lean_closure_set(v___f_674_, 2, v_inst_668_);
lean_closure_set(v___f_674_, 3, v_toBind_672_);
lean_closure_set(v___f_674_, 4, v___f_673_);
v___x_675_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_667_, v_inst_668_, v_inst_669_, v_a_670_);
v___x_676_ = lean_apply_4(v_toBind_672_, lean_box(0), lean_box(0), v___x_675_, v___f_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___boxed(lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_677_, v_inst_678_, v_inst_679_, v_a_680_);
lean_dec(v_a_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(lean_object* v_m_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_683_, v_inst_684_, v_inst_685_, v_a_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___boxed(lean_object* v_m_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(v_m_688_, v_inst_689_, v_inst_690_, v_inst_691_, v_a_692_);
lean_dec(v_a_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(uint8_t v___x_694_, lean_object* v_knownSize_695_, lean_object* v_closeError_696_, lean_object* v_inst_697_, lean_object* v_____r_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_700_ = lean_box(0);
v___x_701_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
lean_ctor_set(v___x_701_, 2, v___x_700_);
lean_ctor_set(v___x_701_, 3, v_knownSize_695_);
lean_ctor_set(v___x_701_, 4, v___x_700_);
lean_ctor_set(v___x_701_, 5, v_closeError_696_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*6, v___x_694_);
lean_inc(v___y_699_);
v___x_702_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_702_, 0, lean_box(0));
lean_closure_set(v___x_702_, 1, lean_box(0));
lean_closure_set(v___x_702_, 2, v___y_699_);
lean_closure_set(v___x_702_, 3, v___x_701_);
v___x_703_ = lean_apply_2(v_inst_697_, lean_box(0), v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed(lean_object* v___x_704_, lean_object* v_knownSize_705_, lean_object* v_closeError_706_, lean_object* v_inst_707_, lean_object* v_____r_708_, lean_object* v___y_709_){
_start:
{
uint8_t v___x_848__boxed_710_; lean_object* v_res_711_; 
v___x_848__boxed_710_ = lean_unbox(v___x_704_);
v_res_711_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(v___x_848__boxed_710_, v_knownSize_705_, v_closeError_706_, v_inst_707_, v_____r_708_, v___y_709_);
lean_dec(v___y_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(lean_object* v___f_712_, lean_object* v___y_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_715_; 
lean_inc(v___y_713_);
v___x_715_ = lean_apply_2(v___f_712_, v_a_714_, v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object* v___f_716_, lean_object* v___y_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(v___f_716_, v___y_717_, v_a_718_);
lean_dec(v___y_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object* v_pendingProducer_720_, lean_object* v_toApplicative_721_, lean_object* v___f_722_, uint8_t v_closed_723_, lean_object* v_inst_724_, lean_object* v_toBind_725_, lean_object* v_____r_726_, lean_object* v___y_727_){
_start:
{
if (lean_obj_tag(v_pendingProducer_720_) == 1)
{
lean_object* v_val_728_; lean_object* v_toFunctor_729_; lean_object* v_done_730_; lean_object* v_mapConst_731_; lean_object* v___f_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_val_728_ = lean_ctor_get(v_pendingProducer_720_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v_pendingProducer_720_, 1);
v_toFunctor_729_ = lean_ctor_get(v_toApplicative_721_, 0);
lean_inc_ref(v_toFunctor_729_);
lean_dec_ref(v_toApplicative_721_);
v_done_730_ = lean_ctor_get(v_val_728_, 1);
lean_inc(v_done_730_);
lean_dec(v_val_728_);
v_mapConst_731_ = lean_ctor_get(v_toFunctor_729_, 1);
lean_inc(v_mapConst_731_);
lean_dec_ref(v_toFunctor_729_);
lean_inc(v___y_727_);
v___f_732_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_732_, 0, v___f_722_);
lean_closure_set(v___f_732_, 1, v___y_727_);
v___x_733_ = lean_box(v_closed_723_);
v___x_734_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_734_, 0, lean_box(0));
lean_closure_set(v___x_734_, 1, v___x_733_);
lean_closure_set(v___x_734_, 2, v_done_730_);
v___x_735_ = lean_apply_2(v_inst_724_, lean_box(0), v___x_734_);
v___x_736_ = lean_box(0);
v___x_737_ = lean_apply_4(v_mapConst_731_, lean_box(0), lean_box(0), v___x_736_, v___x_735_);
v___x_738_ = lean_apply_4(v_toBind_725_, lean_box(0), lean_box(0), v___x_737_, v___f_732_);
return v___x_738_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v_toBind_725_);
lean_dec(v_inst_724_);
lean_dec_ref(v_toApplicative_721_);
lean_dec(v_pendingProducer_720_);
v___x_739_ = lean_box(0);
lean_inc(v___y_727_);
v___x_740_ = lean_apply_2(v___f_722_, v___x_739_, v___y_727_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed(lean_object* v_pendingProducer_741_, lean_object* v_toApplicative_742_, lean_object* v___f_743_, lean_object* v_closed_744_, lean_object* v_inst_745_, lean_object* v_toBind_746_, lean_object* v_____r_747_, lean_object* v___y_748_){
_start:
{
uint8_t v_closed_boxed_749_; lean_object* v_res_750_; 
v_closed_boxed_749_ = lean_unbox(v_closed_744_);
v_res_750_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(v_pendingProducer_741_, v_toApplicative_742_, v___f_743_, v_closed_boxed_749_, v_inst_745_, v_toBind_746_, v_____r_747_, v___y_748_);
lean_dec(v___y_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object* v_interestWaiter_751_, lean_object* v_toApplicative_752_, lean_object* v___f_753_, uint8_t v_closed_754_, lean_object* v_inst_755_, lean_object* v_toBind_756_, lean_object* v_____r_757_, lean_object* v___y_758_){
_start:
{
if (lean_obj_tag(v_interestWaiter_751_) == 1)
{
lean_object* v_toFunctor_759_; lean_object* v_val_760_; lean_object* v_mapConst_761_; lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_toFunctor_759_ = lean_ctor_get(v_toApplicative_752_, 0);
lean_inc_ref(v_toFunctor_759_);
lean_dec_ref(v_toApplicative_752_);
v_val_760_ = lean_ctor_get(v_interestWaiter_751_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v_interestWaiter_751_, 1);
v_mapConst_761_ = lean_ctor_get(v_toFunctor_759_, 1);
lean_inc(v_mapConst_761_);
lean_dec_ref(v_toFunctor_759_);
lean_inc(v___y_758_);
v___f_762_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_762_, 0, v___f_753_);
lean_closure_set(v___f_762_, 1, v___y_758_);
v___x_763_ = lean_box(v_closed_754_);
v___x_764_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_764_, 0, v_val_760_);
lean_closure_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_apply_2(v_inst_755_, lean_box(0), v___x_764_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_apply_4(v_mapConst_761_, lean_box(0), lean_box(0), v___x_766_, v___x_765_);
v___x_768_ = lean_apply_4(v_toBind_756_, lean_box(0), lean_box(0), v___x_767_, v___f_762_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v_toBind_756_);
lean_dec(v_inst_755_);
lean_dec_ref(v_toApplicative_752_);
lean_dec(v_interestWaiter_751_);
v___x_769_ = lean_box(0);
lean_inc(v___y_758_);
v___x_770_ = lean_apply_2(v___f_753_, v___x_769_, v___y_758_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object* v_interestWaiter_771_, lean_object* v_toApplicative_772_, lean_object* v___f_773_, lean_object* v_closed_774_, lean_object* v_inst_775_, lean_object* v_toBind_776_, lean_object* v_____r_777_, lean_object* v___y_778_){
_start:
{
uint8_t v_closed_boxed_779_; lean_object* v_res_780_; 
v_closed_boxed_779_ = lean_unbox(v_closed_774_);
v_res_780_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_771_, v_toApplicative_772_, v___f_773_, v_closed_boxed_779_, v_inst_775_, v_toBind_776_, v_____r_777_, v___y_778_);
lean_dec(v___y_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(lean_object* v___f_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_784_; 
lean_inc(v_a_782_);
v___x_784_ = lean_apply_2(v___f_781_, v_a_783_, v_a_782_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object* v___f_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(v___f_785_, v_a_786_, v_a_787_);
lean_dec(v_a_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object* v_inst_789_, lean_object* v_toApplicative_790_, lean_object* v_inst_791_, lean_object* v_toBind_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
uint8_t v_closed_795_; 
v_closed_795_ = lean_ctor_get_uint8(v_a_794_, sizeof(void*)*6);
if (v_closed_795_ == 0)
{
lean_object* v_pendingProducer_796_; lean_object* v_pendingConsumer_797_; lean_object* v_interestWaiter_798_; lean_object* v_knownSize_799_; lean_object* v_closeError_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v___f_807_; 
v_pendingProducer_796_ = lean_ctor_get(v_a_794_, 0);
lean_inc(v_pendingProducer_796_);
v_pendingConsumer_797_ = lean_ctor_get(v_a_794_, 1);
lean_inc(v_pendingConsumer_797_);
v_interestWaiter_798_ = lean_ctor_get(v_a_794_, 2);
lean_inc_n(v_interestWaiter_798_, 2);
v_knownSize_799_ = lean_ctor_get(v_a_794_, 3);
lean_inc(v_knownSize_799_);
v_closeError_800_ = lean_ctor_get(v_a_794_, 5);
lean_inc_n(v_closeError_800_, 2);
lean_dec_ref(v_a_794_);
v___x_801_ = 1;
v___x_802_ = lean_box(v___x_801_);
v___f_803_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_803_, 0, v___x_802_);
lean_closure_set(v___f_803_, 1, v_knownSize_799_);
lean_closure_set(v___f_803_, 2, v_closeError_800_);
lean_closure_set(v___f_803_, 3, v_inst_789_);
v___x_804_ = lean_box(v_closed_795_);
lean_inc_n(v_toBind_792_, 2);
lean_inc_n(v_inst_791_, 2);
lean_inc_ref_n(v_toApplicative_790_, 2);
v___f_805_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_805_, 0, v_pendingProducer_796_);
lean_closure_set(v___f_805_, 1, v_toApplicative_790_);
lean_closure_set(v___f_805_, 2, v___f_803_);
lean_closure_set(v___f_805_, 3, v___x_804_);
lean_closure_set(v___f_805_, 4, v_inst_791_);
lean_closure_set(v___f_805_, 5, v_toBind_792_);
v___x_806_ = lean_box(v_closed_795_);
lean_inc_ref(v___f_805_);
v___f_807_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_807_, 0, v_interestWaiter_798_);
lean_closure_set(v___f_807_, 1, v_toApplicative_790_);
lean_closure_set(v___f_807_, 2, v___f_805_);
lean_closure_set(v___f_807_, 3, v___x_806_);
lean_closure_set(v___f_807_, 4, v_inst_791_);
lean_closure_set(v___f_807_, 5, v_toBind_792_);
if (lean_obj_tag(v_pendingConsumer_797_) == 1)
{
lean_object* v_val_808_; lean_object* v___f_809_; lean_object* v___y_811_; 
lean_dec_ref(v___f_805_);
lean_dec(v_interestWaiter_798_);
v_val_808_ = lean_ctor_get(v_pendingConsumer_797_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v_pendingConsumer_797_, 1);
lean_inc(v_a_793_);
v___f_809_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_809_, 0, v___f_807_);
lean_closure_set(v___f_809_, 1, v_a_793_);
if (lean_obj_tag(v_closeError_800_) == 0)
{
lean_object* v___x_819_; 
v___x_819_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___y_811_ = v___x_819_;
goto v___jp_810_;
}
else
{
lean_object* v_val_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_val_820_ = lean_ctor_get(v_closeError_800_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v_closeError_800_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v_closeError_800_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_val_820_);
lean_dec(v_closeError_800_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_val_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
v___y_811_ = v___x_825_;
goto v___jp_810_;
}
}
}
v___jp_810_:
{
lean_object* v_toFunctor_812_; lean_object* v_mapConst_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_toFunctor_812_ = lean_ctor_get(v_toApplicative_790_, 0);
lean_inc_ref(v_toFunctor_812_);
lean_dec_ref(v_toApplicative_790_);
v_mapConst_813_ = lean_ctor_get(v_toFunctor_812_, 1);
lean_inc(v_mapConst_813_);
lean_dec_ref(v_toFunctor_812_);
v___x_814_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed), 3, 2);
lean_closure_set(v___x_814_, 0, v_val_808_);
lean_closure_set(v___x_814_, 1, v___y_811_);
v___x_815_ = lean_apply_2(v_inst_791_, lean_box(0), v___x_814_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_apply_4(v_mapConst_813_, lean_box(0), lean_box(0), v___x_816_, v___x_815_);
v___x_818_ = lean_apply_4(v_toBind_792_, lean_box(0), lean_box(0), v___x_817_, v___f_809_);
return v___x_818_;
}
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref(v___f_807_);
lean_dec(v_closeError_800_);
lean_dec(v_pendingConsumer_797_);
v___x_828_ = lean_box(0);
v___x_829_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_798_, v_toApplicative_790_, v___f_805_, v_closed_795_, v_inst_791_, v_toBind_792_, v___x_828_, v_a_793_);
return v___x_829_;
}
}
else
{
lean_object* v_toPure_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec_ref(v_a_794_);
lean_dec(v_toBind_792_);
lean_dec(v_inst_791_);
lean_dec(v_inst_789_);
v_toPure_830_ = lean_ctor_get(v_toApplicative_790_, 1);
lean_inc(v_toPure_830_);
lean_dec_ref(v_toApplicative_790_);
v___x_831_ = lean_box(0);
v___x_832_ = lean_apply_2(v_toPure_830_, lean_box(0), v___x_831_);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object* v_inst_833_, lean_object* v_toApplicative_834_, lean_object* v_inst_835_, lean_object* v_toBind_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(v_inst_833_, v_toApplicative_834_, v_inst_835_, v_toBind_836_, v_a_837_, v_a_838_);
lean_dec(v_a_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_toApplicative_844_; lean_object* v_toBind_845_; lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_toApplicative_844_ = lean_ctor_get(v_inst_840_, 0);
lean_inc_ref(v_toApplicative_844_);
v_toBind_845_ = lean_ctor_get(v_inst_840_, 1);
lean_inc_n(v_toBind_845_, 2);
lean_dec_ref(v_inst_840_);
lean_inc_n(v_a_843_, 2);
lean_inc(v_inst_841_);
v___f_846_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_846_, 0, v_inst_841_);
lean_closure_set(v___f_846_, 1, v_toApplicative_844_);
lean_closure_set(v___f_846_, 2, v_inst_842_);
lean_closure_set(v___f_846_, 3, v_toBind_845_);
lean_closure_set(v___f_846_, 4, v_a_843_);
v___x_847_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_847_, 0, lean_box(0));
lean_closure_set(v___x_847_, 1, lean_box(0));
lean_closure_set(v___x_847_, 2, v_a_843_);
v___x_848_ = lean_apply_2(v_inst_841_, lean_box(0), v___x_847_);
v___x_849_ = lean_apply_4(v_toBind_845_, lean_box(0), lean_box(0), v___x_848_, v___f_846_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_inst_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_850_, v_inst_851_, v_inst_852_, v_a_853_);
lean_dec(v_a_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object* v_m_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_856_, v_inst_857_, v_inst_858_, v_a_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object* v_m_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(v_m_861_, v_inst_862_, v_inst_863_, v_inst_864_, v_a_865_);
lean_dec(v_a_865_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object* v_pendingProducer_871_, lean_object* v_pendingConsumer_872_, uint8_t v_closed_873_, lean_object* v_knownSize_874_, lean_object* v_pendingIncompleteChunk_875_, lean_object* v_closeError_876_, lean_object* v_interestWaiter_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_880_, 0, v_pendingProducer_871_);
lean_ctor_set(v___x_880_, 1, v_pendingConsumer_872_);
lean_ctor_set(v___x_880_, 2, v_interestWaiter_877_);
lean_ctor_set(v___x_880_, 3, v_knownSize_874_);
lean_ctor_set(v___x_880_, 4, v_pendingIncompleteChunk_875_);
lean_ctor_set(v___x_880_, 5, v_closeError_876_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*6, v_closed_873_);
v___x_881_ = lean_st_ref_swap(v___y_878_, v___x_880_);
lean_dec(v___x_881_);
v___x_882_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object* v_pendingProducer_883_, lean_object* v_pendingConsumer_884_, lean_object* v_closed_885_, lean_object* v_knownSize_886_, lean_object* v_pendingIncompleteChunk_887_, lean_object* v_closeError_888_, lean_object* v_interestWaiter_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v_closed_boxed_892_; lean_object* v_res_893_; 
v_closed_boxed_892_ = lean_unbox(v_closed_885_);
v_res_893_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_883_, v_pendingConsumer_884_, v_closed_boxed_892_, v_knownSize_886_, v_pendingIncompleteChunk_887_, v_closeError_888_, v_interestWaiter_889_, v___y_890_);
lean_dec(v___y_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object* v___f_894_, lean_object* v___y_895_, lean_object* v_x_896_){
_start:
{
if (lean_obj_tag(v_x_896_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v___f_894_);
v_a_898_ = lean_ctor_get(v_x_896_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_x_896_);
if (v_isSharedCheck_906_ == 0)
{
v___x_900_ = v_x_896_;
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v_x_896_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_905_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_908_; 
v_a_907_ = lean_ctor_get(v_x_896_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v_x_896_, 1);
lean_inc(v___y_895_);
v___x_908_ = lean_apply_3(v___f_894_, v_a_907_, v___y_895_, lean_box(0));
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object* v___f_909_, lean_object* v___y_910_, lean_object* v_x_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_909_, v___y_910_, v_x_911_);
lean_dec(v___y_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object* v_interestWaiter_918_, lean_object* v___f_919_, lean_object* v___f_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v___f_920_);
lean_dec_ref(v___f_919_);
lean_dec(v_interestWaiter_918_);
v_a_923_ = lean_ctor_get(v_x_921_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_921_);
if (v_isSharedCheck_931_ == 0)
{
v___x_925_ = v_x_921_;
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v_x_921_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_923_);
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
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_948_; 
v_a_932_ = lean_ctor_get(v_x_921_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_x_921_);
if (v_isSharedCheck_948_ == 0)
{
v___x_934_ = v_x_921_;
v_isShared_935_ = v_isSharedCheck_948_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v_x_921_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_948_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
uint8_t v___x_936_; 
v___x_936_ = lean_unbox(v_a_932_);
if (v___x_936_ == 0)
{
lean_object* v___x_938_; 
lean_dec_ref(v___f_920_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v_interestWaiter_918_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_interestWaiter_918_);
v___x_938_ = v_reuseFailAlloc_943_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; lean_object* v___x_942_; 
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_unbox(v_a_932_);
lean_dec(v_a_932_);
v___x_942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_940_, v___x_941_, v___x_939_, v___f_919_);
return v___x_942_;
}
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; 
lean_del_object(v___x_934_);
lean_dec(v_a_932_);
lean_dec_ref(v___f_919_);
lean_dec(v_interestWaiter_918_);
v___x_944_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1));
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = 0;
v___x_947_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_945_, v___x_946_, v___x_944_, v___f_920_);
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object* v_interestWaiter_949_, lean_object* v___f_950_, lean_object* v___f_951_, lean_object* v_x_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_949_, v___f_950_, v___f_951_, v_x_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object* v_pendingProducer_955_, uint8_t v_closed_956_, lean_object* v_knownSize_957_, lean_object* v_pendingIncompleteChunk_958_, lean_object* v_closeError_959_, lean_object* v_interestWaiter_960_, lean_object* v_pendingConsumer_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v___f_965_; 
v___x_964_ = lean_box(v_closed_956_);
v___f_965_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed), 9, 6);
lean_closure_set(v___f_965_, 0, v_pendingProducer_955_);
lean_closure_set(v___f_965_, 1, v_pendingConsumer_961_);
lean_closure_set(v___f_965_, 2, v___x_964_);
lean_closure_set(v___f_965_, 3, v_knownSize_957_);
lean_closure_set(v___f_965_, 4, v_pendingIncompleteChunk_958_);
lean_closure_set(v___f_965_, 5, v_closeError_959_);
if (lean_obj_tag(v_interestWaiter_960_) == 0)
{
lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; lean_object* v___x_971_; 
lean_inc(v___y_962_);
v___f_966_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_966_, 0, v___f_965_);
lean_closure_set(v___f_966_, 1, v___y_962_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v_interestWaiter_960_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = 0;
v___x_971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_969_, v___x_970_, v___x_968_, v___f_966_);
return v___x_971_;
}
else
{
lean_object* v_val_972_; lean_object* v_finished_973_; lean_object* v___x_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; 
v_val_972_ = lean_ctor_get(v_interestWaiter_960_, 0);
v_finished_973_ = lean_ctor_get(v_val_972_, 0);
v___x_974_ = lean_st_ref_get(v_finished_973_);
lean_inc(v___y_962_);
v___f_975_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_975_, 0, v___f_965_);
lean_closure_set(v___f_975_, 1, v___y_962_);
lean_inc_ref(v___f_975_);
v___f_976_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed), 5, 3);
lean_closure_set(v___f_976_, 0, v_interestWaiter_960_);
lean_closure_set(v___f_976_, 1, v___f_975_);
lean_closure_set(v___f_976_, 2, v___f_975_);
v___x_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_974_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = 0;
v___x_981_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_979_, v___x_980_, v___x_978_, v___f_976_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object* v_pendingProducer_982_, lean_object* v_closed_983_, lean_object* v_knownSize_984_, lean_object* v_pendingIncompleteChunk_985_, lean_object* v_closeError_986_, lean_object* v_interestWaiter_987_, lean_object* v_pendingConsumer_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v_closed_boxed_991_; lean_object* v_res_992_; 
v_closed_boxed_991_ = lean_unbox(v_closed_983_);
v_res_992_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_982_, v_closed_boxed_991_, v_knownSize_984_, v_pendingIncompleteChunk_985_, v_closeError_986_, v_interestWaiter_987_, v_pendingConsumer_988_, v___y_989_);
lean_dec(v___y_989_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object* v___f_993_, lean_object* v___y_994_, lean_object* v_x_995_){
_start:
{
if (lean_obj_tag(v_x_995_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v___f_993_);
v_a_997_ = lean_ctor_get(v_x_995_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_x_995_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_999_ = v_x_995_;
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v_x_995_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v_x_995_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v_x_995_, 1);
lean_inc(v___y_994_);
v___x_1007_ = lean_apply_3(v___f_993_, v_a_1006_, v___y_994_, lean_box(0));
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object* v___f_1008_, lean_object* v___y_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_1008_, v___y_1009_, v_x_1010_);
lean_dec(v___y_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object* v___f_1013_, lean_object* v_a_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1015_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v___f_1013_);
v_a_1017_ = lean_ctor_get(v_x_1015_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_x_1015_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1019_ = v_x_1015_;
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v_x_1015_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v_x_1015_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v_x_1015_, 1);
lean_inc(v_a_1014_);
v___x_1027_ = lean_apply_3(v___f_1013_, v_a_1026_, v_a_1014_, lean_box(0));
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object* v___f_1028_, lean_object* v_a_1029_, lean_object* v_x_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_1028_, v_a_1029_, v_x_1030_);
lean_dec(v_a_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object* v_pendingConsumer_1037_, lean_object* v___f_1038_, lean_object* v___f_1039_, lean_object* v_x_1040_){
_start:
{
if (lean_obj_tag(v_x_1040_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v___f_1039_);
lean_dec_ref(v___f_1038_);
lean_dec(v_pendingConsumer_1037_);
v_a_1042_ = lean_ctor_get(v_x_1040_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_x_1040_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1044_ = v_x_1040_;
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v_x_1040_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1067_; 
v_a_1051_ = lean_ctor_get(v_x_1040_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_x_1040_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1053_ = v_x_1040_;
v_isShared_1054_ = v_isSharedCheck_1067_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v_x_1040_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1067_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_unbox(v_a_1051_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1057_; 
lean_dec_ref(v___f_1039_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v_pendingConsumer_1037_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_pendingConsumer_1037_);
v___x_1057_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; 
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_unbox(v_a_1051_);
lean_dec(v_a_1051_);
v___x_1061_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1059_, v___x_1060_, v___x_1058_, v___f_1038_);
return v___x_1061_;
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; 
lean_del_object(v___x_1053_);
lean_dec(v_a_1051_);
lean_dec_ref(v___f_1038_);
lean_dec(v_pendingConsumer_1037_);
v___x_1063_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1));
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = 0;
v___x_1066_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1064_, v___x_1065_, v___x_1063_, v___f_1039_);
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object* v_pendingConsumer_1068_, lean_object* v___f_1069_, lean_object* v___f_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_1068_, v___f_1069_, v___f_1070_, v_x_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object* v_a_1074_, lean_object* v_x_1075_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1085_; 
v_a_1077_ = lean_ctor_get(v_x_1075_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1079_ = v_x_1075_;
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v_x_1075_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1126_; 
v_a_1086_ = lean_ctor_get(v_x_1075_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1088_ = v_x_1075_;
v_isShared_1089_ = v_isSharedCheck_1126_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v_x_1075_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1126_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_pendingProducer_1090_; lean_object* v_pendingConsumer_1091_; lean_object* v_interestWaiter_1092_; uint8_t v_closed_1093_; lean_object* v_knownSize_1094_; lean_object* v_pendingIncompleteChunk_1095_; lean_object* v_closeError_1096_; lean_object* v___x_1097_; lean_object* v___f_1098_; lean_object* v___y_1100_; 
v_pendingProducer_1090_ = lean_ctor_get(v_a_1086_, 0);
lean_inc(v_pendingProducer_1090_);
v_pendingConsumer_1091_ = lean_ctor_get(v_a_1086_, 1);
lean_inc(v_pendingConsumer_1091_);
v_interestWaiter_1092_ = lean_ctor_get(v_a_1086_, 2);
lean_inc(v_interestWaiter_1092_);
v_closed_1093_ = lean_ctor_get_uint8(v_a_1086_, sizeof(void*)*6);
v_knownSize_1094_ = lean_ctor_get(v_a_1086_, 3);
lean_inc(v_knownSize_1094_);
v_pendingIncompleteChunk_1095_ = lean_ctor_get(v_a_1086_, 4);
lean_inc(v_pendingIncompleteChunk_1095_);
v_closeError_1096_ = lean_ctor_get(v_a_1086_, 5);
lean_inc(v_closeError_1096_);
lean_dec(v_a_1086_);
v___x_1097_ = lean_box(v_closed_1093_);
v___f_1098_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed), 9, 6);
lean_closure_set(v___f_1098_, 0, v_pendingProducer_1090_);
lean_closure_set(v___f_1098_, 1, v___x_1097_);
lean_closure_set(v___f_1098_, 2, v_knownSize_1094_);
lean_closure_set(v___f_1098_, 3, v_pendingIncompleteChunk_1095_);
lean_closure_set(v___f_1098_, 4, v_closeError_1096_);
lean_closure_set(v___f_1098_, 5, v_interestWaiter_1092_);
if (lean_obj_tag(v_pendingConsumer_1091_) == 1)
{
lean_object* v_val_1109_; 
v_val_1109_ = lean_ctor_get(v_pendingConsumer_1091_, 0);
lean_inc(v_val_1109_);
if (lean_obj_tag(v_val_1109_) == 1)
{
lean_object* v_finished_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1125_; 
lean_del_object(v___x_1088_);
v_finished_1110_ = lean_ctor_get(v_val_1109_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_val_1109_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1112_ = v_val_1109_;
v_isShared_1113_ = v_isSharedCheck_1125_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_finished_1110_);
lean_dec(v_val_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1125_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_finished_1114_; lean_object* v___x_1115_; lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___x_1119_; 
v_finished_1114_ = lean_ctor_get(v_finished_1110_, 0);
lean_inc(v_finished_1114_);
lean_dec_ref(v_finished_1110_);
v___x_1115_ = lean_st_ref_get(v_finished_1114_);
lean_dec(v_finished_1114_);
lean_inc(v_a_1074_);
v___f_1116_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1116_, 0, v___f_1098_);
lean_closure_set(v___f_1116_, 1, v_a_1074_);
lean_inc_ref(v___f_1116_);
v___f_1117_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1117_, 0, v_pendingConsumer_1091_);
lean_closure_set(v___f_1117_, 1, v___f_1116_);
lean_closure_set(v___f_1117_, 2, v___f_1116_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1115_);
v___x_1119_ = v___x_1112_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1115_);
v___x_1119_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; 
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = 0;
v___x_1123_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1121_, v___x_1122_, v___x_1120_, v___f_1117_);
return v___x_1123_;
}
}
}
else
{
lean_dec(v_val_1109_);
v___y_1100_ = v_a_1074_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v_a_1074_;
goto v___jp_1099_;
}
v___jp_1099_:
{
lean_object* v___f_1101_; lean_object* v___x_1103_; 
lean_inc(v___y_1100_);
v___f_1101_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1101_, 0, v___f_1098_);
lean_closure_set(v___f_1101_, 1, v___y_1100_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v_pendingConsumer_1091_);
v___x_1103_ = v___x_1088_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_pendingConsumer_1091_);
v___x_1103_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = 0;
v___x_1107_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1105_, v___x_1106_, v___x_1104_, v___f_1101_);
return v___x_1107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object* v_a_1127_, lean_object* v_x_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_1127_, v_x_1128_);
lean_dec(v_a_1127_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1133_ = lean_st_ref_get(v_a_1131_);
lean_inc(v_a_1131_);
v___f_1134_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1134_, 0, v_a_1131_);
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = 0;
v___x_1139_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1137_, v___x_1138_, v___x_1136_, v___f_1134_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object* v_a_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_1140_);
lean_dec(v_a_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object* v_mutex_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_io_basemutex_unlock(v_mutex_1143_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(v_mutex_1149_, v_x_1150_);
lean_dec(v_x_1150_);
lean_dec(v_mutex_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object* v_k_1153_, lean_object* v_ref_1154_, lean_object* v_x_1155_){
_start:
{
if (lean_obj_tag(v_x_1155_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_ref_1154_);
lean_dec_ref(v_k_1153_);
v_a_1157_ = lean_ctor_get(v_x_1155_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1155_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1159_ = v_x_1155_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v_x_1155_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
}
else
{
lean_object* v___x_1166_; 
lean_dec_ref_known(v_x_1155_, 1);
v___x_1166_ = lean_apply_2(v_k_1153_, v_ref_1154_, lean_box(0));
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object* v_k_1167_, lean_object* v_ref_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(v_k_1167_, v_ref_1168_, v_x_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object* v_mutex_1172_, lean_object* v___f_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; 
v___x_1175_ = lean_io_basemutex_lock(v_mutex_1172_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = 0;
v___x_1180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1178_, v___x_1179_, v___x_1177_, v___f_1173_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_1181_, lean_object* v___f_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(v_mutex_1181_, v___f_1182_);
lean_dec(v_mutex_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object* v___y_1185_){
_start:
{
if (lean_obj_tag(v___y_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___y_1185_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___y_1185_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___y_1185_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___y_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1202_; 
v_a_1194_ = lean_ctor_get(v___y_1185_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___y_1185_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1196_ = v___y_1185_;
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___y_1185_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_fst_1198_; lean_object* v___x_1200_; 
v_fst_1198_ = lean_ctor_get(v_a_1194_, 0);
lean_inc(v_fst_1198_);
lean_dec(v_a_1194_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v_fst_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_fst_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(lean_object* v_mutex_1204_, lean_object* v_k_1205_){
_start:
{
lean_object* v_ref_1207_; lean_object* v_mutex_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___y_1216_; 
v_ref_1207_ = lean_ctor_get(v_mutex_1204_, 0);
lean_inc(v_ref_1207_);
v_mutex_1208_ = lean_ctor_get(v_mutex_1204_, 1);
lean_inc_n(v_mutex_1208_, 2);
lean_dec_ref(v_mutex_1204_);
v___f_1209_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1209_, 0, v_mutex_1208_);
v___f_1210_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1210_, 0, v_k_1205_);
lean_closure_set(v___f_1210_, 1, v_ref_1207_);
v___f_1211_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1211_, 0, v_mutex_1208_);
lean_closure_set(v___f_1211_, 1, v___f_1210_);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = 0;
v___x_1214_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1211_, v___f_1209_, v___x_1212_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1218_; 
v_a_1218_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1214_, 1);
if (lean_obj_tag(v_a_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
v_a_1219_ = lean_ctor_get(v_a_1218_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v_a_1218_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v_a_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
v___y_1216_ = v___x_1224_;
goto v___jp_1215_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_a_1227_ = lean_ctor_get(v_a_1218_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1229_ = v_a_1218_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v_a_1218_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_fst_1231_; lean_object* v___x_1233_; 
v_fst_1231_ = lean_ctor_get(v_a_1227_, 0);
lean_inc(v_fst_1231_);
lean_dec(v_a_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v_fst_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_fst_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
v___y_1216_ = v___x_1233_;
goto v___jp_1215_;
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1245_; 
v_a_1236_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1238_ = v___x_1214_;
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1214_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___f_1240_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0));
v___x_1241_ = lean_task_map(v___f_1240_, v_a_1236_, v___x_1212_, v___x_1213_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1241_);
v___x_1243_ = v___x_1238_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
v___jp_1215_:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1216_);
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___boxed(lean_object* v_mutex_1246_, lean_object* v_k_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1246_, v_k_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_mutex_1252_, lean_object* v_k_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1252_, v_k_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_00_u03b2_1257_, lean_object* v_mutex_1258_, lean_object* v_k_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(v_00_u03b1_1256_, v_00_u03b2_1257_, v_mutex_1258_, v_k_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0(lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1272_; 
v_a_1264_ = lean_ctor_get(v_x_1262_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_x_1262_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1266_ = v_x_1262_;
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v_x_1262_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v_x_1262_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v_x_1262_, 1);
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_a_1273_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(lean_object* v_x_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_Http_Body_Stream_tryRecv___lam__0(v_x_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object* v_a_1278_, lean_object* v___f_1279_, lean_object* v_x_1280_){
_start:
{
if (lean_obj_tag(v_x_1280_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v___f_1279_);
v_a_1282_ = lean_ctor_get(v_x_1280_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_x_1280_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1284_ = v_x_1280_;
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v_x_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1291_; 
v_a_1291_ = lean_ctor_get(v_x_1280_, 0);
lean_inc(v_a_1291_);
if (lean_obj_tag(v_a_1291_) == 1)
{
lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v___f_1279_);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_a_1291_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v_a_1291_, 0);
lean_dec(v_unused_1300_);
v___x_1293_ = v_a_1291_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v_a_1291_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v_x_1280_);
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_x_1280_);
v___x_1296_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
}
}
else
{
lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_a_1291_);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_x_1280_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_x_1280_, 0);
lean_dec(v_unused_1313_);
v___x_1302_ = v_x_1280_;
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
else
{
lean_dec(v_x_1280_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_st_ref_get(v_a_1278_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1304_);
v___x_1306_ = v___x_1302_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = 0;
v___x_1310_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1308_, v___x_1309_, v___x_1307_, v___f_1279_);
return v___x_1310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object* v_a_1314_, lean_object* v___f_1315_, lean_object* v_x_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_a_1314_, v___f_1315_, v_x_1316_);
lean_dec(v_a_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object* v_x_1323_){
_start:
{
if (lean_obj_tag(v_x_1323_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
v_a_1325_ = lean_ctor_get(v_x_1323_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_x_1323_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1327_ = v_x_1323_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v_x_1323_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1352_; 
v_a_1334_ = lean_ctor_get(v_x_1323_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_x_1323_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1336_ = v_x_1323_;
v_isShared_1337_ = v_isSharedCheck_1352_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v_x_1323_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1352_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_closeError_1338_; 
v_closeError_1338_ = lean_ctor_get(v_a_1334_, 5);
lean_inc(v_closeError_1338_);
lean_dec(v_a_1334_);
if (lean_obj_tag(v_closeError_1338_) == 1)
{
lean_object* v_val_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1350_; 
v_val_1339_ = lean_ctor_get(v_closeError_1338_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_closeError_1338_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1341_ = v_closeError_1338_;
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_val_1339_);
lean_dec(v_closeError_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 0);
lean_ctor_set(v___x_1336_, 0, v_val_1339_);
v___x_1344_ = v___x_1336_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_val_1339_);
v___x_1344_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1346_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1344_);
v___x_1346_ = v___x_1341_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
}
}
else
{
lean_object* v___x_1351_; 
lean_dec(v_closeError_1338_);
lean_del_object(v___x_1336_);
v___x_1351_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__1));
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object* v_x_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_x_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(lean_object* v_done_1356_, lean_object* v___f_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v___f_1357_);
v_a_1360_ = lean_ctor_get(v_x_1358_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1362_ = v_x_1358_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v_x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
}
else
{
uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref_known(v_x_1358_, 1);
v___x_1369_ = 1;
v___x_1370_ = lean_box(v___x_1369_);
v___x_1371_ = lean_io_promise_resolve(v___x_1370_, v_done_1356_);
v___x_1372_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = 0;
v___x_1375_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1373_, v___x_1374_, v___x_1372_, v___f_1357_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed(lean_object* v_done_1376_, lean_object* v___f_1377_, lean_object* v_x_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(v_done_1376_, v___f_1377_, v_x_1378_);
lean_dec(v_done_1376_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(lean_object* v_chunk_1381_, lean_object* v_x_1382_){
_start:
{
if (lean_obj_tag(v_x_1382_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v_chunk_1381_);
v_a_1384_ = lean_ctor_get(v_x_1382_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1386_ = v_x_1382_;
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v_x_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
}
else
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1401_; 
v_isSharedCheck_1401_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1402_);
v___x_1394_ = v_x_1382_;
v_isShared_1395_ = v_isSharedCheck_1401_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v_x_1382_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1401_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_chunk_1381_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed(lean_object* v_chunk_1403_, lean_object* v_x_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(v_chunk_1403_, v_x_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(lean_object* v_a_1409_, lean_object* v_x_1410_){
_start:
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1420_; 
v_a_1412_ = lean_ctor_get(v_x_1410_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1414_ = v_x_1410_;
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v_x_1410_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v_pendingProducer_1422_; 
v_a_1421_ = lean_ctor_get(v_x_1410_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v_x_1410_, 1);
v_pendingProducer_1422_ = lean_ctor_get(v_a_1421_, 0);
if (lean_obj_tag(v_pendingProducer_1422_) == 1)
{
lean_object* v_val_1423_; lean_object* v_pendingConsumer_1424_; lean_object* v_interestWaiter_1425_; uint8_t v_closed_1426_; lean_object* v_knownSize_1427_; lean_object* v_pendingIncompleteChunk_1428_; lean_object* v_closeError_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1447_; 
v_val_1423_ = lean_ctor_get(v_pendingProducer_1422_, 0);
lean_inc(v_val_1423_);
v_pendingConsumer_1424_ = lean_ctor_get(v_a_1421_, 1);
v_interestWaiter_1425_ = lean_ctor_get(v_a_1421_, 2);
v_closed_1426_ = lean_ctor_get_uint8(v_a_1421_, sizeof(void*)*6);
v_knownSize_1427_ = lean_ctor_get(v_a_1421_, 3);
v_pendingIncompleteChunk_1428_ = lean_ctor_get(v_a_1421_, 4);
v_closeError_1429_ = lean_ctor_get(v_a_1421_, 5);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_a_1421_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v_a_1421_, 0);
lean_dec(v_unused_1448_);
v___x_1431_ = v_a_1421_;
v_isShared_1432_ = v_isSharedCheck_1447_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_closeError_1429_);
lean_inc(v_pendingIncompleteChunk_1428_);
lean_inc(v_knownSize_1427_);
lean_inc(v_interestWaiter_1425_);
lean_inc(v_pendingConsumer_1424_);
lean_dec(v_a_1421_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1447_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_chunk_1433_; lean_object* v_done_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v_chunk_1433_ = lean_ctor_get(v_val_1423_, 0);
lean_inc_ref(v_chunk_1433_);
v_done_1434_ = lean_ctor_get(v_val_1423_, 1);
lean_inc(v_done_1434_);
lean_dec(v_val_1423_);
v___x_1435_ = lean_box(0);
v___x_1436_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1427_, v_chunk_1433_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 3, v___x_1436_);
lean_ctor_set(v___x_1431_, 0, v___x_1435_);
v___x_1438_ = v___x_1431_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_pendingConsumer_1424_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_interestWaiter_1425_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_pendingIncompleteChunk_1428_);
lean_ctor_set(v_reuseFailAlloc_1446_, 5, v_closeError_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, sizeof(void*)*6, v_closed_1426_);
v___x_1438_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; lean_object* v___x_1445_; 
v___x_1439_ = lean_st_ref_swap(v_a_1409_, v___x_1438_);
lean_dec(v___x_1439_);
v___f_1440_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1440_, 0, v_chunk_1433_);
v___f_1441_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1441_, 0, v_done_1434_);
lean_closure_set(v___f_1441_, 1, v___f_1440_);
v___x_1442_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = 0;
v___x_1445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1443_, v___x_1444_, v___x_1442_, v___f_1441_);
return v___x_1445_;
}
}
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_a_1421_);
v___x_1449_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1450_, lean_object* v_x_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(v_a_1450_, v_x_1451_);
lean_dec(v_a_1450_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(lean_object* v_a_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; 
v___x_1456_ = lean_st_ref_get(v_a_1454_);
lean_inc(v_a_1454_);
v___f_1457_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1457_, 0, v_a_1454_);
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = 0;
v___x_1462_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1460_, v___x_1461_, v___x_1459_, v___f_1457_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___boxed(lean_object* v_a_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1463_);
lean_dec(v_a_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object* v_a_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v___f_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1469_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1467_);
v___f_1470_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0));
lean_inc(v_a_1467_);
v___f_1471_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1471_, 0, v_a_1467_);
lean_closure_set(v___f_1471_, 1, v___f_1470_);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = 0;
v___x_1474_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1472_, v___x_1473_, v___x_1469_, v___f_1471_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object* v_a_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_1475_);
lean_dec(v_a_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1(lean_object* v___y_1478_, lean_object* v___f_1479_, lean_object* v_x_1480_){
_start:
{
if (lean_obj_tag(v_x_1480_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1490_; 
lean_dec_ref(v___f_1479_);
v_a_1482_ = lean_ctor_get(v_x_1480_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_x_1480_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1484_ = v_x_1480_;
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v_x_1480_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
}
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; 
lean_dec_ref_known(v_x_1480_, 1);
v___x_1491_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1478_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = 0;
v___x_1494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1492_, v___x_1493_, v___x_1491_, v___f_1479_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(lean_object* v___y_1495_, lean_object* v___f_1496_, lean_object* v_x_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_Http_Body_Stream_tryRecv___lam__1(v___y_1495_, v___f_1496_, v_x_1497_);
lean_dec(v___y_1495_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2(lean_object* v___f_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1503_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1501_);
lean_inc(v___y_1501_);
v___f_1504_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecv___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1504_, 0, v___y_1501_);
lean_closure_set(v___f_1504_, 1, v___f_1500_);
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = 0;
v___x_1507_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1505_, v___x_1506_, v___x_1503_, v___f_1504_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2___boxed(lean_object* v___f_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Std_Http_Body_Stream_tryRecv___lam__2(v___f_1508_, v___y_1509_);
lean_dec(v___y_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv(lean_object* v_stream_1515_){
_start:
{
lean_object* v___f_1517_; lean_object* v___x_1518_; 
v___f_1517_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecv___closed__1));
v___x_1518_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1515_, v___f_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___boxed(lean_object* v_stream_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Std_Http_Body_Stream_tryRecv(v_stream_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(lean_object* v_x_1522_){
_start:
{
uint8_t v___y_1525_; 
if (lean_obj_tag(v_x_1522_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1537_; 
v_a_1529_ = lean_ctor_get(v_x_1522_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_x_1522_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1531_ = v_x_1522_;
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v_x_1522_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
return v___x_1535_;
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v_pendingProducer_1539_; 
v_a_1538_ = lean_ctor_get(v_x_1522_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v_x_1522_, 1);
v_pendingProducer_1539_ = lean_ctor_get(v_a_1538_, 0);
if (lean_obj_tag(v_pendingProducer_1539_) == 0)
{
uint8_t v_closed_1540_; 
v_closed_1540_ = lean_ctor_get_uint8(v_a_1538_, sizeof(void*)*6);
lean_dec(v_a_1538_);
v___y_1525_ = v_closed_1540_;
goto v___jp_1524_;
}
else
{
uint8_t v___x_1541_; 
lean_dec(v_a_1538_);
v___x_1541_ = 1;
v___y_1525_ = v___x_1541_;
goto v___jp_1524_;
}
}
v___jp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = lean_box(v___y_1525_);
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed(lean_object* v_x_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(v_x_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1548_ = lean_st_ref_get(v_a_1546_);
v___f_1549_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0));
v___x_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = 0;
v___x_1554_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1552_, v___x_1553_, v___x_1551_, v___f_1549_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___boxed(lean_object* v_a_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v_a_1555_);
lean_dec(v_a_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0(lean_object* v_x_1558_){
_start:
{
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1568_; 
v_a_1560_ = lean_ctor_get(v_x_1558_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_x_1558_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1562_ = v_x_1558_;
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v_x_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1569_; 
v_a_1569_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v_x_1558_, 1);
if (lean_obj_tag(v_a_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
v_a_1570_ = lean_ctor_get(v_a_1569_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_a_1569_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1572_ = v_a_1569_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v_a_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1588_; 
v_a_1579_ = lean_ctor_get(v_a_1569_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_a_1569_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1581_ = v_a_1569_;
v_isShared_1582_ = v_isSharedCheck_1588_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v_a_1569_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1588_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_a_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed(lean_object* v_x_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Std_Http_Body_Stream_tryRecvBody___lam__0(v_x_1589_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1(lean_object* v___y_1596_, lean_object* v___f_1597_, lean_object* v_x_1598_){
_start:
{
if (lean_obj_tag(v_x_1598_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v___f_1597_);
v_a_1600_ = lean_ctor_get(v_x_1598_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_x_1598_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1602_ = v_x_1598_;
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v_x_1598_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
return v___x_1606_;
}
}
}
else
{
lean_object* v_a_1609_; uint8_t v___x_1610_; 
v_a_1609_ = lean_ctor_get(v_x_1598_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v_x_1598_, 1);
v___x_1610_ = lean_unbox(v_a_1609_);
lean_dec(v_a_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_dec_ref(v___f_1597_);
v___x_1611_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1));
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; 
v___x_1612_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1596_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = 0;
v___x_1615_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1613_, v___x_1614_, v___x_1612_, v___f_1597_);
return v___x_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed(lean_object* v___y_1616_, lean_object* v___f_1617_, lean_object* v_x_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1(v___y_1616_, v___f_1617_, v_x_1618_);
lean_dec(v___y_1616_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2(lean_object* v___y_1621_, lean_object* v___f_1622_, lean_object* v_x_1623_){
_start:
{
if (lean_obj_tag(v_x_1623_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v___f_1622_);
v_a_1625_ = lean_ctor_get(v_x_1623_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_x_1623_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v_x_1623_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v_x_1623_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
return v___x_1631_;
}
}
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref_known(v_x_1623_, 1);
v___x_1634_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_1621_);
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = 0;
v___x_1637_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1635_, v___x_1636_, v___x_1634_, v___f_1622_);
return v___x_1637_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed(lean_object* v___y_1638_, lean_object* v___f_1639_, lean_object* v_x_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Std_Http_Body_Stream_tryRecvBody___lam__2(v___y_1638_, v___f_1639_, v_x_1640_);
lean_dec(v___y_1638_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3(lean_object* v___f_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; lean_object* v___f_1647_; lean_object* v___f_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1646_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1644_);
lean_inc_n(v___y_1644_, 2);
v___f_1647_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1647_, 0, v___y_1644_);
lean_closure_set(v___f_1647_, 1, v___f_1643_);
v___f_1648_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1648_, 0, v___y_1644_);
lean_closure_set(v___f_1648_, 1, v___f_1647_);
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = 0;
v___x_1651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1649_, v___x_1650_, v___x_1646_, v___f_1648_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed(lean_object* v___f_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Std_Http_Body_Stream_tryRecvBody___lam__3(v___f_1652_, v___y_1653_);
lean_dec(v___y_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody(lean_object* v_stream_1659_){
_start:
{
lean_object* v___f_1661_; lean_object* v___x_1662_; 
v___f_1661_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_1662_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1659_, v___f_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___boxed(lean_object* v_stream_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v_pendingProducer_1669_; lean_object* v_pendingConsumer_1670_; lean_object* v_interestWaiter_1671_; uint8_t v_closed_1672_; lean_object* v_knownSize_1673_; lean_object* v_pendingIncompleteChunk_1674_; lean_object* v_closeError_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1702_; 
v___x_1668_ = lean_st_ref_get(v_a_1666_);
v_pendingProducer_1669_ = lean_ctor_get(v___x_1668_, 0);
v_pendingConsumer_1670_ = lean_ctor_get(v___x_1668_, 1);
v_interestWaiter_1671_ = lean_ctor_get(v___x_1668_, 2);
v_closed_1672_ = lean_ctor_get_uint8(v___x_1668_, sizeof(void*)*6);
v_knownSize_1673_ = lean_ctor_get(v___x_1668_, 3);
v_pendingIncompleteChunk_1674_ = lean_ctor_get(v___x_1668_, 4);
v_closeError_1675_ = lean_ctor_get(v___x_1668_, 5);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1677_ = v___x_1668_;
v_isShared_1678_ = v_isSharedCheck_1702_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_closeError_1675_);
lean_inc(v_pendingIncompleteChunk_1674_);
lean_inc(v_knownSize_1673_);
lean_inc(v_interestWaiter_1671_);
lean_inc(v_pendingConsumer_1670_);
lean_inc(v_pendingProducer_1669_);
lean_dec(v___x_1668_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1702_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___y_1680_; lean_object* v_interestWaiter_1681_; lean_object* v___y_1682_; lean_object* v_pendingConsumer_1689_; lean_object* v___y_1690_; 
if (lean_obj_tag(v_pendingConsumer_1670_) == 1)
{
lean_object* v_val_1696_; 
v_val_1696_ = lean_ctor_get(v_pendingConsumer_1670_, 0);
if (lean_obj_tag(v_val_1696_) == 1)
{
lean_object* v_finished_1697_; lean_object* v_finished_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_finished_1697_ = lean_ctor_get(v_val_1696_, 0);
v_finished_1698_ = lean_ctor_get(v_finished_1697_, 0);
v___x_1699_ = lean_st_ref_get(v_finished_1698_);
v___x_1700_ = lean_unbox(v___x_1699_);
lean_dec(v___x_1699_);
if (v___x_1700_ == 0)
{
v_pendingConsumer_1689_ = v_pendingConsumer_1670_;
v___y_1690_ = v_a_1666_;
goto v___jp_1688_;
}
else
{
lean_object* v___x_1701_; 
lean_dec_ref_known(v_pendingConsumer_1670_, 1);
v___x_1701_ = lean_box(0);
v_pendingConsumer_1689_ = v___x_1701_;
v___y_1690_ = v_a_1666_;
goto v___jp_1688_;
}
}
else
{
v_pendingConsumer_1689_ = v_pendingConsumer_1670_;
v___y_1690_ = v_a_1666_;
goto v___jp_1688_;
}
}
else
{
v_pendingConsumer_1689_ = v_pendingConsumer_1670_;
v___y_1690_ = v_a_1666_;
goto v___jp_1688_;
}
v___jp_1679_:
{
lean_object* v___x_1684_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 2, v_interestWaiter_1681_);
lean_ctor_set(v___x_1677_, 1, v___y_1680_);
v___x_1684_ = v___x_1677_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_pendingProducer_1669_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___y_1680_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_interestWaiter_1681_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_knownSize_1673_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_pendingIncompleteChunk_1674_);
lean_ctor_set(v_reuseFailAlloc_1687_, 5, v_closeError_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1687_, sizeof(void*)*6, v_closed_1672_);
v___x_1684_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_st_ref_swap(v___y_1682_, v___x_1684_);
lean_dec(v___x_1685_);
v___x_1686_ = lean_box(0);
return v___x_1686_;
}
}
v___jp_1688_:
{
if (lean_obj_tag(v_interestWaiter_1671_) == 0)
{
v___y_1680_ = v_pendingConsumer_1689_;
v_interestWaiter_1681_ = v_interestWaiter_1671_;
v___y_1682_ = v___y_1690_;
goto v___jp_1679_;
}
else
{
lean_object* v_val_1691_; lean_object* v_finished_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v_val_1691_ = lean_ctor_get(v_interestWaiter_1671_, 0);
v_finished_1692_ = lean_ctor_get(v_val_1691_, 0);
v___x_1693_ = lean_st_ref_get(v_finished_1692_);
v___x_1694_ = lean_unbox(v___x_1693_);
lean_dec(v___x_1693_);
if (v___x_1694_ == 0)
{
v___y_1680_ = v_pendingConsumer_1689_;
v_interestWaiter_1681_ = v_interestWaiter_1671_;
v___y_1682_ = v___y_1690_;
goto v___jp_1679_;
}
else
{
lean_object* v___x_1695_; 
lean_dec_ref_known(v_interestWaiter_1671_, 1);
v___x_1695_ = lean_box(0);
v___y_1680_ = v_pendingConsumer_1689_;
v_interestWaiter_1681_ = v___x_1695_;
v___y_1682_ = v___y_1690_;
goto v___jp_1679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object* v_a_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_1703_);
lean_dec(v_a_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1708_; lean_object* v_pendingProducer_1709_; 
v___x_1708_ = lean_st_ref_get(v_a_1706_);
v_pendingProducer_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_pendingProducer_1709_);
if (lean_obj_tag(v_pendingProducer_1709_) == 1)
{
lean_object* v_val_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1739_; 
v_val_1710_ = lean_ctor_get(v_pendingProducer_1709_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_pendingProducer_1709_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1712_ = v_pendingProducer_1709_;
v_isShared_1713_ = v_isSharedCheck_1739_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_val_1710_);
lean_dec(v_pendingProducer_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1739_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_pendingConsumer_1714_; lean_object* v_interestWaiter_1715_; uint8_t v_closed_1716_; lean_object* v_knownSize_1717_; lean_object* v_pendingIncompleteChunk_1718_; lean_object* v_closeError_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1737_; 
v_pendingConsumer_1714_ = lean_ctor_get(v___x_1708_, 1);
v_interestWaiter_1715_ = lean_ctor_get(v___x_1708_, 2);
v_closed_1716_ = lean_ctor_get_uint8(v___x_1708_, sizeof(void*)*6);
v_knownSize_1717_ = lean_ctor_get(v___x_1708_, 3);
v_pendingIncompleteChunk_1718_ = lean_ctor_get(v___x_1708_, 4);
v_closeError_1719_ = lean_ctor_get(v___x_1708_, 5);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v___x_1708_, 0);
lean_dec(v_unused_1738_);
v___x_1721_ = v___x_1708_;
v_isShared_1722_ = v_isSharedCheck_1737_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_closeError_1719_);
lean_inc(v_pendingIncompleteChunk_1718_);
lean_inc(v_knownSize_1717_);
lean_inc(v_interestWaiter_1715_);
lean_inc(v_pendingConsumer_1714_);
lean_dec(v___x_1708_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1737_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_chunk_1723_; lean_object* v_done_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v_chunk_1723_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_chunk_1723_);
v_done_1724_ = lean_ctor_get(v_val_1710_, 1);
lean_inc(v_done_1724_);
lean_dec(v_val_1710_);
v___x_1725_ = lean_box(0);
v___x_1726_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1717_, v_chunk_1723_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 3, v___x_1726_);
lean_ctor_set(v___x_1721_, 0, v___x_1725_);
v___x_1728_ = v___x_1721_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_pendingConsumer_1714_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_interestWaiter_1715_);
lean_ctor_set(v_reuseFailAlloc_1736_, 3, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1736_, 4, v_pendingIncompleteChunk_1718_);
lean_ctor_set(v_reuseFailAlloc_1736_, 5, v_closeError_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*6, v_closed_1716_);
v___x_1728_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1729_ = lean_st_ref_swap(v_a_1706_, v___x_1728_);
lean_dec(v___x_1729_);
v___x_1730_ = 1;
v___x_1731_ = lean_box(v___x_1730_);
v___x_1732_ = lean_io_promise_resolve(v___x_1731_, v_done_1724_);
lean_dec(v_done_1724_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v_chunk_1723_);
v___x_1734_ = v___x_1712_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_chunk_1723_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
else
{
lean_object* v___x_1740_; 
lean_dec(v_pendingProducer_1709_);
lean_dec(v___x_1708_);
v___x_1740_ = lean_box(0);
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object* v_a_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_1741_);
lean_dec(v_a_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; lean_object* v_interestWaiter_1747_; 
v___x_1746_ = lean_st_ref_get(v_a_1744_);
v_interestWaiter_1747_ = lean_ctor_get(v___x_1746_, 2);
lean_inc(v_interestWaiter_1747_);
if (lean_obj_tag(v_interestWaiter_1747_) == 1)
{
lean_object* v_pendingProducer_1748_; lean_object* v_pendingConsumer_1749_; uint8_t v_closed_1750_; lean_object* v_knownSize_1751_; lean_object* v_pendingIncompleteChunk_1752_; lean_object* v_closeError_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1766_; 
v_pendingProducer_1748_ = lean_ctor_get(v___x_1746_, 0);
v_pendingConsumer_1749_ = lean_ctor_get(v___x_1746_, 1);
v_closed_1750_ = lean_ctor_get_uint8(v___x_1746_, sizeof(void*)*6);
v_knownSize_1751_ = lean_ctor_get(v___x_1746_, 3);
v_pendingIncompleteChunk_1752_ = lean_ctor_get(v___x_1746_, 4);
v_closeError_1753_ = lean_ctor_get(v___x_1746_, 5);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v___x_1746_, 2);
lean_dec(v_unused_1767_);
v___x_1755_ = v___x_1746_;
v_isShared_1756_ = v_isSharedCheck_1766_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_closeError_1753_);
lean_inc(v_pendingIncompleteChunk_1752_);
lean_inc(v_knownSize_1751_);
lean_inc(v_pendingConsumer_1749_);
lean_inc(v_pendingProducer_1748_);
lean_dec(v___x_1746_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1766_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v_val_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v_val_1757_ = lean_ctor_get(v_interestWaiter_1747_, 0);
lean_inc(v_val_1757_);
lean_dec_ref_known(v_interestWaiter_1747_, 1);
v___x_1758_ = 1;
v___x_1759_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1757_, v___x_1758_);
lean_dec(v_val_1757_);
v___x_1760_ = lean_box(0);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 2, v___x_1760_);
v___x_1762_ = v___x_1755_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_pendingProducer_1748_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_pendingConsumer_1749_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_knownSize_1751_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_pendingIncompleteChunk_1752_);
lean_ctor_set(v_reuseFailAlloc_1765_, 5, v_closeError_1753_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, sizeof(void*)*6, v_closed_1750_);
v___x_1762_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_st_ref_swap(v_a_1744_, v___x_1762_);
lean_dec(v___x_1763_);
v___x_1764_ = lean_box(0);
return v___x_1764_;
}
}
}
else
{
lean_object* v___x_1768_; 
lean_dec(v_interestWaiter_1747_);
lean_dec(v___x_1746_);
v___x_1768_ = lean_box(0);
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object* v_a_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_1769_);
lean_dec(v_a_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object* v_mutex_1772_, lean_object* v_k_1773_){
_start:
{
lean_object* v_ref_1775_; lean_object* v_mutex_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_ref_1775_ = lean_ctor_get(v_mutex_1772_, 0);
lean_inc(v_ref_1775_);
v_mutex_1776_ = lean_ctor_get(v_mutex_1772_, 1);
lean_inc(v_mutex_1776_);
lean_dec_ref(v_mutex_1772_);
v___x_1777_ = lean_io_basemutex_lock(v_mutex_1776_);
v___x_1778_ = lean_apply_2(v_k_1773_, v_ref_1775_, lean_box(0));
v___x_1779_ = lean_io_basemutex_unlock(v_mutex_1776_);
lean_dec(v_mutex_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object* v_mutex_1780_, lean_object* v_k_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1780_, v_k_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object* v_00_u03b1_1784_, lean_object* v_00_u03b2_1785_, lean_object* v_mutex_1786_, lean_object* v_k_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1786_, v_k_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_00_u03b2_1791_, lean_object* v_mutex_1792_, lean_object* v_k_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(v_00_u03b1_1790_, v_00_u03b2_1791_, v_mutex_1792_, v_k_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object* v_x_1801_){
_start:
{
if (lean_obj_tag(v_x_1801_) == 0)
{
lean_object* v___x_1802_; 
v___x_1802_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2));
return v___x_1802_;
}
else
{
lean_object* v_val_1803_; 
v_val_1803_ = lean_ctor_get(v_x_1801_, 0);
lean_inc(v_val_1803_);
return v_val_1803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___boxed(lean_object* v_x_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(v_x_1804_);
lean_dec(v_x_1804_);
return v_res_1805_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2));
v___x_1812_ = lean_task_pure(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_1814_ = lean_task_pure(v___x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object* v___f_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v_closed_1820_; 
v___x_1818_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_1816_);
v___x_1819_ = lean_st_ref_get(v___y_1816_);
v_closed_1820_ = lean_ctor_get_uint8(v___x_1819_, sizeof(void*)*6);
if (v_closed_1820_ == 0)
{
lean_object* v___x_1821_; 
lean_dec(v___x_1819_);
v___x_1821_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_1816_);
if (lean_obj_tag(v___x_1821_) == 1)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v___f_1815_);
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
v___x_1823_ = lean_task_pure(v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; lean_object* v_pendingConsumer_1825_; 
lean_dec(v___x_1821_);
v___x_1824_ = lean_st_ref_get(v___y_1816_);
v_pendingConsumer_1825_ = lean_ctor_get(v___x_1824_, 1);
lean_inc(v_pendingConsumer_1825_);
if (lean_obj_tag(v_pendingConsumer_1825_) == 0)
{
lean_object* v_pendingProducer_1826_; lean_object* v_interestWaiter_1827_; uint8_t v_closed_1828_; lean_object* v_knownSize_1829_; lean_object* v_pendingIncompleteChunk_1830_; lean_object* v_closeError_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1847_; 
v_pendingProducer_1826_ = lean_ctor_get(v___x_1824_, 0);
v_interestWaiter_1827_ = lean_ctor_get(v___x_1824_, 2);
v_closed_1828_ = lean_ctor_get_uint8(v___x_1824_, sizeof(void*)*6);
v_knownSize_1829_ = lean_ctor_get(v___x_1824_, 3);
v_pendingIncompleteChunk_1830_ = lean_ctor_get(v___x_1824_, 4);
v_closeError_1831_ = lean_ctor_get(v___x_1824_, 5);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v___x_1824_, 1);
lean_dec(v_unused_1848_);
v___x_1833_ = v___x_1824_;
v_isShared_1834_ = v_isSharedCheck_1847_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_closeError_1831_);
lean_inc(v_pendingIncompleteChunk_1830_);
lean_inc(v_knownSize_1829_);
lean_inc(v_interestWaiter_1827_);
lean_inc(v_pendingProducer_1826_);
lean_dec(v___x_1824_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1847_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1835_ = lean_io_promise_new();
lean_inc(v___x_1835_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1837_);
v___x_1839_ = v___x_1833_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_pendingProducer_1826_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_interestWaiter_1827_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_knownSize_1829_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_pendingIncompleteChunk_1830_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v_closeError_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1846_, sizeof(void*)*6, v_closed_1828_);
v___x_1839_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1840_ = lean_st_ref_swap(v___y_1816_, v___x_1839_);
lean_dec(v___x_1840_);
v___x_1841_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_1816_);
v___x_1842_ = 1;
v___x_1843_ = lean_io_promise_result_opt(v___x_1835_);
lean_dec(v___x_1835_);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_task_map(v___f_1815_, v___x_1843_, v___x_1844_, v___x_1842_);
return v___x_1845_;
}
}
}
else
{
lean_object* v___x_1849_; 
lean_dec_ref_known(v_pendingConsumer_1825_, 1);
lean_dec(v___x_1824_);
lean_dec_ref(v___f_1815_);
v___x_1849_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3);
return v___x_1849_;
}
}
}
else
{
lean_object* v_closeError_1850_; 
lean_dec_ref(v___f_1815_);
v_closeError_1850_ = lean_ctor_get(v___x_1819_, 5);
lean_inc(v_closeError_1850_);
lean_dec(v___x_1819_);
if (lean_obj_tag(v_closeError_1850_) == 0)
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4);
return v___x_1851_;
}
else
{
lean_object* v_val_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1860_; 
v_val_1852_ = lean_ctor_get(v_closeError_1850_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_closeError_1850_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1854_ = v_closeError_1850_;
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_val_1852_);
lean_dec(v_closeError_1850_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set_tag(v___x_1854_, 0);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_val_1852_);
v___x_1857_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_task_pure(v___x_1857_);
return v___x_1858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object* v___f_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(v___f_1861_, v___y_1862_);
lean_dec(v___y_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object* v_stream_1868_){
_start:
{
lean_object* v___f_1870_; lean_object* v___x_1871_; 
v___f_1870_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1));
v___x_1871_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_1868_, v___f_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object* v_stream_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object* v_x_1875_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1885_; 
v_a_1877_ = lean_ctor_get(v_x_1875_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1879_ = v_x_1875_;
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v_x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v_x_1875_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v_x_1875_, 1);
v___x_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_a_1886_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object* v_x_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv(lean_object* v_stream_1892_){
_start:
{
lean_object* v___x_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1894_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1892_);
v___f_1895_ = ((lean_object*)(l_Std_Http_Body_Stream_recv___closed__0));
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = 0;
v___x_1900_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1898_, v___x_1899_, v___x_1897_, v___f_1895_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object* v_stream_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Std_Http_Body_Stream_recv(v_stream_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(uint8_t v___x_1904_, lean_object* v_knownSize_1905_, lean_object* v_closeError_1906_, lean_object* v_____r_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
lean_ctor_set(v___x_1911_, 2, v___x_1910_);
lean_ctor_set(v___x_1911_, 3, v_knownSize_1905_);
lean_ctor_set(v___x_1911_, 4, v___x_1910_);
lean_ctor_set(v___x_1911_, 5, v_closeError_1906_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*6, v___x_1904_);
v___x_1912_ = lean_st_ref_swap(v___y_1908_, v___x_1911_);
lean_dec(v___x_1912_);
v___x_1913_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(lean_object* v___x_1914_, lean_object* v_knownSize_1915_, lean_object* v_closeError_1916_, lean_object* v_____r_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
uint8_t v___x_2197__boxed_1920_; lean_object* v_res_1921_; 
v___x_2197__boxed_1920_ = lean_unbox(v___x_1914_);
v_res_1921_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(v___x_2197__boxed_1920_, v_knownSize_1915_, v_closeError_1916_, v_____r_1917_, v___y_1918_);
lean_dec(v___y_1918_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(lean_object* v___f_1922_, lean_object* v___y_1923_, lean_object* v_x_1924_){
_start:
{
if (lean_obj_tag(v_x_1924_) == 0)
{
lean_object* v___x_1926_; 
lean_dec_ref(v___f_1922_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_x_1924_);
return v___x_1926_;
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v_x_1924_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v_x_1924_, 1);
lean_inc(v___y_1923_);
v___x_1928_ = lean_apply_3(v___f_1922_, v_a_1927_, v___y_1923_, lean_box(0));
return v___x_1928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed(lean_object* v___f_1929_, lean_object* v___y_1930_, lean_object* v_x_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(v___f_1929_, v___y_1930_, v_x_1931_);
lean_dec(v___y_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object* v_pendingProducer_1934_, uint8_t v_closed_1935_, lean_object* v___f_1936_, lean_object* v_____r_1937_, lean_object* v___y_1938_){
_start:
{
if (lean_obj_tag(v_pendingProducer_1934_) == 1)
{
lean_object* v_val_1940_; lean_object* v_done_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___f_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_val_1940_ = lean_ctor_get(v_pendingProducer_1934_, 0);
v_done_1941_ = lean_ctor_get(v_val_1940_, 1);
v___x_1942_ = lean_box(v_closed_1935_);
v___x_1943_ = lean_io_promise_resolve(v___x_1942_, v_done_1941_);
lean_inc(v___y_1938_);
v___f_1944_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1944_, 0, v___f_1936_);
lean_closure_set(v___f_1944_, 1, v___y_1938_);
v___x_1945_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1946_, v_closed_1935_, v___x_1945_, v___f_1944_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_box(0);
lean_inc(v___y_1938_);
v___x_1949_ = lean_apply_3(v___f_1936_, v___x_1948_, v___y_1938_, lean_box(0));
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object* v_pendingProducer_1950_, lean_object* v_closed_1951_, lean_object* v___f_1952_, lean_object* v_____r_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
uint8_t v_closed_boxed_1956_; lean_object* v_res_1957_; 
v_closed_boxed_1956_ = lean_unbox(v_closed_1951_);
v_res_1957_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(v_pendingProducer_1950_, v_closed_boxed_1956_, v___f_1952_, v_____r_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec(v_pendingProducer_1950_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object* v_interestWaiter_1958_, uint8_t v_closed_1959_, lean_object* v___f_1960_, lean_object* v_____r_1961_, lean_object* v___y_1962_){
_start:
{
if (lean_obj_tag(v_interestWaiter_1958_) == 1)
{
lean_object* v_val_1964_; uint8_t v___x_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_val_1964_ = lean_ctor_get(v_interestWaiter_1958_, 0);
v___x_1965_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1964_, v_closed_1959_);
lean_inc(v___y_1962_);
v___f_1966_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1966_, 0, v___f_1960_);
lean_closure_set(v___f_1966_, 1, v___y_1962_);
v___x_1967_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1968_, v_closed_1959_, v___x_1967_, v___f_1966_);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_box(0);
lean_inc(v___y_1962_);
v___x_1971_ = lean_apply_3(v___f_1960_, v___x_1970_, v___y_1962_, lean_box(0));
return v___x_1971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(lean_object* v_interestWaiter_1972_, lean_object* v_closed_1973_, lean_object* v___f_1974_, lean_object* v_____r_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v_closed_boxed_1978_; lean_object* v_res_1979_; 
v_closed_boxed_1978_ = lean_unbox(v_closed_1973_);
v_res_1979_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_1972_, v_closed_boxed_1978_, v___f_1974_, v_____r_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec(v_interestWaiter_1972_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(lean_object* v___f_1980_, lean_object* v_a_1981_, lean_object* v_x_1982_){
_start:
{
if (lean_obj_tag(v_x_1982_) == 0)
{
lean_object* v___x_1984_; 
lean_dec_ref(v___f_1980_);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_x_1982_);
return v___x_1984_;
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1986_; 
v_a_1985_ = lean_ctor_get(v_x_1982_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v_x_1982_, 1);
lean_inc(v_a_1981_);
v___x_1986_ = lean_apply_3(v___f_1980_, v_a_1985_, v_a_1981_, lean_box(0));
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed(lean_object* v___f_1987_, lean_object* v_a_1988_, lean_object* v_x_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(v___f_1987_, v_a_1988_, v_x_1989_);
lean_dec(v_a_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(lean_object* v_a_1992_, lean_object* v_x_1993_){
_start:
{
if (lean_obj_tag(v_x_1993_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2003_; 
v_a_1995_ = lean_ctor_get(v_x_1993_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_x_1993_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1997_ = v_x_1993_;
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v_x_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2037_; 
v_a_2004_ = lean_ctor_get(v_x_1993_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_x_1993_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2006_ = v_x_1993_;
v_isShared_2007_ = v_isSharedCheck_2037_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v_x_1993_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2037_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
uint8_t v_closed_2008_; 
v_closed_2008_ = lean_ctor_get_uint8(v_a_2004_, sizeof(void*)*6);
if (v_closed_2008_ == 0)
{
lean_object* v_pendingProducer_2009_; lean_object* v_pendingConsumer_2010_; lean_object* v_interestWaiter_2011_; lean_object* v_knownSize_2012_; lean_object* v_closeError_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___x_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___f_2020_; 
v_pendingProducer_2009_ = lean_ctor_get(v_a_2004_, 0);
lean_inc(v_pendingProducer_2009_);
v_pendingConsumer_2010_ = lean_ctor_get(v_a_2004_, 1);
lean_inc(v_pendingConsumer_2010_);
v_interestWaiter_2011_ = lean_ctor_get(v_a_2004_, 2);
lean_inc_n(v_interestWaiter_2011_, 2);
v_knownSize_2012_ = lean_ctor_get(v_a_2004_, 3);
lean_inc(v_knownSize_2012_);
v_closeError_2013_ = lean_ctor_get(v_a_2004_, 5);
lean_inc_n(v_closeError_2013_, 2);
lean_dec(v_a_2004_);
v___x_2014_ = 1;
v___x_2015_ = lean_box(v___x_2014_);
v___f_2016_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2016_, 0, v___x_2015_);
lean_closure_set(v___f_2016_, 1, v_knownSize_2012_);
lean_closure_set(v___f_2016_, 2, v_closeError_2013_);
v___x_2017_ = lean_box(v_closed_2008_);
v___f_2018_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2018_, 0, v_pendingProducer_2009_);
lean_closure_set(v___f_2018_, 1, v___x_2017_);
lean_closure_set(v___f_2018_, 2, v___f_2016_);
v___x_2019_ = lean_box(v_closed_2008_);
lean_inc_ref(v___f_2018_);
v___f_2020_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2020_, 0, v_interestWaiter_2011_);
lean_closure_set(v___f_2020_, 1, v___x_2019_);
lean_closure_set(v___f_2020_, 2, v___f_2018_);
if (lean_obj_tag(v_pendingConsumer_2010_) == 1)
{
lean_object* v_val_2021_; lean_object* v___f_2022_; lean_object* v___y_2024_; 
lean_dec_ref(v___f_2018_);
lean_dec(v_interestWaiter_2011_);
v_val_2021_ = lean_ctor_get(v_pendingConsumer_2010_, 0);
lean_inc(v_val_2021_);
lean_dec_ref_known(v_pendingConsumer_2010_, 1);
lean_inc(v_a_1992_);
v___f_2022_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2022_, 0, v___f_2020_);
lean_closure_set(v___f_2022_, 1, v_a_1992_);
if (lean_obj_tag(v_closeError_2013_) == 0)
{
lean_object* v___x_2029_; 
lean_del_object(v___x_2006_);
v___x_2029_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___y_2024_ = v___x_2029_;
goto v___jp_2023_;
}
else
{
lean_object* v_val_2030_; lean_object* v___x_2032_; 
v_val_2030_ = lean_ctor_get(v_closeError_2013_, 0);
lean_inc(v_val_2030_);
lean_dec_ref_known(v_closeError_2013_, 1);
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 0);
lean_ctor_set(v___x_2006_, 0, v_val_2030_);
v___x_2032_ = v___x_2006_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_val_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
v___y_2024_ = v___x_2032_;
goto v___jp_2023_;
}
}
v___jp_2023_:
{
uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2025_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_2021_, v___y_2024_);
lean_dec(v_val_2021_);
v___x_2026_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2027_ = lean_unsigned_to_nat(0u);
v___x_2028_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2027_, v_closed_2008_, v___x_2026_, v___f_2022_);
return v___x_2028_;
}
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec_ref(v___f_2020_);
lean_dec(v_closeError_2013_);
lean_dec(v_pendingConsumer_2010_);
lean_del_object(v___x_2006_);
v___x_2034_ = lean_box(0);
v___x_2035_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_2011_, v_closed_2008_, v___f_2018_, v___x_2034_, v_a_1992_);
lean_dec(v_interestWaiter_2011_);
return v___x_2035_;
}
}
else
{
lean_object* v___x_2036_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
v___x_2036_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed(lean_object* v_a_2038_, lean_object* v_x_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(v_a_2038_, v_x_2039_);
lean_dec(v_a_2038_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(lean_object* v_a_2042_){
_start:
{
lean_object* v___x_2044_; lean_object* v___f_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; 
v___x_2044_ = lean_st_ref_get(v_a_2042_);
lean_inc(v_a_2042_);
v___f_2045_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed), 3, 1);
lean_closure_set(v___f_2045_, 0, v_a_2042_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = 0;
v___x_2050_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2048_, v___x_2049_, v___x_2047_, v___f_2045_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed(lean_object* v_a_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v_a_2051_);
lean_dec(v_a_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close(lean_object* v_stream_2055_){
_start:
{
lean_object* v___f_2057_; lean_object* v___x_2058_; 
v___f_2057_ = ((lean_object*)(l_Std_Http_Body_Stream_close___closed__0));
v___x_2058_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2055_, v___f_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object* v_stream_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Std_Http_Body_Stream_close(v_stream_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(uint8_t v___x_2062_, lean_object* v_x_2063_){
_start:
{
if (lean_obj_tag(v_x_2063_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2073_; 
v_a_2065_ = lean_ctor_get(v_x_2063_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_x_2063_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2067_ = v_x_2063_;
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v_x_2063_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
}
else
{
lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2082_; 
v_isSharedCheck_2082_ = !lean_is_exclusive(v_x_2063_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v_x_2063_, 0);
lean_dec(v_unused_2083_);
v___x_2075_ = v_x_2063_;
v_isShared_2076_ = v_isSharedCheck_2082_;
goto v_resetjp_2074_;
}
else
{
lean_dec(v_x_2063_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2082_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = lean_box(v___x_2062_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2077_);
v___x_2079_ = v___x_2075_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0___boxed(lean_object* v___x_2084_, lean_object* v_x_2085_, lean_object* v___y_2086_){
_start:
{
uint8_t v___x_1490__boxed_2087_; lean_object* v_res_2088_; 
v___x_1490__boxed_2087_ = lean_unbox(v___x_2084_);
v_res_2088_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(v___x_1490__boxed_2087_, v_x_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(lean_object* v___y_2092_, lean_object* v_x_2093_){
_start:
{
uint8_t v___y_2096_; 
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2108_; 
v_a_2100_ = lean_ctor_get(v_x_2093_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2102_ = v_x_2093_;
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v_x_2093_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
}
}
else
{
lean_object* v_a_2109_; uint8_t v_closed_2110_; 
v_a_2109_ = lean_ctor_get(v_x_2093_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v_x_2093_, 1);
v_closed_2110_ = lean_ctor_get_uint8(v_a_2109_, sizeof(void*)*6);
if (v_closed_2110_ == 0)
{
lean_object* v_pendingConsumer_2111_; 
v_pendingConsumer_2111_ = lean_ctor_get(v_a_2109_, 1);
lean_inc(v_pendingConsumer_2111_);
lean_dec(v_a_2109_);
if (lean_obj_tag(v_pendingConsumer_2111_) == 0)
{
lean_object* v___x_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2112_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v___y_2092_);
v___f_2113_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0));
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2114_, v_closed_2110_, v___x_2112_, v___f_2113_);
return v___x_2115_;
}
else
{
lean_dec_ref_known(v_pendingConsumer_2111_, 1);
v___y_2096_ = v_closed_2110_;
goto v___jp_2095_;
}
}
else
{
uint8_t v___x_2116_; 
lean_dec(v_a_2109_);
v___x_2116_ = 0;
v___y_2096_ = v___x_2116_;
goto v___jp_2095_;
}
}
v___jp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = lean_box(v___y_2096_);
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed(lean_object* v___y_2117_, lean_object* v_x_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(v___y_2117_, v_x_2118_);
lean_dec(v___y_2117_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(lean_object* v___y_2121_, lean_object* v___f_2122_, lean_object* v_x_2123_){
_start:
{
if (lean_obj_tag(v_x_2123_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v___f_2122_);
v_a_2125_ = lean_ctor_get(v_x_2123_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_x_2123_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2127_ = v_x_2123_;
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v_x_2123_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
}
else
{
lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2145_; 
v_isSharedCheck_2145_ = !lean_is_exclusive(v_x_2123_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_x_2123_, 0);
lean_dec(v_unused_2146_);
v___x_2135_ = v_x_2123_;
v_isShared_2136_ = v_isSharedCheck_2145_;
goto v_resetjp_2134_;
}
else
{
lean_dec(v_x_2123_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2145_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = lean_st_ref_get(v___y_2121_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2137_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; 
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = 0;
v___x_2143_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2141_, v___x_2142_, v___x_2140_, v___f_2122_);
return v___x_2143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed(lean_object* v___y_2147_, lean_object* v___f_2148_, lean_object* v_x_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(v___y_2147_, v___f_2148_, v_x_2149_);
lean_dec(v___y_2147_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2154_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2152_);
lean_inc_n(v___y_2152_, 2);
v___f_2155_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2155_, 0, v___y_2152_);
v___f_2156_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2156_, 0, v___y_2152_);
lean_closure_set(v___f_2156_, 1, v___f_2155_);
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = 0;
v___x_2159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2157_, v___x_2158_, v___x_2154_, v___f_2156_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3___boxed(lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(v___y_2160_);
lean_dec(v___y_2160_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned(lean_object* v_stream_2164_){
_start:
{
lean_object* v___f_2166_; lean_object* v___x_2167_; 
v___f_2166_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___closed__0));
v___x_2167_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2164_, v___f_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___boxed(lean_object* v_stream_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Std_Http_Body_Stream_closeIfAbandoned(v_stream_2168_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0(lean_object* v___y_2171_, lean_object* v_x_2172_){
_start:
{
if (lean_obj_tag(v_x_2172_) == 0)
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_x_2172_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; 
lean_dec_ref_known(v_x_2172_, 1);
v___x_2175_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v___y_2171_);
return v___x_2175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0___boxed(lean_object* v___y_2176_, lean_object* v_x_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Std_Http_Body_Stream_closeWithError___lam__0(v___y_2176_, v_x_2177_);
lean_dec(v___y_2176_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1(lean_object* v_err_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v_pendingProducer_2184_; lean_object* v_pendingConsumer_2185_; lean_object* v_interestWaiter_2186_; uint8_t v_closed_2187_; lean_object* v_knownSize_2188_; lean_object* v_pendingIncompleteChunk_2189_; lean_object* v_closeError_2190_; lean_object* v___f_2191_; lean_object* v_fst_2193_; lean_object* v_snd_2194_; lean_object* v___x_2201_; 
v___x_2183_ = lean_st_ref_take(v___y_2181_);
v_pendingProducer_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_pendingProducer_2184_);
v_pendingConsumer_2185_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_pendingConsumer_2185_);
v_interestWaiter_2186_ = lean_ctor_get(v___x_2183_, 2);
lean_inc(v_interestWaiter_2186_);
v_closed_2187_ = lean_ctor_get_uint8(v___x_2183_, sizeof(void*)*6);
v_knownSize_2188_ = lean_ctor_get(v___x_2183_, 3);
lean_inc(v_knownSize_2188_);
v_pendingIncompleteChunk_2189_ = lean_ctor_get(v___x_2183_, 4);
lean_inc(v_pendingIncompleteChunk_2189_);
v_closeError_2190_ = lean_ctor_get(v___x_2183_, 5);
lean_inc(v_closeError_2190_);
lean_inc(v___y_2181_);
v___f_2191_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2191_, 0, v___y_2181_);
v___x_2201_ = lean_box(0);
if (lean_obj_tag(v_closeError_2190_) == 0)
{
lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2210_ = lean_ctor_get(v___x_2183_, 5);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v___x_2183_, 4);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v___x_2183_, 3);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v___x_2183_, 2);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v___x_2183_, 1);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v___x_2183_, 0);
lean_dec(v_unused_2215_);
v___x_2203_ = v___x_2183_;
v_isShared_2204_ = v_isSharedCheck_2209_;
goto v_resetjp_2202_;
}
else
{
lean_dec(v___x_2183_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2209_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2205_, 0, v_err_2180_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 5, v___x_2205_);
v___x_2207_ = v___x_2203_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_pendingProducer_2184_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_pendingConsumer_2185_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_interestWaiter_2186_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_knownSize_2188_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_pendingIncompleteChunk_2189_);
lean_ctor_set(v_reuseFailAlloc_2208_, 5, v___x_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2208_, sizeof(void*)*6, v_closed_2187_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
v_fst_2193_ = v___x_2201_;
v_snd_2194_ = v___x_2207_;
goto v___jp_2192_;
}
}
}
else
{
lean_dec_ref_known(v_closeError_2190_, 1);
lean_dec(v_pendingIncompleteChunk_2189_);
lean_dec(v_knownSize_2188_);
lean_dec(v_interestWaiter_2186_);
lean_dec(v_pendingConsumer_2185_);
lean_dec(v_pendingProducer_2184_);
lean_dec(v_err_2180_);
v_fst_2193_ = v___x_2201_;
v_snd_2194_ = v___x_2183_;
goto v___jp_2192_;
}
v___jp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; 
v___x_2195_ = lean_st_ref_put(v___y_2181_, v_snd_2194_);
v___x_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2196_, 0, v_fst_2193_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = 0;
v___x_2200_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2198_, v___x_2199_, v___x_2197_, v___f_2191_);
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1___boxed(lean_object* v_err_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Std_Http_Body_Stream_closeWithError___lam__1(v_err_2216_, v___y_2217_);
lean_dec(v___y_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError(lean_object* v_stream_2220_, lean_object* v_err_2221_){
_start:
{
lean_object* v___f_2223_; lean_object* v___x_2224_; 
v___f_2223_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2223_, 0, v_err_2221_);
v___x_2224_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2220_, v___f_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___boxed(lean_object* v_stream_2225_, lean_object* v_err_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Std_Http_Body_Stream_closeWithError(v_stream_2225_, v_err_2226_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object* v_____do__lift_2229_, lean_object* v___y_2230_){
_start:
{
uint8_t v_closed_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_closed_2232_ = lean_ctor_get_uint8(v_____do__lift_2229_, sizeof(void*)*6);
v___x_2233_ = lean_box(v_closed_2232_);
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object* v_____do__lift_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v_____do__lift_2236_);
return v_res_2239_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__1(void){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_2241_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__2(void){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_2242_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__6(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___f_2249_; lean_object* v___f_2250_; 
v___x_2248_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2249_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___f_2250_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2250_, 0, v___f_2249_);
lean_closure_set(v___f_2250_, 1, v___x_2248_);
return v___f_2250_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__11(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___f_2260_; lean_object* v___f_2261_; 
v___x_2259_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2260_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__10));
v___f_2261_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2261_, 0, v___f_2260_);
lean_closure_set(v___f_2261_, 1, v___x_2259_);
return v___f_2261_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__12(void){
_start:
{
lean_object* v___f_2262_; lean_object* v___x_2263_; 
v___f_2262_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__11, &l_Std_Http_Body_Stream_isClosed___closed__11_once, _init_l_Std_Http_Body_Stream_isClosed___closed__11);
v___x_2263_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2263_, 0, lean_box(0));
lean_closure_set(v___x_2263_, 1, lean_box(0));
lean_closure_set(v___x_2263_, 2, lean_box(0));
lean_closure_set(v___x_2263_, 3, v___f_2262_);
return v___x_2263_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__13(void){
_start:
{
lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___f_2264_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__0));
v___x_2265_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2266_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2267_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2267_, 0, lean_box(0));
lean_closure_set(v___x_2267_, 1, lean_box(0));
lean_closure_set(v___x_2267_, 2, v___x_2266_);
lean_closure_set(v___x_2267_, 3, lean_box(0));
lean_closure_set(v___x_2267_, 4, lean_box(0));
lean_closure_set(v___x_2267_, 5, v___x_2265_);
lean_closure_set(v___x_2267_, 6, v___f_2264_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed(lean_object* v_stream_2268_){
_start:
{
lean_object* v___x_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v___x_29__overap_2274_; lean_object* v___x_2275_; 
v___x_2270_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2271_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2272_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2273_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__13, &l_Std_Http_Body_Stream_isClosed___closed__13_once, _init_l_Std_Http_Body_Stream_isClosed___closed__13);
v___x_29__overap_2274_ = l_Std_Mutex_atomically___redArg(v___x_2270_, v___f_2271_, v___f_2272_, v_stream_2268_, v___x_2273_);
v___x_2275_ = lean_apply_1(v___x_29__overap_2274_, lean_box(0));
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___boxed(lean_object* v_stream_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Std_Http_Body_Stream_isClosed(v_stream_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0(lean_object* v_____do__lift_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_knownSize_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_knownSize_2282_ = lean_ctor_get(v_____do__lift_2279_, 3);
lean_inc(v_knownSize_2282_);
v___x_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2283_, 0, v_knownSize_2282_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(lean_object* v_____do__lift_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v_____do__lift_2285_);
return v_res_2288_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_getKnownSize___closed__1(void){
_start:
{
lean_object* v___f_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___f_2290_ = ((lean_object*)(l_Std_Http_Body_Stream_getKnownSize___closed__0));
v___x_2291_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2292_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2293_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2293_, 0, lean_box(0));
lean_closure_set(v___x_2293_, 1, lean_box(0));
lean_closure_set(v___x_2293_, 2, v___x_2292_);
lean_closure_set(v___x_2293_, 3, lean_box(0));
lean_closure_set(v___x_2293_, 4, lean_box(0));
lean_closure_set(v___x_2293_, 5, v___x_2291_);
lean_closure_set(v___x_2293_, 6, v___f_2290_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize(lean_object* v_stream_2294_){
_start:
{
lean_object* v___x_2296_; lean_object* v___f_2297_; lean_object* v___f_2298_; lean_object* v___x_2299_; lean_object* v___x_29__overap_2300_; lean_object* v___x_2301_; 
v___x_2296_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2297_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2298_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2299_ = lean_obj_once(&l_Std_Http_Body_Stream_getKnownSize___closed__1, &l_Std_Http_Body_Stream_getKnownSize___closed__1_once, _init_l_Std_Http_Body_Stream_getKnownSize___closed__1);
v___x_29__overap_2300_ = l_Std_Mutex_atomically___redArg(v___x_2296_, v___f_2297_, v___f_2298_, v_stream_2294_, v___x_2299_);
v___x_2301_ = lean_apply_1(v___x_29__overap_2300_, lean_box(0));
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___boxed(lean_object* v_stream_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0(lean_object* v_size_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v_pendingProducer_2309_; lean_object* v_pendingConsumer_2310_; lean_object* v_interestWaiter_2311_; uint8_t v_closed_2312_; lean_object* v_pendingIncompleteChunk_2313_; lean_object* v_closeError_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2323_; 
v___x_2308_ = lean_st_ref_take(v___y_2306_);
v_pendingProducer_2309_ = lean_ctor_get(v___x_2308_, 0);
v_pendingConsumer_2310_ = lean_ctor_get(v___x_2308_, 1);
v_interestWaiter_2311_ = lean_ctor_get(v___x_2308_, 2);
v_closed_2312_ = lean_ctor_get_uint8(v___x_2308_, sizeof(void*)*6);
v_pendingIncompleteChunk_2313_ = lean_ctor_get(v___x_2308_, 4);
v_closeError_2314_ = lean_ctor_get(v___x_2308_, 5);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; 
v_unused_2324_ = lean_ctor_get(v___x_2308_, 3);
lean_dec(v_unused_2324_);
v___x_2316_ = v___x_2308_;
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_closeError_2314_);
lean_inc(v_pendingIncompleteChunk_2313_);
lean_inc(v_interestWaiter_2311_);
lean_inc(v_pendingConsumer_2310_);
lean_inc(v_pendingProducer_2309_);
lean_dec(v___x_2308_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 3, v_size_2305_);
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_pendingProducer_2309_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_pendingConsumer_2310_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_interestWaiter_2311_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_size_2305_);
lean_ctor_set(v_reuseFailAlloc_2322_, 4, v_pendingIncompleteChunk_2313_);
lean_ctor_set(v_reuseFailAlloc_2322_, 5, v_closeError_2314_);
lean_ctor_set_uint8(v_reuseFailAlloc_2322_, sizeof(void*)*6, v_closed_2312_);
v___x_2319_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_st_ref_put(v___y_2306_, v___x_2319_);
v___x_2321_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(lean_object* v_size_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_2325_, v___y_2326_);
lean_dec(v___y_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize(lean_object* v_stream_2329_, lean_object* v_size_2330_){
_start:
{
lean_object* v___f_2332_; lean_object* v___x_2333_; lean_object* v___f_2334_; lean_object* v___f_2335_; lean_object* v___x_26__overap_2336_; lean_object* v___x_2337_; 
v___f_2332_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2332_, 0, v_size_2330_);
v___x_2333_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2334_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2335_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_26__overap_2336_ = l_Std_Mutex_atomically___redArg(v___x_2333_, v___f_2334_, v___f_2335_, v_stream_2329_, v___f_2332_);
v___x_2337_ = lean_apply_1(v___x_26__overap_2336_, lean_box(0));
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___boxed(lean_object* v_stream_2338_, lean_object* v_size_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_2338_, v_size_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object* v_pendingProducer_2342_, lean_object* v_pendingConsumer_2343_, uint8_t v_closed_2344_, lean_object* v_knownSize_2345_, lean_object* v_pendingIncompleteChunk_2346_, lean_object* v_closeError_2347_, lean_object* v_a_2348_, lean_object* v___x_2349_, lean_object* v_x_2350_){
_start:
{
if (lean_obj_tag(v_x_2350_) == 0)
{
lean_object* v___x_2352_; 
lean_dec(v_closeError_2347_);
lean_dec(v_pendingIncompleteChunk_2346_);
lean_dec(v_knownSize_2345_);
lean_dec(v_pendingConsumer_2343_);
lean_dec(v_pendingProducer_2342_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_x_2350_);
return v___x_2352_;
}
else
{
lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2363_; 
v_isSharedCheck_2363_ = !lean_is_exclusive(v_x_2350_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v_x_2350_, 0);
lean_dec(v_unused_2364_);
v___x_2354_ = v_x_2350_;
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v_x_2350_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2356_ = lean_box(0);
v___x_2357_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2357_, 0, v_pendingProducer_2342_);
lean_ctor_set(v___x_2357_, 1, v_pendingConsumer_2343_);
lean_ctor_set(v___x_2357_, 2, v___x_2356_);
lean_ctor_set(v___x_2357_, 3, v_knownSize_2345_);
lean_ctor_set(v___x_2357_, 4, v_pendingIncompleteChunk_2346_);
lean_ctor_set(v___x_2357_, 5, v_closeError_2347_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*6, v_closed_2344_);
v___x_2358_ = lean_st_ref_swap(v_a_2348_, v___x_2357_);
lean_dec(v___x_2358_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2349_);
v___x_2360_ = v___x_2354_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2349_);
v___x_2360_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object* v_pendingProducer_2365_, lean_object* v_pendingConsumer_2366_, lean_object* v_closed_2367_, lean_object* v_knownSize_2368_, lean_object* v_pendingIncompleteChunk_2369_, lean_object* v_closeError_2370_, lean_object* v_a_2371_, lean_object* v___x_2372_, lean_object* v_x_2373_, lean_object* v___y_2374_){
_start:
{
uint8_t v_closed_boxed_2375_; lean_object* v_res_2376_; 
v_closed_boxed_2375_ = lean_unbox(v_closed_2367_);
v_res_2376_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_2365_, v_pendingConsumer_2366_, v_closed_boxed_2375_, v_knownSize_2368_, v_pendingIncompleteChunk_2369_, v_closeError_2370_, v_a_2371_, v___x_2372_, v_x_2373_);
lean_dec(v_a_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object* v_a_2377_, lean_object* v_x_2378_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2388_; 
v_a_2380_ = lean_ctor_get(v_x_2378_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_x_2378_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2382_ = v_x_2378_;
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v_x_2378_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v_interestWaiter_2390_; 
v_a_2389_ = lean_ctor_get(v_x_2378_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v_x_2378_, 1);
v_interestWaiter_2390_ = lean_ctor_get(v_a_2389_, 2);
lean_inc(v_interestWaiter_2390_);
if (lean_obj_tag(v_interestWaiter_2390_) == 1)
{
lean_object* v_pendingProducer_2391_; lean_object* v_pendingConsumer_2392_; uint8_t v_closed_2393_; lean_object* v_knownSize_2394_; lean_object* v_pendingIncompleteChunk_2395_; lean_object* v_closeError_2396_; lean_object* v_val_2397_; uint8_t v___x_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___f_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; 
v_pendingProducer_2391_ = lean_ctor_get(v_a_2389_, 0);
lean_inc(v_pendingProducer_2391_);
v_pendingConsumer_2392_ = lean_ctor_get(v_a_2389_, 1);
lean_inc(v_pendingConsumer_2392_);
v_closed_2393_ = lean_ctor_get_uint8(v_a_2389_, sizeof(void*)*6);
v_knownSize_2394_ = lean_ctor_get(v_a_2389_, 3);
lean_inc(v_knownSize_2394_);
v_pendingIncompleteChunk_2395_ = lean_ctor_get(v_a_2389_, 4);
lean_inc(v_pendingIncompleteChunk_2395_);
v_closeError_2396_ = lean_ctor_get(v_a_2389_, 5);
lean_inc(v_closeError_2396_);
lean_dec(v_a_2389_);
v_val_2397_ = lean_ctor_get(v_interestWaiter_2390_, 0);
lean_inc(v_val_2397_);
lean_dec_ref_known(v_interestWaiter_2390_, 1);
v___x_2398_ = 1;
v___x_2399_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2397_, v___x_2398_);
lean_dec(v_val_2397_);
v___x_2400_ = lean_box(0);
v___x_2401_ = lean_box(v_closed_2393_);
lean_inc(v_a_2377_);
v___f_2402_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed), 10, 8);
lean_closure_set(v___f_2402_, 0, v_pendingProducer_2391_);
lean_closure_set(v___f_2402_, 1, v_pendingConsumer_2392_);
lean_closure_set(v___f_2402_, 2, v___x_2401_);
lean_closure_set(v___f_2402_, 3, v_knownSize_2394_);
lean_closure_set(v___f_2402_, 4, v_pendingIncompleteChunk_2395_);
lean_closure_set(v___f_2402_, 5, v_closeError_2396_);
lean_closure_set(v___f_2402_, 6, v_a_2377_);
lean_closure_set(v___f_2402_, 7, v___x_2400_);
v___x_2403_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = 0;
v___x_2406_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2404_, v___x_2405_, v___x_2403_, v___f_2402_);
return v___x_2406_;
}
else
{
lean_object* v___x_2407_; 
lean_dec(v_interestWaiter_2390_);
lean_dec(v_a_2389_);
v___x_2407_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object* v_a_2408_, lean_object* v_x_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_2408_, v_x_2409_);
lean_dec(v_a_2408_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object* v_a_2412_){
_start:
{
lean_object* v___x_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2414_ = lean_st_ref_get(v_a_2412_);
lean_inc(v_a_2412_);
v___f_2415_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2415_, 0, v_a_2412_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
v___x_2418_ = lean_unsigned_to_nat(0u);
v___x_2419_ = 0;
v___x_2420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2418_, v___x_2419_, v___x_2417_, v___f_2415_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object* v_a_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_2421_);
lean_dec(v_a_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object* v_promise_2424_, lean_object* v_x_2425_){
_start:
{
if (lean_obj_tag(v_x_2425_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2435_; 
v_a_2427_ = lean_ctor_get(v_x_2425_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_x_2425_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2429_ = v_x_2425_;
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v_x_2425_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2445_; 
v_a_2436_ = lean_ctor_get(v_x_2425_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_x_2425_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2438_ = v_x_2425_;
v_isShared_2439_ = v_isSharedCheck_2445_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v_x_2425_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2445_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2440_ = lean_io_promise_resolve(v_a_2436_, v_promise_2424_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2440_);
v___x_2442_ = v___x_2438_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
return v___x_2443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_2446_, lean_object* v_x_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(v_promise_2446_, v_x_2447_);
lean_dec(v_promise_2446_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object* v_lose_2450_, lean_object* v___y_2451_, lean_object* v___f_2452_, lean_object* v_x_2453_){
_start:
{
if (lean_obj_tag(v_x_2453_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v___f_2452_);
lean_dec_ref(v_lose_2450_);
v_a_2455_ = lean_ctor_get(v_x_2453_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_x_2453_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2457_ = v_x_2453_;
v_isShared_2458_ = v_isSharedCheck_2463_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v_x_2453_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2463_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
}
}
else
{
lean_object* v_a_2464_; uint8_t v___x_2465_; 
v_a_2464_ = lean_ctor_get(v_x_2453_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v_x_2453_, 1);
v___x_2465_ = lean_unbox(v_a_2464_);
lean_dec(v_a_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; 
lean_dec_ref(v___f_2452_);
lean_inc(v___y_2451_);
v___x_2466_ = lean_apply_2(v_lose_2450_, v___y_2451_, lean_box(0));
return v___x_2466_;
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; 
lean_dec_ref(v_lose_2450_);
v___x_2467_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2451_);
v___x_2468_ = lean_unsigned_to_nat(0u);
v___x_2469_ = 0;
v___x_2470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2468_, v___x_2469_, v___x_2467_, v___f_2452_);
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object* v_lose_2471_, lean_object* v___y_2472_, lean_object* v___f_2473_, lean_object* v_x_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(v_lose_2471_, v___y_2472_, v___f_2473_, v_x_2474_);
lean_dec(v___y_2472_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object* v_w_2477_, lean_object* v_lose_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_finished_2481_; lean_object* v_promise_2482_; lean_object* v___x_2483_; lean_object* v___f_2484_; lean_object* v___f_2485_; uint8_t v___y_2487_; uint8_t v___x_2497_; 
v_finished_2481_ = lean_ctor_get(v_w_2477_, 0);
lean_inc(v_finished_2481_);
v_promise_2482_ = lean_ctor_get(v_w_2477_, 1);
lean_inc(v_promise_2482_);
lean_dec_ref(v_w_2477_);
v___x_2483_ = lean_st_ref_take(v_finished_2481_);
v___f_2484_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2484_, 0, v_promise_2482_);
lean_inc(v___y_2479_);
v___f_2485_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2485_, 0, v_lose_2478_);
lean_closure_set(v___f_2485_, 1, v___y_2479_);
lean_closure_set(v___f_2485_, 2, v___f_2484_);
v___x_2497_ = lean_unbox(v___x_2483_);
lean_dec(v___x_2483_);
if (v___x_2497_ == 0)
{
uint8_t v___x_2498_; 
v___x_2498_ = 1;
v___y_2487_ = v___x_2498_;
goto v___jp_2486_;
}
else
{
uint8_t v___x_2499_; 
v___x_2499_ = 0;
v___y_2487_ = v___x_2499_;
goto v___jp_2486_;
}
v___jp_2486_:
{
uint8_t v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; 
v___x_2488_ = 1;
v___x_2489_ = lean_box(v___x_2488_);
v___x_2490_ = lean_st_ref_put(v_finished_2481_, v___x_2489_);
lean_dec(v_finished_2481_);
v___x_2491_ = lean_box(v___y_2487_);
v___x_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = 0;
v___x_2496_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2494_, v___x_2495_, v___x_2493_, v___f_2485_);
return v___x_2496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object* v_w_2500_, lean_object* v_lose_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_2500_, v_lose_2501_, v___y_2502_);
lean_dec(v___y_2502_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object* v___y_2505_, lean_object* v_x_2506_){
_start:
{
if (lean_obj_tag(v_x_2506_) == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_x_2506_);
return v___x_2508_;
}
else
{
lean_object* v___x_2509_; 
lean_dec_ref_known(v_x_2506_, 1);
v___x_2509_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_2505_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object* v___y_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_2510_, v_x_2511_);
lean_dec(v___y_2510_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object* v_waiter_2514_, lean_object* v_pendingProducer_2515_, lean_object* v_interestWaiter_2516_, uint8_t v_closed_2517_, lean_object* v_knownSize_2518_, lean_object* v_pendingIncompleteChunk_2519_, lean_object* v_closeError_2520_, uint8_t v_a_2521_, lean_object* v_____r_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_waiter_2514_);
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2527_, 0, v_pendingProducer_2515_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
lean_ctor_set(v___x_2527_, 2, v_interestWaiter_2516_);
lean_ctor_set(v___x_2527_, 3, v_knownSize_2518_);
lean_ctor_set(v___x_2527_, 4, v_pendingIncompleteChunk_2519_);
lean_ctor_set(v___x_2527_, 5, v_closeError_2520_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*6, v_closed_2517_);
v___x_2528_ = lean_st_ref_swap(v___y_2523_, v___x_2527_);
lean_dec(v___x_2528_);
lean_inc(v___y_2523_);
v___f_2529_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2529_, 0, v___y_2523_);
v___x_2530_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2531_, v_a_2521_, v___x_2530_, v___f_2529_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object* v_waiter_2533_, lean_object* v_pendingProducer_2534_, lean_object* v_interestWaiter_2535_, lean_object* v_closed_2536_, lean_object* v_knownSize_2537_, lean_object* v_pendingIncompleteChunk_2538_, lean_object* v_closeError_2539_, lean_object* v_a_2540_, lean_object* v_____r_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
uint8_t v_closed_boxed_2544_; uint8_t v_a_6306__boxed_2545_; lean_object* v_res_2546_; 
v_closed_boxed_2544_ = lean_unbox(v_closed_2536_);
v_a_6306__boxed_2545_ = lean_unbox(v_a_2540_);
v_res_2546_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2533_, v_pendingProducer_2534_, v_interestWaiter_2535_, v_closed_boxed_2544_, v_knownSize_2537_, v_pendingIncompleteChunk_2538_, v_closeError_2539_, v_a_6306__boxed_2545_, v_____r_2541_, v___y_2542_);
lean_dec(v___y_2542_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object* v_waiter_2551_, uint8_t v_a_2552_, lean_object* v___y_2553_, lean_object* v_x_2554_){
_start:
{
if (lean_obj_tag(v_x_2554_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_waiter_2551_);
v_a_2556_ = lean_ctor_get(v_x_2554_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_x_2554_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2558_ = v_x_2554_;
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v_x_2554_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v_pendingProducer_2566_; lean_object* v_pendingConsumer_2567_; lean_object* v_interestWaiter_2568_; uint8_t v_closed_2569_; lean_object* v_knownSize_2570_; lean_object* v_pendingIncompleteChunk_2571_; lean_object* v_closeError_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___f_2575_; 
v_a_2565_ = lean_ctor_get(v_x_2554_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v_x_2554_, 1);
v_pendingProducer_2566_ = lean_ctor_get(v_a_2565_, 0);
lean_inc_n(v_pendingProducer_2566_, 2);
v_pendingConsumer_2567_ = lean_ctor_get(v_a_2565_, 1);
lean_inc(v_pendingConsumer_2567_);
v_interestWaiter_2568_ = lean_ctor_get(v_a_2565_, 2);
lean_inc_n(v_interestWaiter_2568_, 2);
v_closed_2569_ = lean_ctor_get_uint8(v_a_2565_, sizeof(void*)*6);
v_knownSize_2570_ = lean_ctor_get(v_a_2565_, 3);
lean_inc_n(v_knownSize_2570_, 2);
v_pendingIncompleteChunk_2571_ = lean_ctor_get(v_a_2565_, 4);
lean_inc_n(v_pendingIncompleteChunk_2571_, 2);
v_closeError_2572_ = lean_ctor_get(v_a_2565_, 5);
lean_inc_n(v_closeError_2572_, 2);
lean_dec(v_a_2565_);
v___x_2573_ = lean_box(v_closed_2569_);
v___x_2574_ = lean_box(v_a_2552_);
lean_inc_ref(v_waiter_2551_);
v___f_2575_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__0___boxed), 11, 8);
lean_closure_set(v___f_2575_, 0, v_waiter_2551_);
lean_closure_set(v___f_2575_, 1, v_pendingProducer_2566_);
lean_closure_set(v___f_2575_, 2, v_interestWaiter_2568_);
lean_closure_set(v___f_2575_, 3, v___x_2573_);
lean_closure_set(v___f_2575_, 4, v_knownSize_2570_);
lean_closure_set(v___f_2575_, 5, v_pendingIncompleteChunk_2571_);
lean_closure_set(v___f_2575_, 6, v_closeError_2572_);
lean_closure_set(v___f_2575_, 7, v___x_2574_);
if (lean_obj_tag(v_pendingConsumer_2567_) == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec_ref(v___f_2575_);
v___x_2576_ = lean_box(0);
v___x_2577_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2551_, v_pendingProducer_2566_, v_interestWaiter_2568_, v_closed_2569_, v_knownSize_2570_, v_pendingIncompleteChunk_2571_, v_closeError_2572_, v_a_2552_, v___x_2576_, v___y_2553_);
return v___x_2577_;
}
else
{
lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref_known(v_pendingConsumer_2567_, 1);
lean_dec(v_closeError_2572_);
lean_dec(v_pendingIncompleteChunk_2571_);
lean_dec(v_knownSize_2570_);
lean_dec(v_interestWaiter_2568_);
lean_dec(v_pendingProducer_2566_);
lean_dec_ref(v_waiter_2551_);
lean_inc(v___y_2553_);
v___f_2578_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2578_, 0, v___f_2575_);
lean_closure_set(v___f_2578_, 1, v___y_2553_);
v___x_2579_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1));
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2580_, v_a_2552_, v___x_2579_, v___f_2578_);
return v___x_2581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object* v_waiter_2582_, lean_object* v_a_2583_, lean_object* v___y_2584_, lean_object* v_x_2585_, lean_object* v___y_2586_){
_start:
{
uint8_t v_a_6347__boxed_2587_; lean_object* v_res_2588_; 
v_a_6347__boxed_2587_ = lean_unbox(v_a_2583_);
v_res_2588_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v_waiter_2582_, v_a_6347__boxed_2587_, v___y_2584_, v_x_2585_);
lean_dec(v___y_2584_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object* v___x_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2589_);
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object* v___x_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_2594_, v___y_2595_);
lean_dec(v___y_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object* v___y_2600_, lean_object* v_waiter_2601_, lean_object* v_x_2602_){
_start:
{
if (lean_obj_tag(v_x_2602_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v_waiter_2601_);
v_a_2604_ = lean_ctor_get(v_x_2602_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_x_2602_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2606_ = v_x_2602_;
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v_x_2602_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2629_; 
v_a_2613_ = lean_ctor_get(v_x_2602_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_x_2602_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2615_ = v_x_2602_;
v_isShared_2616_ = v_isSharedCheck_2629_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v_x_2602_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2629_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
uint8_t v___x_2617_; 
v___x_2617_ = lean_unbox(v_a_2613_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___x_2621_; 
v___x_2618_ = lean_st_ref_get(v___y_2600_);
lean_inc(v___y_2600_);
lean_inc(v_a_2613_);
v___f_2619_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2619_, 0, v_waiter_2601_);
lean_closure_set(v___f_2619_, 1, v_a_2613_);
lean_closure_set(v___f_2619_, 2, v___y_2600_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2618_);
v___x_2621_ = v___x_2615_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2618_);
v___x_2621_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; 
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
v___x_2623_ = lean_unsigned_to_nat(0u);
v___x_2624_ = lean_unbox(v_a_2613_);
lean_dec(v_a_2613_);
v___x_2625_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2623_, v___x_2624_, v___x_2622_, v___f_2619_);
return v___x_2625_;
}
}
else
{
lean_object* v___f_2627_; lean_object* v___x_2628_; 
lean_del_object(v___x_2615_);
lean_dec(v_a_2613_);
v___f_2627_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_2628_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_waiter_2601_, v___f_2627_, v___y_2600_);
return v___x_2628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object* v___y_2630_, lean_object* v_waiter_2631_, lean_object* v_x_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v___y_2630_, v_waiter_2631_, v_x_2632_);
lean_dec(v___y_2630_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object* v___y_2635_, lean_object* v___f_2636_, lean_object* v_x_2637_){
_start:
{
if (lean_obj_tag(v_x_2637_) == 0)
{
lean_object* v___x_2639_; 
lean_dec_ref(v___f_2636_);
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_x_2637_);
return v___x_2639_;
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; 
lean_dec_ref_known(v_x_2637_, 1);
v___x_2640_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_2635_);
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = 0;
v___x_2643_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2641_, v___x_2642_, v___x_2640_, v___f_2636_);
return v___x_2643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object* v___y_2644_, lean_object* v___f_2645_, lean_object* v_x_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_2644_, v___f_2645_, v_x_2646_);
lean_dec(v___y_2644_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object* v_waiter_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; lean_object* v___f_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; lean_object* v___x_2657_; 
v___x_2652_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2650_);
lean_inc_n(v___y_2650_, 2);
v___f_2653_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__4___boxed), 4, 2);
lean_closure_set(v___f_2653_, 0, v___y_2650_);
lean_closure_set(v___f_2653_, 1, v_waiter_2649_);
v___f_2654_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2654_, 0, v___y_2650_);
lean_closure_set(v___f_2654_, 1, v___f_2653_);
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = 0;
v___x_2657_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2655_, v___x_2656_, v___x_2652_, v___f_2654_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object* v_waiter_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_2658_, v___y_2659_);
lean_dec(v___y_2659_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object* v_stream_2662_, lean_object* v_waiter_2663_){
_start:
{
lean_object* v___f_2665_; lean_object* v___x_2666_; 
v___f_2665_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2665_, 0, v_waiter_2663_);
v___x_2666_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2662_, v___f_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object* v_stream_2667_, lean_object* v_waiter_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_2667_, v_waiter_2668_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object* v_stream_2672_){
_start:
{
lean_object* v___f_2673_; lean_object* v___f_2674_; lean_object* v___f_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___f_2673_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_2672_, 2);
v___f_2674_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2674_, 0, v_stream_2672_);
v___f_2675_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_2676_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2676_, 0, lean_box(0));
lean_closure_set(v___x_2676_, 1, lean_box(0));
lean_closure_set(v___x_2676_, 2, v_stream_2672_);
lean_closure_set(v___x_2676_, 3, v___f_2675_);
v___x_2677_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2677_, 0, lean_box(0));
lean_closure_set(v___x_2677_, 1, lean_box(0));
lean_closure_set(v___x_2677_, 2, v_stream_2672_);
lean_closure_set(v___x_2677_, 3, v___f_2673_);
v___x_2678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___f_2674_);
lean_ctor_set(v___x_2678_, 2, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(lean_object* v_step_2679_, lean_object* v_acc_2680_, lean_object* v___f_2681_, lean_object* v_x_2682_){
_start:
{
if (lean_obj_tag(v_x_2682_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2692_; 
lean_dec_ref(v___f_2681_);
lean_dec(v_acc_2680_);
lean_dec_ref(v_step_2679_);
v_a_2684_ = lean_ctor_get(v_x_2682_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_x_2682_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2686_ = v_x_2682_;
v_isShared_2687_ = v_isSharedCheck_2692_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v_x_2682_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2692_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2706_; 
v_a_2693_ = lean_ctor_get(v_x_2682_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_x_2682_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2695_ = v_x_2682_;
v_isShared_2696_ = v_isSharedCheck_2706_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v_x_2682_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2706_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
if (lean_obj_tag(v_a_2693_) == 1)
{
lean_object* v_val_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; 
lean_del_object(v___x_2695_);
v_val_2697_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v_a_2693_, 1);
v___x_2698_ = lean_apply_3(v_step_2679_, v_val_2697_, v_acc_2680_, lean_box(0));
v___x_2699_ = lean_unsigned_to_nat(0u);
v___x_2700_ = 0;
v___x_2701_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2699_, v___x_2700_, v___x_2698_, v___f_2681_);
return v___x_2701_;
}
else
{
lean_object* v___x_2703_; 
lean_dec(v_a_2693_);
lean_dec_ref(v___f_2681_);
lean_dec_ref(v_step_2679_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v_acc_2680_);
v___x_2703_ = v___x_2695_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_acc_2680_);
v___x_2703_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; 
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed(lean_object* v_step_2707_, lean_object* v_acc_2708_, lean_object* v___f_2709_, lean_object* v_x_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(v_step_2707_, v_acc_2708_, v___f_2709_, v_x_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(lean_object* v_step_2713_, lean_object* v_stream_2714_, lean_object* v_x_2715_){
_start:
{
if (lean_obj_tag(v_x_2715_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2725_; 
lean_dec_ref(v_stream_2714_);
lean_dec_ref(v_step_2713_);
v_a_2717_ = lean_ctor_get(v_x_2715_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_x_2715_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2719_ = v_x_2715_;
v_isShared_2720_ = v_isSharedCheck_2725_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v_x_2715_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2725_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2743_; 
v_a_2726_ = lean_ctor_get(v_x_2715_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_x_2715_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2728_ = v_x_2715_;
v_isShared_2729_ = v_isSharedCheck_2743_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v_x_2715_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2743_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
if (lean_obj_tag(v_a_2726_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2740_; 
lean_dec_ref(v_stream_2714_);
lean_dec_ref(v_step_2713_);
v_a_2730_ = lean_ctor_get(v_a_2726_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_a_2726_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2732_ = v_a_2726_;
v_isShared_2733_ = v_isSharedCheck_2740_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v_a_2726_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2740_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v_a_2730_);
v___x_2735_ = v___x_2728_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2737_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2735_);
v___x_2737_ = v___x_2732_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2742_; 
lean_del_object(v___x_2728_);
v_a_2741_ = lean_ctor_get(v_a_2726_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v_a_2726_, 1);
v___x_2742_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2713_, v_stream_2714_, v_a_2741_);
return v___x_2742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed(lean_object* v_step_2744_, lean_object* v_stream_2745_, lean_object* v_x_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(v_step_2744_, v_stream_2745_, v_x_2746_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(lean_object* v_step_2749_, lean_object* v_stream_2750_, lean_object* v_acc_2751_){
_start:
{
lean_object* v___x_2753_; lean_object* v___f_2754_; lean_object* v___f_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; 
lean_inc_ref(v_stream_2750_);
v___x_2753_ = l_Std_Http_Body_Stream_recv(v_stream_2750_);
lean_inc_ref(v_step_2749_);
v___f_2754_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2754_, 0, v_step_2749_);
lean_closure_set(v___f_2754_, 1, v_stream_2750_);
v___f_2755_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2755_, 0, v_step_2749_);
lean_closure_set(v___f_2755_, 1, v_acc_2751_);
lean_closure_set(v___f_2755_, 2, v___f_2754_);
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = 0;
v___x_2758_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2756_, v___x_2757_, v___x_2753_, v___f_2755_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___boxed(lean_object* v_step_2759_, lean_object* v_stream_2760_, lean_object* v_acc_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2759_, v_stream_2760_, v_acc_2761_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(lean_object* v_00_u03b2_2764_, lean_object* v_step_2765_, lean_object* v_stream_2766_, lean_object* v_acc_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2765_, v_stream_2766_, v_acc_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___boxed(lean_object* v_00_u03b2_2770_, lean_object* v_step_2771_, lean_object* v_stream_2772_, lean_object* v_acc_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(v_00_u03b2_2770_, v_step_2771_, v_stream_2772_, v_acc_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_2776_, lean_object* v_acc_2777_, lean_object* v_step_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2778_, v_stream_2776_, v_acc_2777_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_2781_, lean_object* v_acc_2782_, lean_object* v_step_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_2781_, v_acc_2782_, v_step_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_2786_, lean_object* v_stream_2787_, lean_object* v_acc_2788_, lean_object* v_step_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2789_, v_stream_2787_, v_acc_2788_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_2792_, lean_object* v_stream_2793_, lean_object* v_acc_2794_, lean_object* v_step_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_2792_, v_stream_2793_, v_acc_2794_, v_step_2795_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(lean_object* v_x_2798_){
_start:
{
if (lean_obj_tag(v_x_2798_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2808_; 
v_a_2800_ = lean_ctor_get(v_x_2798_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_x_2798_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2802_ = v_x_2798_;
v_isShared_2803_ = v_isSharedCheck_2808_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v_x_2798_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2808_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_object* v___x_2806_; 
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
return v___x_2806_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2819_; 
v_a_2809_ = lean_ctor_get(v_x_2798_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_x_2798_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2811_ = v_x_2798_;
v_isShared_2812_ = v_isSharedCheck_2819_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v_x_2798_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2819_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v_token_2813_; lean_object* v___x_2814_; lean_object* v___x_2816_; 
v_token_2813_ = lean_ctor_get(v_a_2809_, 1);
lean_inc_ref(v_token_2813_);
lean_dec(v_a_2809_);
v___x_2814_ = l_Std_CancellationToken_selector(v_token_2813_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v___x_2814_);
v___x_2816_ = v___x_2811_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
lean_object* v___x_2817_; 
v___x_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
return v___x_2817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_x_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(v_x_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___y_2823_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed(lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(v___y_2827_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(lean_object* v_x_2830_){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed(lean_object* v_x_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(v_x_2833_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(lean_object* v_stream_2836_, lean_object* v___f_2837_, lean_object* v___f_2838_, lean_object* v___f_2839_, lean_object* v_x_2840_){
_start:
{
if (lean_obj_tag(v_x_2840_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v___f_2839_);
lean_dec_ref(v___f_2838_);
lean_dec_ref(v___f_2837_);
lean_dec_ref(v_stream_2836_);
v_a_2842_ = lean_ctor_get(v_x_2840_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_x_2840_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2844_ = v_x_2840_;
v_isShared_2845_ = v_isSharedCheck_2850_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v_x_2840_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2850_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; 
v_a_2851_ = lean_ctor_get(v_x_2840_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v_x_2840_, 1);
v___x_2852_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2836_);
v___x_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v___f_2837_);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v_a_2851_);
lean_ctor_set(v___x_2854_, 1, v___f_2838_);
v___x_2855_ = lean_unsigned_to_nat(2u);
v___x_2856_ = lean_mk_empty_array_with_capacity(v___x_2855_);
v___x_2857_ = lean_array_push(v___x_2856_, v___x_2853_);
v___x_2858_ = lean_array_push(v___x_2857_, v___x_2854_);
v___x_2859_ = l_Std_Async_Selectable_one___redArg(v___x_2858_);
v___x_2860_ = lean_unsigned_to_nat(0u);
v___x_2861_ = 0;
v___x_2862_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2860_, v___x_2861_, v___x_2859_, v___f_2839_);
return v___x_2862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed(lean_object* v_stream_2863_, lean_object* v___f_2864_, lean_object* v___f_2865_, lean_object* v___f_2866_, lean_object* v_x_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(v_stream_2863_, v___f_2864_, v___f_2865_, v___f_2866_, v_x_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(lean_object* v_step_2870_, lean_object* v_acc_2871_, lean_object* v_a_2872_, lean_object* v___f_2873_, lean_object* v_x_2874_){
_start:
{
if (lean_obj_tag(v_x_2874_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2884_; 
lean_dec_ref(v___f_2873_);
lean_dec(v_acc_2871_);
lean_dec_ref(v_step_2870_);
v_a_2876_ = lean_ctor_get(v_x_2874_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_x_2874_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2878_ = v_x_2874_;
v_isShared_2879_ = v_isSharedCheck_2884_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v_x_2874_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2884_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2898_; 
v_a_2885_ = lean_ctor_get(v_x_2874_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_x_2874_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2887_ = v_x_2874_;
v_isShared_2888_ = v_isSharedCheck_2898_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v_x_2874_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2898_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
if (lean_obj_tag(v_a_2885_) == 1)
{
lean_object* v_val_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; 
lean_del_object(v___x_2887_);
v_val_2889_ = lean_ctor_get(v_a_2885_, 0);
lean_inc(v_val_2889_);
lean_dec_ref_known(v_a_2885_, 1);
lean_inc_ref(v_a_2872_);
v___x_2890_ = lean_apply_4(v_step_2870_, v_val_2889_, v_acc_2871_, v_a_2872_, lean_box(0));
v___x_2891_ = lean_unsigned_to_nat(0u);
v___x_2892_ = 0;
v___x_2893_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2891_, v___x_2892_, v___x_2890_, v___f_2873_);
return v___x_2893_;
}
else
{
lean_object* v___x_2895_; 
lean_dec(v_a_2885_);
lean_dec_ref(v___f_2873_);
lean_dec_ref(v_step_2870_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v_acc_2871_);
v___x_2895_ = v___x_2887_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_acc_2871_);
v___x_2895_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed(lean_object* v_step_2899_, lean_object* v_acc_2900_, lean_object* v_a_2901_, lean_object* v___f_2902_, lean_object* v_x_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(v_step_2899_, v_acc_2900_, v_a_2901_, v___f_2902_, v_x_2903_);
lean_dec_ref(v_a_2901_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed(lean_object* v_step_2909_, lean_object* v_stream_2910_, lean_object* v_a_2911_, lean_object* v_x_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(v_step_2909_, v_stream_2910_, v_a_2911_, v_x_2912_);
lean_dec_ref(v_a_2911_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(lean_object* v_step_2915_, lean_object* v_stream_2916_, lean_object* v_acc_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v___f_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; lean_object* v___x_2925_; lean_object* v___f_2926_; lean_object* v___f_2927_; lean_object* v___f_2928_; lean_object* v___f_2929_; lean_object* v___f_2930_; lean_object* v___x_2931_; 
v___f_2920_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0));
lean_inc_ref_n(v_a_2918_, 3);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v_a_2918_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
v___x_2923_ = lean_unsigned_to_nat(0u);
v___x_2924_ = 0;
v___x_2925_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2923_, v___x_2924_, v___x_2922_, v___f_2920_);
v___f_2926_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1));
v___f_2927_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2));
lean_inc_ref(v_stream_2916_);
lean_inc_ref(v_step_2915_);
v___f_2928_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2928_, 0, v_step_2915_);
lean_closure_set(v___f_2928_, 1, v_stream_2916_);
lean_closure_set(v___f_2928_, 2, v_a_2918_);
v___f_2929_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_2929_, 0, v_step_2915_);
lean_closure_set(v___f_2929_, 1, v_acc_2917_);
lean_closure_set(v___f_2929_, 2, v_a_2918_);
lean_closure_set(v___f_2929_, 3, v___f_2928_);
v___f_2930_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_2930_, 0, v_stream_2916_);
lean_closure_set(v___f_2930_, 1, v___f_2926_);
lean_closure_set(v___f_2930_, 2, v___f_2927_);
lean_closure_set(v___f_2930_, 3, v___f_2929_);
v___x_2931_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2923_, v___x_2924_, v___x_2925_, v___f_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(lean_object* v_step_2932_, lean_object* v_stream_2933_, lean_object* v_a_2934_, lean_object* v_x_2935_){
_start:
{
if (lean_obj_tag(v_x_2935_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v_stream_2933_);
lean_dec_ref(v_step_2932_);
v_a_2937_ = lean_ctor_get(v_x_2935_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_x_2935_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2939_ = v_x_2935_;
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v_x_2935_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2963_; 
v_a_2946_ = lean_ctor_get(v_x_2935_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_x_2935_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2948_ = v_x_2935_;
v_isShared_2949_ = v_isSharedCheck_2963_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v_x_2935_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2963_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
if (lean_obj_tag(v_a_2946_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v_stream_2933_);
lean_dec_ref(v_step_2932_);
v_a_2950_ = lean_ctor_get(v_a_2946_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_a_2946_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2952_ = v_a_2946_;
v_isShared_2953_ = v_isSharedCheck_2960_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v_a_2946_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2960_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v_a_2950_);
v___x_2955_ = v___x_2948_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 0, v___x_2955_);
v___x_2957_ = v___x_2952_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2962_; 
lean_del_object(v___x_2948_);
v_a_2961_ = lean_ctor_get(v_a_2946_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v_a_2946_, 1);
v___x_2962_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2932_, v_stream_2933_, v_a_2961_, v_a_2934_);
return v___x_2962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___boxed(lean_object* v_step_2964_, lean_object* v_stream_2965_, lean_object* v_acc_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2964_, v_stream_2965_, v_acc_2966_, v_a_2967_);
lean_dec_ref(v_a_2967_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(lean_object* v_00_u03b2_2970_, lean_object* v_step_2971_, lean_object* v_stream_2972_, lean_object* v_acc_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2971_, v_stream_2972_, v_acc_2973_, v_a_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___boxed(lean_object* v_00_u03b2_2977_, lean_object* v_step_2978_, lean_object* v_stream_2979_, lean_object* v_acc_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(v_00_u03b2_2977_, v_step_2978_, v_stream_2979_, v_acc_2980_, v_a_2981_);
lean_dec_ref(v_a_2981_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_2984_, lean_object* v_acc_2985_, lean_object* v_step_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2986_, v_stream_2984_, v_acc_2985_, v_a_2987_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_2990_, lean_object* v_acc_2991_, lean_object* v_step_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_2990_, v_acc_2991_, v_step_2992_, v_a_2993_);
lean_dec_ref(v_a_2993_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_2996_, lean_object* v_stream_2997_, lean_object* v_acc_2998_, lean_object* v_step_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2999_, v_stream_2997_, v_acc_2998_, v_a_3000_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_3003_, lean_object* v_stream_3004_, lean_object* v_acc_3005_, lean_object* v_step_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_3003_, v_stream_3004_, v_acc_3005_, v_step_3006_, v_a_3007_);
lean_dec_ref(v_a_3007_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v_x_3012_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v_x_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v_x_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___y_3018_);
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed(lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(v___y_3022_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(lean_object* v_x_3025_){
_start:
{
if (lean_obj_tag(v_x_3025_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3035_; 
v_a_3027_ = lean_ctor_get(v_x_3025_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_x_3025_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3029_ = v_x_3025_;
v_isShared_3030_ = v_isSharedCheck_3035_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v_x_3025_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3035_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
return v___x_3033_;
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3046_; 
v_a_3036_ = lean_ctor_get(v_x_3025_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_x_3025_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3038_ = v_x_3025_;
v_isShared_3039_ = v_isSharedCheck_3046_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v_x_3025_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3046_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v_token_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v_token_3040_ = lean_ctor_get(v_a_3036_, 1);
lean_inc_ref(v_token_3040_);
lean_dec(v_a_3036_);
v___x_3041_ = l_Std_CancellationToken_selector(v_token_3040_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3041_);
v___x_3043_ = v___x_3038_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
return v___x_3044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed(lean_object* v_x_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(v_x_3047_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v_stream_3050_, lean_object* v___f_3051_, lean_object* v___f_3052_, lean_object* v_x_3053_){
_start:
{
if (lean_obj_tag(v_x_3053_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v___f_3052_);
lean_dec_ref(v___f_3051_);
lean_dec_ref(v_stream_3050_);
v_a_3055_ = lean_ctor_get(v_x_3053_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_x_3053_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3057_ = v_x_3053_;
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v_x_3053_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
return v___x_3061_;
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_a_3064_ = lean_ctor_get(v_x_3053_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v_x_3053_, 1);
v___x_3065_ = l_Std_Http_Body_Stream_recvSelector(v_stream_3050_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
lean_ctor_set(v___x_3066_, 1, v___f_3051_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_a_3064_);
lean_ctor_set(v___x_3067_, 1, v___f_3052_);
v___x_3068_ = lean_unsigned_to_nat(2u);
v___x_3069_ = lean_mk_empty_array_with_capacity(v___x_3068_);
v___x_3070_ = lean_array_push(v___x_3069_, v___x_3066_);
v___x_3071_ = lean_array_push(v___x_3070_, v___x_3067_);
v___x_3072_ = l_Std_Async_Selectable_one___redArg(v___x_3071_);
return v___x_3072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v_stream_3073_, lean_object* v___f_3074_, lean_object* v___f_3075_, lean_object* v_x_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_3073_, v___f_3074_, v___f_3075_, v_x_3076_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(lean_object* v___f_3079_, lean_object* v___f_3080_, lean_object* v___f_3081_, lean_object* v_stream_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___f_3090_; lean_object* v___x_3091_; 
lean_inc_ref(v___y_3083_);
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___y_3083_);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
v___x_3087_ = lean_unsigned_to_nat(0u);
v___x_3088_ = 0;
v___x_3089_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3087_, v___x_3088_, v___x_3086_, v___f_3079_);
v___f_3090_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3090_, 0, v_stream_3082_);
lean_closure_set(v___f_3090_, 1, v___f_3080_);
lean_closure_set(v___f_3090_, 2, v___f_3081_);
v___x_3091_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3087_, v___x_3088_, v___x_3089_, v___f_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4___boxed(lean_object* v___f_3092_, lean_object* v___f_3093_, lean_object* v___f_3094_, lean_object* v_stream_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(v___f_3092_, v___f_3093_, v___f_3094_, v_stream_3095_, v___y_3096_);
lean_dec_ref(v___y_3096_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v_toPure_3109_, lean_object* v_result_3110_, lean_object* v_maximumSize_3111_, lean_object* v_inst_3112_, lean_object* v_inst_3113_, lean_object* v_inst_3114_, lean_object* v_stream_3115_, lean_object* v_toBind_3116_, lean_object* v_____do__lift_3117_){
_start:
{
if (lean_obj_tag(v_____do__lift_3117_) == 0)
{
lean_object* v___x_3118_; 
lean_dec(v_toBind_3116_);
lean_dec_ref(v_stream_3115_);
lean_dec(v_inst_3114_);
lean_dec_ref(v_inst_3113_);
lean_dec_ref(v_inst_3112_);
lean_dec(v_maximumSize_3111_);
v___x_3118_ = lean_apply_2(v_toPure_3109_, lean_box(0), v_result_3110_);
return v___x_3118_;
}
else
{
lean_object* v_val_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v_toPure_3109_);
v_val_3119_ = lean_ctor_get(v_____do__lift_3117_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_____do__lift_3117_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3121_ = v_____do__lift_3117_;
v_isShared_3122_ = v_isSharedCheck_3150_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_val_3119_);
lean_dec(v_____do__lift_3117_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3150_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v_data_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v_result_3128_; 
v_data_3123_ = lean_ctor_get(v_val_3119_, 0);
lean_inc_ref(v_data_3123_);
lean_dec(v_val_3119_);
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = lean_byte_array_size(v_result_3110_);
v___x_3126_ = lean_byte_array_size(v_data_3123_);
v___x_3127_ = 0;
v_result_3128_ = lean_byte_array_copy_slice(v_data_3123_, v___x_3124_, v_result_3110_, v___x_3125_, v___x_3126_, v___x_3127_);
lean_dec_ref(v_data_3123_);
if (lean_obj_tag(v_maximumSize_3111_) == 1)
{
lean_object* v_val_3129_; lean_object* v___x_3130_; uint64_t v___x_3131_; uint64_t v___x_3132_; uint8_t v___x_3133_; 
v_val_3129_ = lean_ctor_get(v_maximumSize_3111_, 0);
v___x_3130_ = lean_byte_array_size(v_result_3128_);
v___x_3131_ = lean_uint64_of_nat(v___x_3130_);
v___x_3132_ = lean_unbox_uint64(v_val_3129_);
v___x_3133_ = lean_uint64_dec_lt(v___x_3132_, v___x_3131_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
lean_del_object(v___x_3121_);
lean_dec(v_toBind_3116_);
v___x_3134_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3112_, v_inst_3113_, v_inst_3114_, v_stream_3115_, v_maximumSize_3111_, v_result_3128_);
return v___x_3134_;
}
else
{
lean_object* v_throw_3135_; lean_object* v___f_3136_; lean_object* v___x_3137_; uint64_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
lean_inc(v_val_3129_);
v_throw_3135_ = lean_ctor_get(v_inst_3113_, 0);
lean_inc(v_throw_3135_);
v___f_3136_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0), 7, 6);
lean_closure_set(v___f_3136_, 0, v_inst_3112_);
lean_closure_set(v___f_3136_, 1, v_inst_3113_);
lean_closure_set(v___f_3136_, 2, v_inst_3114_);
lean_closure_set(v___f_3136_, 3, v_stream_3115_);
lean_closure_set(v___f_3136_, 4, v_maximumSize_3111_);
lean_closure_set(v___f_3136_, 5, v_result_3128_);
v___x_3137_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0));
v___x_3138_ = lean_unbox_uint64(v_val_3129_);
lean_dec(v_val_3129_);
v___x_3139_ = lean_uint64_to_nat(v___x_3138_);
v___x_3140_ = l_Nat_reprFast(v___x_3139_);
v___x_3141_ = lean_string_append(v___x_3137_, v___x_3140_);
lean_dec_ref(v___x_3140_);
v___x_3142_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1));
v___x_3143_ = lean_string_append(v___x_3141_, v___x_3142_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set_tag(v___x_3121_, 18);
lean_ctor_set(v___x_3121_, 0, v___x_3143_);
v___x_3145_ = v___x_3121_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_apply_2(v_throw_3135_, lean_box(0), v___x_3145_);
v___x_3147_ = lean_apply_4(v_toBind_3116_, lean_box(0), lean_box(0), v___x_3146_, v___f_3136_);
return v___x_3147_;
}
}
}
else
{
lean_object* v___x_3149_; 
lean_del_object(v___x_3121_);
lean_dec(v_toBind_3116_);
v___x_3149_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3112_, v_inst_3113_, v_inst_3114_, v_stream_3115_, v_maximumSize_3111_, v_result_3128_);
return v___x_3149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_stream_3154_, lean_object* v_maximumSize_3155_, lean_object* v_result_3156_){
_start:
{
lean_object* v_toApplicative_3157_; lean_object* v_toBind_3158_; lean_object* v_toPure_3159_; lean_object* v___x_3160_; lean_object* v___f_3161_; lean_object* v___x_3162_; 
v_toApplicative_3157_ = lean_ctor_get(v_inst_3151_, 0);
v_toBind_3158_ = lean_ctor_get(v_inst_3151_, 1);
lean_inc_n(v_toBind_3158_, 2);
v_toPure_3159_ = lean_ctor_get(v_toApplicative_3157_, 1);
lean_inc(v_toPure_3159_);
lean_inc(v_inst_3153_);
lean_inc_ref(v_stream_3154_);
v___x_3160_ = lean_apply_1(v_inst_3153_, v_stream_3154_);
v___f_3161_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 9, 8);
lean_closure_set(v___f_3161_, 0, v_toPure_3159_);
lean_closure_set(v___f_3161_, 1, v_result_3156_);
lean_closure_set(v___f_3161_, 2, v_maximumSize_3155_);
lean_closure_set(v___f_3161_, 3, v_inst_3151_);
lean_closure_set(v___f_3161_, 4, v_inst_3152_);
lean_closure_set(v___f_3161_, 5, v_inst_3153_);
lean_closure_set(v___f_3161_, 6, v_stream_3154_);
lean_closure_set(v___f_3161_, 7, v_toBind_3158_);
v___x_3162_ = lean_apply_4(v_toBind_3158_, lean_box(0), lean_box(0), v___x_3160_, v___f_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_stream_3166_, lean_object* v_maximumSize_3167_, lean_object* v_result_3168_, lean_object* v_____r_3169_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3163_, v_inst_3164_, v_inst_3165_, v_stream_3166_, v_maximumSize_3167_, v_result_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_stream_3175_, lean_object* v_maximumSize_3176_, lean_object* v_result_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3172_, v_inst_3173_, v_inst_3174_, v_stream_3175_, v_maximumSize_3176_, v_result_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v_toPure_3181_, lean_object* v_result_3182_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_apply_1(v_inst_3179_, v_result_3182_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v_toPure_3181_);
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3193_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3193_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v_throw_3188_; lean_object* v___x_3190_; 
v_throw_3188_ = lean_ctor_get(v_inst_3180_, 0);
lean_inc(v_throw_3188_);
lean_dec_ref(v_inst_3180_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set_tag(v___x_3186_, 18);
v___x_3190_ = v___x_3186_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3184_);
v___x_3190_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_apply_2(v_throw_3188_, lean_box(0), v___x_3190_);
return v___x_3191_;
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3195_; 
lean_dec_ref(v_inst_3180_);
v_a_3194_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3194_);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3195_ = lean_apply_2(v_toPure_3181_, lean_box(0), v_a_3194_);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_inst_3199_, lean_object* v_stream_3200_, lean_object* v_maximumSize_3201_){
_start:
{
lean_object* v_toApplicative_3202_; lean_object* v_toBind_3203_; lean_object* v_toPure_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___f_3207_; lean_object* v___x_3208_; 
v_toApplicative_3202_ = lean_ctor_get(v_inst_3197_, 0);
v_toBind_3203_ = lean_ctor_get(v_inst_3197_, 1);
lean_inc(v_toBind_3203_);
v_toPure_3204_ = lean_ctor_get(v_toApplicative_3202_, 1);
lean_inc(v_toPure_3204_);
v___x_3205_ = l_ByteArray_empty;
lean_inc_ref(v_inst_3198_);
v___x_3206_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3197_, v_inst_3198_, v_inst_3199_, v_stream_3200_, v_maximumSize_3201_, v___x_3205_);
v___f_3207_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3207_, 0, v_inst_3196_);
lean_closure_set(v___f_3207_, 1, v_inst_3198_);
lean_closure_set(v___f_3207_, 2, v_toPure_3204_);
v___x_3208_ = lean_apply_4(v_toBind_3203_, lean_box(0), lean_box(0), v___x_3206_, v___f_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_3209_, lean_object* v_m_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_stream_3215_, lean_object* v_maximumSize_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_3211_, v_inst_3212_, v_inst_3213_, v_inst_3214_, v_stream_3215_, v_maximumSize_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0(lean_object* v_toPure_3218_, lean_object* v_____r_3219_){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_apply_2(v_toPure_3218_, lean_box(0), v___x_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(lean_object* v_toPure_3222_, uint64_t v_consumed_3223_, lean_object* v_drainLimit_3224_, lean_object* v_inst_3225_, lean_object* v_inst_3226_, lean_object* v_stream_3227_, lean_object* v_closeStream_3228_, lean_object* v_toBind_3229_, lean_object* v___f_3230_, lean_object* v_____do__lift_3231_){
_start:
{
if (lean_obj_tag(v_____do__lift_3231_) == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
lean_dec(v___f_3230_);
lean_dec(v_toBind_3229_);
lean_dec(v_closeStream_3228_);
lean_dec_ref(v_stream_3227_);
lean_dec(v_inst_3226_);
lean_dec_ref(v_inst_3225_);
lean_dec(v_drainLimit_3224_);
v___x_3232_ = lean_box(0);
v___x_3233_ = lean_apply_2(v_toPure_3222_, lean_box(0), v___x_3232_);
return v___x_3233_;
}
else
{
lean_object* v_val_3234_; lean_object* v_data_3235_; lean_object* v___x_3236_; uint64_t v___x_3237_; uint64_t v_consumed_3238_; 
lean_dec(v_toPure_3222_);
v_val_3234_ = lean_ctor_get(v_____do__lift_3231_, 0);
v_data_3235_ = lean_ctor_get(v_val_3234_, 0);
v___x_3236_ = lean_byte_array_size(v_data_3235_);
v___x_3237_ = lean_uint64_of_nat(v___x_3236_);
v_consumed_3238_ = lean_uint64_add(v_consumed_3223_, v___x_3237_);
if (lean_obj_tag(v_drainLimit_3224_) == 1)
{
lean_object* v_val_3239_; uint64_t v___x_3240_; uint8_t v___x_3241_; 
v_val_3239_ = lean_ctor_get(v_drainLimit_3224_, 0);
v___x_3240_ = lean_unbox_uint64(v_val_3239_);
v___x_3241_ = lean_uint64_dec_lt(v___x_3240_, v_consumed_3238_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; 
lean_dec(v___f_3230_);
lean_dec(v_toBind_3229_);
v___x_3242_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3225_, v_inst_3226_, v_stream_3227_, v_drainLimit_3224_, v_closeStream_3228_, v_consumed_3238_);
return v___x_3242_;
}
else
{
lean_object* v___x_3243_; 
lean_dec_ref_known(v_drainLimit_3224_, 1);
lean_dec_ref(v_stream_3227_);
lean_dec(v_inst_3226_);
lean_dec_ref(v_inst_3225_);
v___x_3243_ = lean_apply_4(v_toBind_3229_, lean_box(0), lean_box(0), v_closeStream_3228_, v___f_3230_);
return v___x_3243_;
}
}
else
{
lean_object* v___x_3244_; 
lean_dec(v___f_3230_);
lean_dec(v_toBind_3229_);
v___x_3244_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3225_, v_inst_3226_, v_stream_3227_, v_drainLimit_3224_, v_closeStream_3228_, v_consumed_3238_);
return v___x_3244_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed(lean_object* v_toPure_3245_, lean_object* v_consumed_3246_, lean_object* v_drainLimit_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_stream_3250_, lean_object* v_closeStream_3251_, lean_object* v_toBind_3252_, lean_object* v___f_3253_, lean_object* v_____do__lift_3254_){
_start:
{
uint64_t v_consumed_boxed_3255_; lean_object* v_res_3256_; 
v_consumed_boxed_3255_ = lean_unbox_uint64(v_consumed_3246_);
lean_dec_ref(v_consumed_3246_);
v_res_3256_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(v_toPure_3245_, v_consumed_boxed_3255_, v_drainLimit_3247_, v_inst_3248_, v_inst_3249_, v_stream_3250_, v_closeStream_3251_, v_toBind_3252_, v___f_3253_, v_____do__lift_3254_);
lean_dec(v_____do__lift_3254_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(lean_object* v_inst_3257_, lean_object* v_inst_3258_, lean_object* v_stream_3259_, lean_object* v_drainLimit_3260_, lean_object* v_closeStream_3261_, uint64_t v_consumed_3262_){
_start:
{
lean_object* v_toApplicative_3263_; lean_object* v_toBind_3264_; lean_object* v_toPure_3265_; lean_object* v___x_3266_; lean_object* v___f_3267_; lean_object* v___x_3268_; lean_object* v___f_3269_; lean_object* v___x_3270_; 
v_toApplicative_3263_ = lean_ctor_get(v_inst_3257_, 0);
v_toBind_3264_ = lean_ctor_get(v_inst_3257_, 1);
lean_inc_n(v_toBind_3264_, 2);
v_toPure_3265_ = lean_ctor_get(v_toApplicative_3263_, 1);
lean_inc_n(v_toPure_3265_, 2);
lean_inc(v_inst_3258_);
lean_inc_ref(v_stream_3259_);
v___x_3266_ = lean_apply_1(v_inst_3258_, v_stream_3259_);
v___f_3267_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3267_, 0, v_toPure_3265_);
v___x_3268_ = lean_box_uint64(v_consumed_3262_);
v___f_3269_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3269_, 0, v_toPure_3265_);
lean_closure_set(v___f_3269_, 1, v___x_3268_);
lean_closure_set(v___f_3269_, 2, v_drainLimit_3260_);
lean_closure_set(v___f_3269_, 3, v_inst_3257_);
lean_closure_set(v___f_3269_, 4, v_inst_3258_);
lean_closure_set(v___f_3269_, 5, v_stream_3259_);
lean_closure_set(v___f_3269_, 6, v_closeStream_3261_);
lean_closure_set(v___f_3269_, 7, v_toBind_3264_);
lean_closure_set(v___f_3269_, 8, v___f_3267_);
v___x_3270_ = lean_apply_4(v_toBind_3264_, lean_box(0), lean_box(0), v___x_3266_, v___f_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___boxed(lean_object* v_inst_3271_, lean_object* v_inst_3272_, lean_object* v_stream_3273_, lean_object* v_drainLimit_3274_, lean_object* v_closeStream_3275_, lean_object* v_consumed_3276_){
_start:
{
uint64_t v_consumed_boxed_3277_; lean_object* v_res_3278_; 
v_consumed_boxed_3277_ = lean_unbox_uint64(v_consumed_3276_);
lean_dec_ref(v_consumed_3276_);
v_res_3278_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3271_, v_inst_3272_, v_stream_3273_, v_drainLimit_3274_, v_closeStream_3275_, v_consumed_boxed_3277_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_object* v_m_3279_, lean_object* v_inst_3280_, lean_object* v_inst_3281_, lean_object* v_stream_3282_, lean_object* v_drainLimit_3283_, lean_object* v_closeStream_3284_, uint64_t v_consumed_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3280_, v_inst_3281_, v_stream_3282_, v_drainLimit_3283_, v_closeStream_3284_, v_consumed_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___boxed(lean_object* v_m_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_stream_3290_, lean_object* v_drainLimit_3291_, lean_object* v_closeStream_3292_, lean_object* v_consumed_3293_){
_start:
{
uint64_t v_consumed_boxed_3294_; lean_object* v_res_3295_; 
v_consumed_boxed_3294_ = lean_unbox_uint64(v_consumed_3293_);
lean_dec_ref(v_consumed_3293_);
v_res_3295_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(v_m_3287_, v_inst_3288_, v_inst_3289_, v_stream_3290_, v_drainLimit_3291_, v_closeStream_3292_, v_consumed_boxed_3294_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain___redArg(lean_object* v_inst_3296_, lean_object* v_inst_3297_, lean_object* v_stream_3298_, lean_object* v_drainLimit_3299_, lean_object* v_closeStream_3300_){
_start:
{
uint64_t v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = 0ULL;
v___x_3302_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3296_, v_inst_3297_, v_stream_3298_, v_drainLimit_3299_, v_closeStream_3300_, v___x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain(lean_object* v_m_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_stream_3306_, lean_object* v_drainLimit_3307_, lean_object* v_closeStream_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Std_Http_Body_Stream_drain___redArg(v_inst_3304_, v_inst_3305_, v_stream_3306_, v_drainLimit_3307_, v_closeStream_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t v_incomplete_3315_, lean_object* v_chunk_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v_pendingProducer_3321_; lean_object* v_pendingConsumer_3322_; lean_object* v_interestWaiter_3323_; uint8_t v_closed_3324_; lean_object* v_knownSize_3325_; lean_object* v_pendingIncompleteChunk_3326_; lean_object* v_closeError_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3368_; 
v___x_3319_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_3317_);
v___x_3320_ = lean_st_ref_get(v___y_3317_);
v_pendingProducer_3321_ = lean_ctor_get(v___x_3320_, 0);
v_pendingConsumer_3322_ = lean_ctor_get(v___x_3320_, 1);
v_interestWaiter_3323_ = lean_ctor_get(v___x_3320_, 2);
v_closed_3324_ = lean_ctor_get_uint8(v___x_3320_, sizeof(void*)*6);
v_knownSize_3325_ = lean_ctor_get(v___x_3320_, 3);
v_pendingIncompleteChunk_3326_ = lean_ctor_get(v___x_3320_, 4);
v_closeError_3327_ = lean_ctor_get(v___x_3320_, 5);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3329_ = v___x_3320_;
v_isShared_3330_ = v_isSharedCheck_3368_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_closeError_3327_);
lean_inc(v_pendingIncompleteChunk_3326_);
lean_inc(v_knownSize_3325_);
lean_inc(v_interestWaiter_3323_);
lean_inc(v_pendingConsumer_3322_);
lean_inc(v_pendingProducer_3321_);
lean_dec(v___x_3320_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3368_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___y_3332_; 
if (v_closed_3324_ == 0)
{
if (lean_obj_tag(v_pendingIncompleteChunk_3326_) == 0)
{
v___y_3332_ = v_chunk_3316_;
goto v___jp_3331_;
}
else
{
lean_object* v_val_3346_; lean_object* v_data_3347_; lean_object* v_extensions_3348_; lean_object* v_data_3349_; lean_object* v_extensions_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3366_; 
v_val_3346_ = lean_ctor_get(v_pendingIncompleteChunk_3326_, 0);
lean_inc(v_val_3346_);
lean_dec_ref_known(v_pendingIncompleteChunk_3326_, 1);
v_data_3347_ = lean_ctor_get(v_val_3346_, 0);
lean_inc_ref(v_data_3347_);
v_extensions_3348_ = lean_ctor_get(v_val_3346_, 1);
lean_inc_ref(v_extensions_3348_);
lean_dec(v_val_3346_);
v_data_3349_ = lean_ctor_get(v_chunk_3316_, 0);
v_extensions_3350_ = lean_ctor_get(v_chunk_3316_, 1);
v_isSharedCheck_3366_ = !lean_is_exclusive(v_chunk_3316_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3352_ = v_chunk_3316_;
v_isShared_3353_ = v_isSharedCheck_3366_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_extensions_3350_);
lean_inc(v_data_3349_);
lean_dec(v_chunk_3316_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3366_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3354_ = lean_unsigned_to_nat(0u);
v___x_3355_ = lean_byte_array_size(v_data_3347_);
v___x_3356_ = lean_byte_array_size(v_data_3349_);
v___x_3357_ = lean_byte_array_copy_slice(v_data_3349_, v___x_3354_, v_data_3347_, v___x_3355_, v___x_3356_, v_closed_3324_);
lean_dec_ref(v_data_3349_);
v___x_3358_ = lean_array_get_size(v_extensions_3348_);
v___x_3359_ = lean_nat_dec_eq(v___x_3358_, v___x_3354_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3361_; 
lean_dec_ref(v_extensions_3350_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 1, v_extensions_3348_);
lean_ctor_set(v___x_3352_, 0, v___x_3357_);
v___x_3361_ = v___x_3352_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_extensions_3348_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
v___y_3332_ = v___x_3361_;
goto v___jp_3331_;
}
}
else
{
lean_object* v___x_3364_; 
lean_dec_ref(v_extensions_3348_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3357_);
v___x_3364_ = v___x_3352_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_extensions_3350_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
v___y_3332_ = v___x_3364_;
goto v___jp_3331_;
}
}
}
}
}
else
{
lean_object* v___x_3367_; 
lean_del_object(v___x_3329_);
lean_dec(v_closeError_3327_);
lean_dec(v_pendingIncompleteChunk_3326_);
lean_dec(v_knownSize_3325_);
lean_dec(v_interestWaiter_3323_);
lean_dec(v_pendingConsumer_3322_);
lean_dec(v_pendingProducer_3321_);
lean_dec_ref(v_chunk_3316_);
v___x_3367_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_3367_;
}
v___jp_3331_:
{
if (v_incomplete_3315_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = lean_box(0);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 4, v___x_3333_);
v___x_3335_ = v___x_3329_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_pendingProducer_3321_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_pendingConsumer_3322_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_interestWaiter_3323_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_knownSize_3325_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v___x_3333_);
lean_ctor_set(v_reuseFailAlloc_3339_, 5, v_closeError_3327_);
lean_ctor_set_uint8(v_reuseFailAlloc_3339_, sizeof(void*)*6, v_closed_3324_);
v___x_3335_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = lean_st_ref_swap(v___y_3317_, v___x_3335_);
lean_dec(v___x_3336_);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___y_3332_);
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
return v___x_3338_;
}
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3340_, 0, v___y_3332_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 4, v___x_3340_);
v___x_3342_ = v___x_3329_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_pendingProducer_3321_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_pendingConsumer_3322_);
lean_ctor_set(v_reuseFailAlloc_3345_, 2, v_interestWaiter_3323_);
lean_ctor_set(v_reuseFailAlloc_3345_, 3, v_knownSize_3325_);
lean_ctor_set(v_reuseFailAlloc_3345_, 4, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3345_, 5, v_closeError_3327_);
lean_ctor_set_uint8(v_reuseFailAlloc_3345_, sizeof(void*)*6, v_closed_3324_);
v___x_3342_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = lean_st_ref_swap(v___y_3317_, v___x_3342_);
lean_dec(v___x_3343_);
v___x_3344_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
return v___x_3344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_incomplete_3369_, lean_object* v_chunk_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v_incomplete_boxed_3373_; lean_object* v_res_3374_; 
v_incomplete_boxed_3373_ = lean_unbox(v_incomplete_3369_);
v_res_3374_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_incomplete_boxed_3373_, v_chunk_3370_, v___y_3371_);
lean_dec(v___y_3371_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_3375_, lean_object* v_chunk_3376_, uint8_t v_incomplete_3377_){
_start:
{
lean_object* v___x_3379_; lean_object* v___f_3380_; lean_object* v___x_3381_; 
v___x_3379_ = lean_box(v_incomplete_3377_);
v___f_3380_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3380_, 0, v___x_3379_);
lean_closure_set(v___f_3380_, 1, v_chunk_3376_);
v___x_3381_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_3375_, v___f_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_3382_, lean_object* v_chunk_3383_, lean_object* v_incomplete_3384_, lean_object* v_a_3385_){
_start:
{
uint8_t v_incomplete_boxed_3386_; lean_object* v_res_3387_; 
v_incomplete_boxed_3386_ = lean_unbox(v_incomplete_3384_);
v_res_3387_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3382_, v_chunk_3383_, v_incomplete_boxed_3386_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_3394_){
_start:
{
if (lean_obj_tag(v_x_3394_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3404_; 
v_a_3396_ = lean_ctor_get(v_x_3394_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_x_3394_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3398_ = v_x_3394_;
v_isShared_3399_ = v_isSharedCheck_3404_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v_x_3394_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3404_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
}
}
else
{
lean_object* v___x_3405_; 
lean_dec_ref_known(v_x_3394_, 1);
v___x_3405_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_3405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_3406_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___3409_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___3412_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_3419_, lean_object* v_x_3420_){
_start:
{
if (lean_obj_tag(v_x_3420_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3432_; 
lean_dec_ref(v___f_3419_);
v_a_3424_ = lean_ctor_get(v_x_3420_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_x_3420_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3426_ = v_x_3420_;
v_isShared_3427_ = v_isSharedCheck_3432_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v_x_3420_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3432_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
return v___x_3430_;
}
}
}
else
{
lean_object* v_a_3433_; 
v_a_3433_ = lean_ctor_get(v_x_3420_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v_x_3420_, 1);
if (lean_obj_tag(v_a_3433_) == 1)
{
lean_object* v_val_3434_; uint8_t v___x_3435_; 
v_val_3434_ = lean_ctor_get(v_a_3433_, 0);
lean_inc(v_val_3434_);
lean_dec_ref_known(v_a_3433_, 1);
v___x_3435_ = lean_unbox(v_val_3434_);
lean_dec(v_val_3434_);
if (v___x_3435_ == 1)
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_apply_2(v___f_3419_, v___x_3436_, lean_box(0));
return v___x_3437_;
}
else
{
lean_dec_ref(v___f_3419_);
goto v___jp_3422_;
}
}
else
{
lean_dec(v_a_3433_);
lean_dec_ref(v___f_3419_);
goto v___jp_3422_;
}
}
v___jp_3422_:
{
lean_object* v___x_3423_; 
v___x_3423_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_3423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_3438_, lean_object* v_x_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_3438_, v_x_3439_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_3442_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3443_, 0, v_a_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_3444_, lean_object* v_x_3445_){
_start:
{
if (lean_obj_tag(v_x_3445_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3455_; 
v_a_3447_ = lean_ctor_get(v_x_3445_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_x_3445_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3449_ = v_x_3445_;
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v_x_3445_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
}
else
{
lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3466_; 
v_isSharedCheck_3466_ = !lean_is_exclusive(v_x_3445_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; 
v_unused_3467_ = lean_ctor_get(v_x_3445_, 0);
lean_dec(v_unused_3467_);
v___x_3457_ = v_x_3445_;
v_isShared_3458_ = v_isSharedCheck_3466_;
goto v_resetjp_3456_;
}
else
{
lean_dec(v_x_3445_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3466_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3459_ = lean_box(v___x_3444_);
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3460_);
v___x_3462_ = v___x_3457_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
return v___x_3464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_3468_, lean_object* v_x_3469_, lean_object* v___y_3470_){
_start:
{
uint8_t v___x_5848__boxed_3471_; lean_object* v_res_3472_; 
v___x_5848__boxed_3471_ = lean_unbox(v___x_3468_);
v_res_3472_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5848__boxed_3471_, v_x_3469_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_3473_, lean_object* v_x_3474_){
_start:
{
if (lean_obj_tag(v_x_3474_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3484_; 
v_a_3476_ = lean_ctor_get(v_x_3474_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_x_3474_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3478_ = v_x_3474_;
v_isShared_3479_ = v_isSharedCheck_3484_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v_x_3474_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3484_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
return v___x_3482_;
}
}
}
else
{
lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3495_; 
v_isSharedCheck_3495_ = !lean_is_exclusive(v_x_3474_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; 
v_unused_3496_ = lean_ctor_get(v_x_3474_, 0);
lean_dec(v_unused_3496_);
v___x_3486_ = v_x_3474_;
v_isShared_3487_ = v_isSharedCheck_3495_;
goto v_resetjp_3485_;
}
else
{
lean_dec(v_x_3474_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3495_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3488_ = lean_box(v_a_3473_);
v___x_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3489_);
v___x_3491_ = v___x_3486_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
v___x_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
return v___x_3493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_3497_, lean_object* v_x_3498_, lean_object* v___y_3499_){
_start:
{
uint8_t v_a_5900__boxed_3500_; lean_object* v_res_3501_; 
v_a_5900__boxed_3500_ = lean_unbox(v_a_3497_);
v_res_3501_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5900__boxed_3500_, v_x_3498_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_3502_, lean_object* v_interestWaiter_3503_, uint8_t v_closed_3504_, lean_object* v_knownSize_3505_, lean_object* v_pendingIncompleteChunk_3506_, lean_object* v_closeError_3507_, lean_object* v___y_3508_, lean_object* v_chunk_3509_, lean_object* v___f_3510_, lean_object* v_x_3511_){
_start:
{
if (lean_obj_tag(v_x_3511_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3521_; 
lean_dec_ref(v___f_3510_);
lean_dec(v_closeError_3507_);
lean_dec(v_pendingIncompleteChunk_3506_);
lean_dec(v_knownSize_3505_);
lean_dec(v_interestWaiter_3503_);
lean_dec(v_pendingProducer_3502_);
v_a_3513_ = lean_ctor_get(v_x_3511_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_x_3511_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3515_ = v_x_3511_;
v_isShared_3516_ = v_isSharedCheck_3521_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v_x_3511_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3521_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
return v___x_3519_;
}
}
}
else
{
lean_object* v_a_3522_; uint8_t v___x_3523_; 
v_a_3522_ = lean_ctor_get(v_x_3511_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v_x_3511_, 1);
v___x_3523_ = lean_unbox(v_a_3522_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___f_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; lean_object* v___x_3531_; 
lean_dec_ref(v___f_3510_);
v___x_3524_ = lean_box(0);
v___x_3525_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3525_, 0, v_pendingProducer_3502_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
lean_ctor_set(v___x_3525_, 2, v_interestWaiter_3503_);
lean_ctor_set(v___x_3525_, 3, v_knownSize_3505_);
lean_ctor_set(v___x_3525_, 4, v_pendingIncompleteChunk_3506_);
lean_ctor_set(v___x_3525_, 5, v_closeError_3507_);
lean_ctor_set_uint8(v___x_3525_, sizeof(void*)*6, v_closed_3504_);
v___x_3526_ = lean_st_ref_swap(v___y_3508_, v___x_3525_);
lean_dec(v___x_3526_);
lean_inc(v_a_3522_);
v___f_3527_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3527_, 0, v_a_3522_);
v___x_3528_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3529_ = lean_unsigned_to_nat(0u);
v___x_3530_ = lean_unbox(v_a_3522_);
lean_dec(v_a_3522_);
v___x_3531_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3529_, v___x_3530_, v___x_3528_, v___f_3527_);
return v___x_3531_;
}
else
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_dec(v_a_3522_);
v___x_3532_ = lean_box(0);
v___x_3533_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_3505_, v_chunk_3509_);
v___x_3534_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3534_, 0, v_pendingProducer_3502_);
lean_ctor_set(v___x_3534_, 1, v___x_3532_);
lean_ctor_set(v___x_3534_, 2, v_interestWaiter_3503_);
lean_ctor_set(v___x_3534_, 3, v___x_3533_);
lean_ctor_set(v___x_3534_, 4, v_pendingIncompleteChunk_3506_);
lean_ctor_set(v___x_3534_, 5, v_closeError_3507_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*6, v_closed_3504_);
v___x_3535_ = lean_st_ref_swap(v___y_3508_, v___x_3534_);
lean_dec(v___x_3535_);
v___x_3536_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3537_ = lean_unsigned_to_nat(0u);
v___x_3538_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3537_, v_closed_3504_, v___x_3536_, v___f_3510_);
return v___x_3538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_3539_, lean_object* v_interestWaiter_3540_, lean_object* v_closed_3541_, lean_object* v_knownSize_3542_, lean_object* v_pendingIncompleteChunk_3543_, lean_object* v_closeError_3544_, lean_object* v___y_3545_, lean_object* v_chunk_3546_, lean_object* v___f_3547_, lean_object* v_x_3548_, lean_object* v___y_3549_){
_start:
{
uint8_t v_closed_boxed_3550_; lean_object* v_res_3551_; 
v_closed_boxed_3550_ = lean_unbox(v_closed_3541_);
v_res_3551_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_3539_, v_interestWaiter_3540_, v_closed_boxed_3550_, v_knownSize_3542_, v_pendingIncompleteChunk_3543_, v_closeError_3544_, v___y_3545_, v_chunk_3546_, v___f_3547_, v_x_3548_);
lean_dec_ref(v_chunk_3546_);
lean_dec(v___y_3545_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v_chunk_3570_, lean_object* v___y_3571_, lean_object* v_a_3572_, lean_object* v___f_3573_, lean_object* v_x_3574_){
_start:
{
if (lean_obj_tag(v_x_3574_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v___f_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_chunk_3570_);
v_a_3576_ = lean_ctor_get(v_x_3574_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_x_3574_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3578_ = v_x_3574_;
v_isShared_3579_ = v_isSharedCheck_3584_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v_x_3574_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3584_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; 
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3638_; 
v_a_3585_ = lean_ctor_get(v_x_3574_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_x_3574_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3587_ = v_x_3574_;
v_isShared_3588_ = v_isSharedCheck_3638_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v_x_3574_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3638_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
uint8_t v_closed_3589_; 
v_closed_3589_ = lean_ctor_get_uint8(v_a_3585_, sizeof(void*)*6);
if (v_closed_3589_ == 0)
{
lean_object* v_pendingConsumer_3590_; 
v_pendingConsumer_3590_ = lean_ctor_get(v_a_3585_, 1);
lean_inc(v_pendingConsumer_3590_);
if (lean_obj_tag(v_pendingConsumer_3590_) == 1)
{
lean_object* v_pendingProducer_3591_; lean_object* v_interestWaiter_3592_; lean_object* v_knownSize_3593_; lean_object* v_pendingIncompleteChunk_3594_; lean_object* v_closeError_3595_; lean_object* v_val_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3615_; 
lean_dec_ref(v___f_3573_);
lean_dec(v_a_3572_);
v_pendingProducer_3591_ = lean_ctor_get(v_a_3585_, 0);
lean_inc(v_pendingProducer_3591_);
v_interestWaiter_3592_ = lean_ctor_get(v_a_3585_, 2);
lean_inc(v_interestWaiter_3592_);
v_knownSize_3593_ = lean_ctor_get(v_a_3585_, 3);
lean_inc(v_knownSize_3593_);
v_pendingIncompleteChunk_3594_ = lean_ctor_get(v_a_3585_, 4);
lean_inc(v_pendingIncompleteChunk_3594_);
v_closeError_3595_ = lean_ctor_get(v_a_3585_, 5);
lean_inc(v_closeError_3595_);
lean_dec(v_a_3585_);
v_val_3596_ = lean_ctor_get(v_pendingConsumer_3590_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_pendingConsumer_3590_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3598_ = v_pendingConsumer_3590_;
v_isShared_3599_ = v_isSharedCheck_3615_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_val_3596_);
lean_dec(v_pendingConsumer_3590_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3615_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
lean_inc_ref(v_chunk_3570_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v_chunk_3570_);
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_chunk_3570_);
v___x_3601_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3603_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v___x_3601_);
v___x_3603_ = v___x_3587_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
uint8_t v___x_3604_; lean_object* v___f_3605_; lean_object* v___x_3606_; lean_object* v___f_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3604_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_3596_, v___x_3603_);
lean_dec(v_val_3596_);
v___f_3605_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_3606_ = lean_box(v_closed_3589_);
lean_inc(v___y_3571_);
v___f_3607_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 11, 9);
lean_closure_set(v___f_3607_, 0, v_pendingProducer_3591_);
lean_closure_set(v___f_3607_, 1, v_interestWaiter_3592_);
lean_closure_set(v___f_3607_, 2, v___x_3606_);
lean_closure_set(v___f_3607_, 3, v_knownSize_3593_);
lean_closure_set(v___f_3607_, 4, v_pendingIncompleteChunk_3594_);
lean_closure_set(v___f_3607_, 5, v_closeError_3595_);
lean_closure_set(v___f_3607_, 6, v___y_3571_);
lean_closure_set(v___f_3607_, 7, v_chunk_3570_);
lean_closure_set(v___f_3607_, 8, v___f_3605_);
v___x_3608_ = lean_box(v___x_3604_);
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
v___x_3611_ = lean_unsigned_to_nat(0u);
v___x_3612_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3611_, v_closed_3589_, v___x_3610_, v___f_3607_);
return v___x_3612_;
}
}
}
}
else
{
lean_object* v_pendingProducer_3616_; 
lean_del_object(v___x_3587_);
v_pendingProducer_3616_ = lean_ctor_get(v_a_3585_, 0);
if (lean_obj_tag(v_pendingProducer_3616_) == 0)
{
lean_object* v_interestWaiter_3617_; lean_object* v_knownSize_3618_; lean_object* v_pendingIncompleteChunk_3619_; lean_object* v_closeError_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3633_; 
v_interestWaiter_3617_ = lean_ctor_get(v_a_3585_, 2);
v_knownSize_3618_ = lean_ctor_get(v_a_3585_, 3);
v_pendingIncompleteChunk_3619_ = lean_ctor_get(v_a_3585_, 4);
v_closeError_3620_ = lean_ctor_get(v_a_3585_, 5);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_a_3585_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; lean_object* v_unused_3635_; 
v_unused_3634_ = lean_ctor_get(v_a_3585_, 1);
lean_dec(v_unused_3634_);
v_unused_3635_ = lean_ctor_get(v_a_3585_, 0);
lean_dec(v_unused_3635_);
v___x_3622_ = v_a_3585_;
v_isShared_3623_ = v_isSharedCheck_3633_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_closeError_3620_);
lean_inc(v_pendingIncompleteChunk_3619_);
lean_inc(v_knownSize_3618_);
lean_inc(v_interestWaiter_3617_);
lean_dec(v_a_3585_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3633_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3627_; 
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v_chunk_3570_);
lean_ctor_set(v___x_3624_, 1, v_a_3572_);
v___x_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 0, v___x_3625_);
v___x_3627_ = v___x_3622_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3625_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v_pendingConsumer_3590_);
lean_ctor_set(v_reuseFailAlloc_3632_, 2, v_interestWaiter_3617_);
lean_ctor_set(v_reuseFailAlloc_3632_, 3, v_knownSize_3618_);
lean_ctor_set(v_reuseFailAlloc_3632_, 4, v_pendingIncompleteChunk_3619_);
lean_ctor_set(v_reuseFailAlloc_3632_, 5, v_closeError_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3632_, sizeof(void*)*6, v_closed_3589_);
v___x_3627_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3628_ = lean_st_ref_swap(v___y_3571_, v___x_3627_);
lean_dec(v___x_3628_);
v___x_3629_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3630_ = lean_unsigned_to_nat(0u);
v___x_3631_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3630_, v_closed_3589_, v___x_3629_, v___f_3573_);
return v___x_3631_;
}
}
}
else
{
lean_object* v___x_3636_; 
lean_dec(v_pendingConsumer_3590_);
lean_dec(v_a_3585_);
lean_dec_ref(v___f_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_chunk_3570_);
v___x_3636_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_3636_;
}
}
}
else
{
lean_object* v___x_3637_; 
lean_del_object(v___x_3587_);
lean_dec(v_a_3585_);
lean_dec_ref(v___f_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_chunk_3570_);
v___x_3637_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_3637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v_chunk_3639_, lean_object* v___y_3640_, lean_object* v_a_3641_, lean_object* v___f_3642_, lean_object* v_x_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v_chunk_3639_, v___y_3640_, v_a_3641_, v___f_3642_, v_x_3643_);
lean_dec(v___y_3640_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_3646_, lean_object* v___f_3647_, lean_object* v_x_3648_){
_start:
{
if (lean_obj_tag(v_x_3648_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3658_; 
lean_dec_ref(v___f_3647_);
v_a_3650_ = lean_ctor_get(v_x_3648_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_x_3648_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3652_ = v_x_3648_;
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v_x_3648_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
return v___x_3656_;
}
}
}
else
{
lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3670_; 
v_isSharedCheck_3670_ = !lean_is_exclusive(v_x_3648_);
if (v_isSharedCheck_3670_ == 0)
{
lean_object* v_unused_3671_; 
v_unused_3671_ = lean_ctor_get(v_x_3648_, 0);
lean_dec(v_unused_3671_);
v___x_3660_ = v_x_3648_;
v_isShared_3661_ = v_isSharedCheck_3670_;
goto v_resetjp_3659_;
}
else
{
lean_dec(v_x_3648_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3670_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
v___x_3662_ = lean_st_ref_get(v___y_3646_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3662_);
v___x_3664_ = v___x_3660_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; lean_object* v___x_3668_; 
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
v___x_3666_ = lean_unsigned_to_nat(0u);
v___x_3667_ = 0;
v___x_3668_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3666_, v___x_3667_, v___x_3665_, v___f_3647_);
return v___x_3668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_3672_, lean_object* v___f_3673_, lean_object* v_x_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_3672_, v___f_3673_, v_x_3674_);
lean_dec(v___y_3672_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_3677_, lean_object* v_a_3678_, lean_object* v___f_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; lean_object* v___f_3683_; lean_object* v___f_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; lean_object* v___x_3687_; 
v___x_3682_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3680_);
lean_inc_n(v___y_3680_, 2);
v___f_3683_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_3683_, 0, v_chunk_3677_);
lean_closure_set(v___f_3683_, 1, v___y_3680_);
lean_closure_set(v___f_3683_, 2, v_a_3678_);
lean_closure_set(v___f_3683_, 3, v___f_3679_);
v___f_3684_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_3684_, 0, v___y_3680_);
lean_closure_set(v___f_3684_, 1, v___f_3683_);
v___x_3685_ = lean_unsigned_to_nat(0u);
v___x_3686_ = 0;
v___x_3687_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3685_, v___x_3686_, v___x_3682_, v___f_3684_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_3688_, lean_object* v_a_3689_, lean_object* v___f_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_3688_, v_a_3689_, v___f_3690_, v___y_3691_);
lean_dec(v___y_3691_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_3699_, lean_object* v___f_3700_, lean_object* v___f_3701_, lean_object* v_stream_3702_, lean_object* v_chunk_3703_, lean_object* v___f_3704_, lean_object* v_x_3705_){
_start:
{
if (lean_obj_tag(v_x_3705_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3715_; 
lean_dec_ref(v___f_3704_);
lean_dec_ref(v_chunk_3703_);
lean_dec_ref(v_stream_3702_);
lean_dec_ref(v___f_3701_);
lean_dec_ref(v___f_3700_);
v_a_3707_ = lean_ctor_get(v_x_3705_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v_x_3705_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3709_ = v_x_3705_;
v_isShared_3710_ = v_isSharedCheck_3715_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v_x_3705_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3715_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
}
}
else
{
lean_object* v_a_3716_; 
v_a_3716_ = lean_ctor_get(v_x_3705_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v_x_3705_, 1);
if (lean_obj_tag(v_a_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v___f_3704_);
lean_dec_ref(v_chunk_3703_);
lean_dec_ref(v_stream_3702_);
lean_dec_ref(v___f_3701_);
lean_dec_ref(v___f_3700_);
v_a_3717_ = lean_ctor_get(v_a_3716_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_a_3716_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3719_ = v_a_3716_;
v_isShared_3720_ = v_isSharedCheck_3725_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v_a_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3725_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
}
}
else
{
lean_object* v_a_3726_; 
v_a_3726_ = lean_ctor_get(v_a_3716_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v_a_3716_, 1);
if (lean_obj_tag(v_a_3726_) == 0)
{
lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
lean_dec_ref(v___f_3704_);
lean_dec_ref(v_chunk_3703_);
lean_dec_ref(v_stream_3702_);
v___x_3727_ = lean_io_promise_result_opt(v_a_3699_);
v___x_3728_ = lean_unsigned_to_nat(0u);
v___x_3729_ = 0;
v___x_3730_ = lean_task_map(v___f_3700_, v___x_3727_, v___x_3728_, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
v___x_3732_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3728_, v___x_3729_, v___x_3731_, v___f_3701_);
return v___x_3732_;
}
else
{
lean_object* v_val_3733_; uint8_t v___x_3734_; 
lean_dec_ref(v___f_3701_);
lean_dec_ref(v___f_3700_);
v_val_3733_ = lean_ctor_get(v_a_3726_, 0);
lean_inc(v_val_3733_);
lean_dec_ref_known(v_a_3726_, 1);
v___x_3734_ = lean_unbox(v_val_3733_);
lean_dec(v_val_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; 
lean_dec_ref(v___f_3704_);
v___x_3735_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3702_, v_chunk_3703_);
return v___x_3735_;
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_dec_ref(v_chunk_3703_);
lean_dec_ref(v_stream_3702_);
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_apply_2(v___f_3704_, v___x_3736_, lean_box(0));
return v___x_3737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_3738_, lean_object* v___f_3739_, lean_object* v___f_3740_, lean_object* v_stream_3741_, lean_object* v_chunk_3742_, lean_object* v___f_3743_, lean_object* v_x_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_3738_, v___f_3739_, v___f_3740_, v_stream_3741_, v_chunk_3742_, v___f_3743_, v_x_3744_);
lean_dec(v_a_3738_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_3747_, lean_object* v___f_3748_, lean_object* v_stream_3749_, lean_object* v___f_3750_, lean_object* v___f_3751_, lean_object* v___f_3752_, lean_object* v_x_3753_){
_start:
{
if (lean_obj_tag(v_x_3753_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3763_; 
lean_dec_ref(v___f_3752_);
lean_dec_ref(v___f_3751_);
lean_dec_ref(v___f_3750_);
lean_dec_ref(v_stream_3749_);
lean_dec_ref(v___f_3748_);
lean_dec_ref(v_chunk_3747_);
v_a_3755_ = lean_ctor_get(v_x_3753_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_x_3753_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3757_ = v_x_3753_;
v_isShared_3758_ = v_isSharedCheck_3763_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v_x_3753_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3763_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
return v___x_3761_;
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___f_3765_; lean_object* v___x_3766_; lean_object* v___f_3767_; lean_object* v___x_3768_; uint8_t v___x_3769_; lean_object* v___x_3770_; 
v_a_3764_ = lean_ctor_get(v_x_3753_, 0);
lean_inc_n(v_a_3764_, 2);
lean_dec_ref_known(v_x_3753_, 1);
lean_inc_ref(v_chunk_3747_);
v___f_3765_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_3765_, 0, v_chunk_3747_);
lean_closure_set(v___f_3765_, 1, v_a_3764_);
lean_closure_set(v___f_3765_, 2, v___f_3748_);
lean_inc_ref(v_stream_3749_);
v___x_3766_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3749_, v___f_3765_);
v___f_3767_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3767_, 0, v_a_3764_);
lean_closure_set(v___f_3767_, 1, v___f_3750_);
lean_closure_set(v___f_3767_, 2, v___f_3751_);
lean_closure_set(v___f_3767_, 3, v_stream_3749_);
lean_closure_set(v___f_3767_, 4, v_chunk_3747_);
lean_closure_set(v___f_3767_, 5, v___f_3752_);
v___x_3768_ = lean_unsigned_to_nat(0u);
v___x_3769_ = 0;
v___x_3770_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3768_, v___x_3769_, v___x_3766_, v___f_3767_);
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_3771_, lean_object* v___f_3772_, lean_object* v_stream_3773_, lean_object* v___f_3774_, lean_object* v___f_3775_, lean_object* v___f_3776_, lean_object* v_x_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_3771_, v___f_3772_, v_stream_3773_, v___f_3774_, v___f_3775_, v___f_3776_, v_x_3777_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_3780_, lean_object* v_chunk_3781_){
_start:
{
lean_object* v___x_3783_; lean_object* v___f_3784_; lean_object* v___f_3785_; lean_object* v___f_3786_; lean_object* v___f_3787_; lean_object* v___f_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; lean_object* v___x_3793_; 
v___x_3783_ = lean_io_promise_new();
v___f_3784_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_3785_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_3786_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_3787_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_3788_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_3788_, 0, v_chunk_3781_);
lean_closure_set(v___f_3788_, 1, v___f_3784_);
lean_closure_set(v___f_3788_, 2, v_stream_3780_);
lean_closure_set(v___f_3788_, 3, v___f_3787_);
lean_closure_set(v___f_3788_, 4, v___f_3786_);
lean_closure_set(v___f_3788_, 5, v___f_3785_);
v___x_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3783_);
v___x_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
v___x_3791_ = lean_unsigned_to_nat(0u);
v___x_3792_ = 0;
v___x_3793_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3791_, v___x_3792_, v___x_3790_, v___f_3788_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_3794_, lean_object* v_chunk_3795_, lean_object* v_a_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3794_, v_chunk_3795_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_3798_, lean_object* v_x_3799_){
_start:
{
if (lean_obj_tag(v_x_3799_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v_stream_3798_);
v_a_3801_ = lean_ctor_get(v_x_3799_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_x_3799_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3803_ = v_x_3799_;
v_isShared_3804_ = v_isSharedCheck_3809_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v_x_3799_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3809_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3807_; 
v___x_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
return v___x_3807_;
}
}
}
else
{
lean_object* v_a_3810_; 
v_a_3810_ = lean_ctor_get(v_x_3799_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v_x_3799_, 1);
if (lean_obj_tag(v_a_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_stream_3798_);
v_a_3811_ = lean_ctor_get(v_a_3810_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_a_3810_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3813_ = v_a_3810_;
v_isShared_3814_ = v_isSharedCheck_3819_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v_a_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3819_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3817_; 
v___x_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
return v___x_3817_;
}
}
}
else
{
lean_object* v_a_3820_; 
v_a_3820_ = lean_ctor_get(v_a_3810_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v_a_3810_, 1);
if (lean_obj_tag(v_a_3820_) == 0)
{
lean_object* v___x_3821_; 
lean_dec_ref(v_stream_3798_);
v___x_3821_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3821_;
}
else
{
lean_object* v_val_3822_; lean_object* v_data_3823_; lean_object* v_extensions_3824_; uint8_t v___x_3825_; 
v_val_3822_ = lean_ctor_get(v_a_3820_, 0);
lean_inc(v_val_3822_);
lean_dec_ref_known(v_a_3820_, 1);
v_data_3823_ = lean_ctor_get(v_val_3822_, 0);
v_extensions_3824_ = lean_ctor_get(v_val_3822_, 1);
v___x_3825_ = l_ByteArray_isEmpty(v_data_3823_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; 
v___x_3826_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3798_, v_val_3822_);
return v___x_3826_;
}
else
{
lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v___x_3827_ = lean_array_get_size(v_extensions_3824_);
v___x_3828_ = lean_unsigned_to_nat(0u);
v___x_3829_ = lean_nat_dec_eq(v___x_3827_, v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; 
v___x_3830_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3798_, v_val_3822_);
return v___x_3830_;
}
else
{
lean_object* v___x_3831_; 
lean_dec(v_val_3822_);
lean_dec_ref(v_stream_3798_);
v___x_3831_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3831_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object* v_stream_3832_, lean_object* v_x_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_3832_, v_x_3833_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object* v_stream_3836_, lean_object* v_chunk_3837_, uint8_t v_incomplete_3838_){
_start:
{
lean_object* v___x_3840_; lean_object* v___f_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; uint8_t v___x_3845_; lean_object* v___x_3846_; 
lean_inc_ref(v_stream_3836_);
v___x_3840_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3836_, v_chunk_3837_, v_incomplete_3838_);
v___f_3841_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3841_, 0, v_stream_3836_);
v___x_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
v___x_3844_ = lean_unsigned_to_nat(0u);
v___x_3845_ = 0;
v___x_3846_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3844_, v___x_3845_, v___x_3843_, v___f_3841_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object* v_stream_3847_, lean_object* v_chunk_3848_, lean_object* v_incomplete_3849_, lean_object* v_a_3850_){
_start:
{
uint8_t v_incomplete_boxed_3851_; lean_object* v_res_3852_; 
v_incomplete_boxed_3851_ = lean_unbox(v_incomplete_3849_);
v_res_3852_ = l_Std_Http_Body_Stream_send(v_stream_3847_, v_chunk_3848_, v_incomplete_boxed_3851_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object* v_x_3853_){
_start:
{
uint8_t v___y_3856_; 
if (lean_obj_tag(v_x_3853_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3868_; 
v_a_3860_ = lean_ctor_get(v_x_3853_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_x_3853_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3862_ = v_x_3853_;
v_isShared_3863_ = v_isSharedCheck_3868_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v_x_3853_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3868_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
return v___x_3866_;
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v_pendingConsumer_3870_; 
v_a_3869_ = lean_ctor_get(v_x_3853_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v_x_3853_, 1);
v_pendingConsumer_3870_ = lean_ctor_get(v_a_3869_, 1);
lean_inc(v_pendingConsumer_3870_);
lean_dec(v_a_3869_);
if (lean_obj_tag(v_pendingConsumer_3870_) == 0)
{
uint8_t v___x_3871_; 
v___x_3871_ = 0;
v___y_3856_ = v___x_3871_;
goto v___jp_3855_;
}
else
{
uint8_t v___x_3872_; 
lean_dec_ref_known(v_pendingConsumer_3870_, 1);
v___x_3872_ = 1;
v___y_3856_ = v___x_3872_;
goto v___jp_3855_;
}
}
v___jp_3855_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3857_ = lean_box(v___y_3856_);
v___x_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
v___x_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
return v___x_3859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object* v_x_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object* v_a_3877_){
_start:
{
lean_object* v___x_3879_; lean_object* v___f_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; uint8_t v___x_3884_; lean_object* v___x_3885_; 
v___x_3879_ = lean_st_ref_get(v_a_3877_);
v___f_3880_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = 0;
v___x_3885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3883_, v___x_3884_, v___x_3882_, v___f_3880_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object* v_a_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_3886_);
lean_dec(v_a_3886_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object* v___y_3889_, lean_object* v_x_3890_){
_start:
{
if (lean_obj_tag(v_x_3890_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3900_; 
v_a_3892_ = lean_ctor_get(v_x_3890_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v_x_3890_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3894_ = v_x_3890_;
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v_x_3890_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; 
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
}
}
else
{
lean_object* v___x_3901_; 
lean_dec_ref_known(v_x_3890_, 1);
v___x_3901_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_3889_);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object* v___y_3902_, lean_object* v_x_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_3902_, v_x_3903_);
lean_dec(v___y_3902_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; lean_object* v___f_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; lean_object* v___x_3912_; 
v___x_3908_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3906_);
lean_inc(v___y_3906_);
v___f_3909_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3909_, 0, v___y_3906_);
v___x_3910_ = lean_unsigned_to_nat(0u);
v___x_3911_ = 0;
v___x_3912_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3910_, v___x_3911_, v___x_3908_, v___f_3909_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_3913_);
lean_dec(v___y_3913_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object* v_stream_3917_){
_start:
{
lean_object* v___f_3919_; lean_object* v___x_3920_; 
v___f_3919_ = ((lean_object*)(l_Std_Http_Body_Stream_hasInterest___closed__0));
v___x_3920_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3917_, v___f_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object* v_stream_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Std_Http_Body_Stream_hasInterest(v_stream_3921_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object* v_lose_3924_, lean_object* v___y_3925_, uint8_t v___x_3926_, lean_object* v_promise_3927_, lean_object* v_x_3928_){
_start:
{
if (lean_obj_tag(v_x_3928_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v_lose_3924_);
v_a_3930_ = lean_ctor_get(v_x_3928_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_x_3928_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3932_ = v_x_3928_;
v_isShared_3933_ = v_isSharedCheck_3938_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v_x_3928_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3938_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3936_; 
v___x_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3935_);
return v___x_3936_;
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3952_; 
v_a_3939_ = lean_ctor_get(v_x_3928_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_x_3928_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3941_ = v_x_3928_;
v_isShared_3942_ = v_isSharedCheck_3952_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v_x_3928_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3952_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
uint8_t v___x_3943_; 
v___x_3943_ = lean_unbox(v_a_3939_);
lean_dec(v_a_3939_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; 
lean_del_object(v___x_3941_);
lean_inc(v___y_3925_);
v___x_3944_ = lean_apply_2(v_lose_3924_, v___y_3925_, lean_box(0));
return v___x_3944_;
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3947_; 
lean_dec_ref(v_lose_3924_);
v___x_3945_ = lean_box(v___x_3926_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3945_);
v___x_3947_ = v___x_3941_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3948_ = lean_io_promise_resolve(v___x_3947_, v_promise_3927_);
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
return v___x_3950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object* v_lose_3953_, lean_object* v___y_3954_, lean_object* v___x_3955_, lean_object* v_promise_3956_, lean_object* v_x_3957_, lean_object* v___y_3958_){
_start:
{
uint8_t v___x_4677__boxed_3959_; lean_object* v_res_3960_; 
v___x_4677__boxed_3959_ = lean_unbox(v___x_3955_);
v_res_3960_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_3953_, v___y_3954_, v___x_4677__boxed_3959_, v_promise_3956_, v_x_3957_);
lean_dec(v_promise_3956_);
lean_dec(v___y_3954_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_3961_, lean_object* v_lose_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_finished_3965_; lean_object* v_promise_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___f_3970_; uint8_t v___y_3972_; uint8_t v___x_3981_; 
v_finished_3965_ = lean_ctor_get(v_w_3961_, 0);
lean_inc(v_finished_3965_);
v_promise_3966_ = lean_ctor_get(v_w_3961_, 1);
lean_inc(v_promise_3966_);
lean_dec_ref(v_w_3961_);
v___x_3967_ = lean_st_ref_take(v_finished_3965_);
v___x_3968_ = 0;
v___x_3969_ = lean_box(v___x_3968_);
lean_inc(v___y_3963_);
v___f_3970_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3970_, 0, v_lose_3962_);
lean_closure_set(v___f_3970_, 1, v___y_3963_);
lean_closure_set(v___f_3970_, 2, v___x_3969_);
lean_closure_set(v___f_3970_, 3, v_promise_3966_);
v___x_3981_ = lean_unbox(v___x_3967_);
lean_dec(v___x_3967_);
if (v___x_3981_ == 0)
{
uint8_t v___x_3982_; 
v___x_3982_ = 1;
v___y_3972_ = v___x_3982_;
goto v___jp_3971_;
}
else
{
v___y_3972_ = v___x_3968_;
goto v___jp_3971_;
}
v___jp_3971_:
{
uint8_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3973_ = 1;
v___x_3974_ = lean_box(v___x_3973_);
v___x_3975_ = lean_st_ref_put(v_finished_3965_, v___x_3974_);
lean_dec(v_finished_3965_);
v___x_3976_ = lean_box(v___y_3972_);
v___x_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
v___x_3979_ = lean_unsigned_to_nat(0u);
v___x_3980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3979_, v___x_3968_, v___x_3978_, v___f_3970_);
return v___x_3980_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object* v_w_3983_, lean_object* v_lose_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_3983_, v_lose_3984_, v___y_3985_);
lean_dec(v___y_3985_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object* v_w_3988_, lean_object* v_lose_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v_finished_3992_; lean_object* v_promise_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; lean_object* v___x_3996_; lean_object* v___f_3997_; uint8_t v___y_3999_; uint8_t v___x_4008_; 
v_finished_3992_ = lean_ctor_get(v_w_3988_, 0);
lean_inc(v_finished_3992_);
v_promise_3993_ = lean_ctor_get(v_w_3988_, 1);
lean_inc(v_promise_3993_);
lean_dec_ref(v_w_3988_);
v___x_3994_ = lean_st_ref_take(v_finished_3992_);
v___x_3995_ = 1;
v___x_3996_ = lean_box(v___x_3995_);
lean_inc(v___y_3990_);
v___f_3997_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3997_, 0, v_lose_3989_);
lean_closure_set(v___f_3997_, 1, v___y_3990_);
lean_closure_set(v___f_3997_, 2, v___x_3996_);
lean_closure_set(v___f_3997_, 3, v_promise_3993_);
v___x_4008_ = lean_unbox(v___x_3994_);
lean_dec(v___x_3994_);
if (v___x_4008_ == 0)
{
v___y_3999_ = v___x_3995_;
goto v___jp_3998_;
}
else
{
uint8_t v___x_4009_; 
v___x_4009_ = 0;
v___y_3999_ = v___x_4009_;
goto v___jp_3998_;
}
v___jp_3998_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; lean_object* v___x_4007_; 
v___x_4000_ = lean_box(v___x_3995_);
v___x_4001_ = lean_st_ref_put(v_finished_3992_, v___x_4000_);
lean_dec(v_finished_3992_);
v___x_4002_ = lean_box(v___y_3999_);
v___x_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
v___x_4005_ = lean_unsigned_to_nat(0u);
v___x_4006_ = 0;
v___x_4007_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4005_, v___x_4006_, v___x_4004_, v___f_3997_);
return v___x_4007_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_4010_, lean_object* v_lose_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_4010_, v_lose_4011_, v___y_4012_);
lean_dec(v___y_4012_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_4031_){
_start:
{
if (lean_obj_tag(v_x_4031_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4041_; 
v_a_4033_ = lean_ctor_get(v_x_4031_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_x_4031_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4035_ = v_x_4031_;
v_isShared_4036_ = v_isSharedCheck_4041_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v_x_4031_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4041_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
lean_object* v___x_4039_; 
v___x_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
return v___x_4039_;
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v_pendingConsumer_4043_; 
v_a_4042_ = lean_ctor_get(v_x_4031_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v_x_4031_, 1);
v_pendingConsumer_4043_ = lean_ctor_get(v_a_4042_, 1);
if (lean_obj_tag(v_pendingConsumer_4043_) == 0)
{
uint8_t v_closed_4044_; 
v_closed_4044_ = lean_ctor_get_uint8(v_a_4042_, sizeof(void*)*6);
lean_dec(v_a_4042_);
if (v_closed_4044_ == 0)
{
lean_object* v___x_4045_; 
v___x_4045_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_4045_;
}
else
{
lean_object* v___x_4046_; 
v___x_4046_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_4046_;
}
}
else
{
lean_object* v___x_4047_; 
lean_dec(v_a_4042_);
v___x_4047_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_4047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_4048_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_4058_, lean_object* v___y_4059_, lean_object* v_x_4060_){
_start:
{
if (lean_obj_tag(v_x_4060_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4070_; 
lean_dec_ref(v_waiter_4058_);
v_a_4062_ = lean_ctor_get(v_x_4060_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_x_4060_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4064_ = v_x_4060_;
v_isShared_4065_ = v_isSharedCheck_4070_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v_x_4060_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4070_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v_pendingConsumer_4072_; 
v_a_4071_ = lean_ctor_get(v_x_4060_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v_x_4060_, 1);
v_pendingConsumer_4072_ = lean_ctor_get(v_a_4071_, 1);
lean_inc(v_pendingConsumer_4072_);
if (lean_obj_tag(v_pendingConsumer_4072_) == 0)
{
uint8_t v_closed_4073_; 
v_closed_4073_ = lean_ctor_get_uint8(v_a_4071_, sizeof(void*)*6);
if (v_closed_4073_ == 0)
{
lean_object* v_interestWaiter_4074_; 
v_interestWaiter_4074_ = lean_ctor_get(v_a_4071_, 2);
if (lean_obj_tag(v_interestWaiter_4074_) == 0)
{
lean_object* v_pendingProducer_4075_; lean_object* v_knownSize_4076_; lean_object* v_pendingIncompleteChunk_4077_; lean_object* v_closeError_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4088_; 
v_pendingProducer_4075_ = lean_ctor_get(v_a_4071_, 0);
v_knownSize_4076_ = lean_ctor_get(v_a_4071_, 3);
v_pendingIncompleteChunk_4077_ = lean_ctor_get(v_a_4071_, 4);
v_closeError_4078_ = lean_ctor_get(v_a_4071_, 5);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_a_4071_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; lean_object* v_unused_4090_; 
v_unused_4089_ = lean_ctor_get(v_a_4071_, 2);
lean_dec(v_unused_4089_);
v_unused_4090_ = lean_ctor_get(v_a_4071_, 1);
lean_dec(v_unused_4090_);
v___x_4080_ = v_a_4071_;
v_isShared_4081_ = v_isSharedCheck_4088_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_closeError_4078_);
lean_inc(v_pendingIncompleteChunk_4077_);
lean_inc(v_knownSize_4076_);
lean_inc(v_pendingProducer_4075_);
lean_dec(v_a_4071_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4088_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4084_; 
v___x_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4082_, 0, v_waiter_4058_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 2, v___x_4082_);
v___x_4084_ = v___x_4080_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_pendingProducer_4075_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_pendingConsumer_4072_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v___x_4082_);
lean_ctor_set(v_reuseFailAlloc_4087_, 3, v_knownSize_4076_);
lean_ctor_set(v_reuseFailAlloc_4087_, 4, v_pendingIncompleteChunk_4077_);
lean_ctor_set(v_reuseFailAlloc_4087_, 5, v_closeError_4078_);
lean_ctor_set_uint8(v_reuseFailAlloc_4087_, sizeof(void*)*6, v_closed_4073_);
v___x_4084_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = lean_st_ref_swap(v___y_4059_, v___x_4084_);
lean_dec(v___x_4085_);
v___x_4086_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4086_;
}
}
}
else
{
lean_object* v___x_4091_; 
lean_dec(v_a_4071_);
lean_dec_ref(v_waiter_4058_);
v___x_4091_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_4091_;
}
}
else
{
lean_object* v___f_4092_; lean_object* v___x_4093_; 
lean_dec(v_a_4071_);
v___f_4092_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4093_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_4058_, v___f_4092_, v___y_4059_);
return v___x_4093_;
}
}
else
{
lean_object* v___f_4094_; lean_object* v___x_4095_; 
lean_dec_ref_known(v_pendingConsumer_4072_, 1);
lean_dec(v_a_4071_);
v___f_4094_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4095_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_4058_, v___f_4094_, v___y_4059_);
return v___x_4095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_4096_, lean_object* v___y_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_4096_, v___y_4097_, v_x_4098_);
lean_dec(v___y_4097_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_4101_, lean_object* v___f_4102_, lean_object* v_x_4103_){
_start:
{
if (lean_obj_tag(v_x_4103_) == 0)
{
lean_object* v___x_4105_; 
lean_dec_ref(v___f_4102_);
v___x_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4105_, 0, v_x_4103_);
return v___x_4105_;
}
else
{
lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4117_; 
v_isSharedCheck_4117_ = !lean_is_exclusive(v_x_4103_);
if (v_isSharedCheck_4117_ == 0)
{
lean_object* v_unused_4118_; 
v_unused_4118_ = lean_ctor_get(v_x_4103_, 0);
lean_dec(v_unused_4118_);
v___x_4107_ = v_x_4103_;
v_isShared_4108_ = v_isSharedCheck_4117_;
goto v_resetjp_4106_;
}
else
{
lean_dec(v_x_4103_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4117_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4109_; lean_object* v___x_4111_; 
v___x_4109_ = lean_st_ref_get(v___y_4101_);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 0, v___x_4109_);
v___x_4111_ = v___x_4107_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4109_);
v___x_4111_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; lean_object* v___x_4115_; 
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = 0;
v___x_4115_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4113_, v___x_4114_, v___x_4112_, v___f_4102_);
return v___x_4115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_4119_, lean_object* v___f_4120_, lean_object* v_x_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_4119_, v___f_4120_, v_x_4121_);
lean_dec(v___y_4119_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; lean_object* v___f_4128_; lean_object* v___f_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; lean_object* v___x_4132_; 
v___x_4127_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4125_);
lean_inc_n(v___y_4125_, 2);
v___f_4128_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_4128_, 0, v_waiter_4124_);
lean_closure_set(v___f_4128_, 1, v___y_4125_);
v___f_4129_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4129_, 0, v___y_4125_);
lean_closure_set(v___f_4129_, 1, v___f_4128_);
v___x_4130_ = lean_unsigned_to_nat(0u);
v___x_4131_ = 0;
v___x_4132_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4130_, v___x_4131_, v___x_4127_, v___f_4129_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_4133_, v___y_4134_);
lean_dec(v___y_4134_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_4137_, lean_object* v_waiter_4138_){
_start:
{
lean_object* v___f_4140_; lean_object* v___x_4141_; 
v___f_4140_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4140_, 0, v_waiter_4138_);
v___x_4141_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_4137_, v___f_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_4142_, lean_object* v_waiter_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_4142_, v_waiter_4143_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_4146_, lean_object* v___f_4147_, lean_object* v_x_4148_){
_start:
{
if (lean_obj_tag(v_x_4148_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4158_; 
lean_dec_ref(v___f_4147_);
v_a_4150_ = lean_ctor_get(v_x_4148_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v_x_4148_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4152_ = v_x_4148_;
v_isShared_4153_ = v_isSharedCheck_4158_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v_x_4148_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4158_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
lean_object* v___x_4156_; 
v___x_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
return v___x_4156_;
}
}
}
else
{
lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4170_; 
v_isSharedCheck_4170_ = !lean_is_exclusive(v_x_4148_);
if (v_isSharedCheck_4170_ == 0)
{
lean_object* v_unused_4171_; 
v_unused_4171_ = lean_ctor_get(v_x_4148_, 0);
lean_dec(v_unused_4171_);
v___x_4160_ = v_x_4148_;
v_isShared_4161_ = v_isSharedCheck_4170_;
goto v_resetjp_4159_;
}
else
{
lean_dec(v_x_4148_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4170_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4162_; lean_object* v___x_4164_; 
v___x_4162_ = lean_st_ref_get(v___y_4146_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v___x_4162_);
v___x_4164_ = v___x_4160_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; uint8_t v___x_4167_; lean_object* v___x_4168_; 
v___x_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
v___x_4166_ = lean_unsigned_to_nat(0u);
v___x_4167_ = 0;
v___x_4168_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4166_, v___x_4167_, v___x_4165_, v___f_4147_);
return v___x_4168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_4172_, lean_object* v___f_4173_, lean_object* v_x_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_4172_, v___f_4173_, v_x_4174_);
lean_dec(v___y_4172_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v___x_4180_; lean_object* v___f_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; lean_object* v___x_4184_; 
v___x_4180_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4178_);
lean_inc(v___y_4178_);
v___f_4181_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_4181_, 0, v___y_4178_);
lean_closure_set(v___f_4181_, 1, v___f_4177_);
v___x_4182_ = lean_unsigned_to_nat(0u);
v___x_4183_ = 0;
v___x_4184_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4182_, v___x_4183_, v___x_4180_, v___f_4181_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_4185_, v___y_4186_);
lean_dec(v___y_4186_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_4192_){
_start:
{
lean_object* v___f_4193_; lean_object* v___f_4194_; lean_object* v___f_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___f_4193_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_4192_, 2);
v___f_4194_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_4194_, 0, v_stream_4192_);
v___f_4195_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_4196_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4196_, 0, lean_box(0));
lean_closure_set(v___x_4196_, 1, lean_box(0));
lean_closure_set(v___x_4196_, 2, v_stream_4192_);
lean_closure_set(v___x_4196_, 3, v___f_4195_);
v___x_4197_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4197_, 0, lean_box(0));
lean_closure_set(v___x_4197_, 1, lean_box(0));
lean_closure_set(v___x_4197_, 2, v_stream_4192_);
lean_closure_set(v___x_4197_, 3, v___f_4193_);
v___x_4198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4196_);
lean_ctor_set(v___x_4198_, 1, v___f_4194_);
lean_ctor_set(v___x_4198_, 2, v___x_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v___x_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v___x_4202_; lean_object* v_pendingProducer_4203_; lean_object* v_pendingConsumer_4204_; lean_object* v_interestWaiter_4205_; uint8_t v_closed_4206_; lean_object* v_pendingIncompleteChunk_4207_; lean_object* v_closeError_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4217_; 
v___x_4202_ = lean_st_ref_take(v___y_4200_);
v_pendingProducer_4203_ = lean_ctor_get(v___x_4202_, 0);
v_pendingConsumer_4204_ = lean_ctor_get(v___x_4202_, 1);
v_interestWaiter_4205_ = lean_ctor_get(v___x_4202_, 2);
v_closed_4206_ = lean_ctor_get_uint8(v___x_4202_, sizeof(void*)*6);
v_pendingIncompleteChunk_4207_ = lean_ctor_get(v___x_4202_, 4);
v_closeError_4208_ = lean_ctor_get(v___x_4202_, 5);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4217_ == 0)
{
lean_object* v_unused_4218_; 
v_unused_4218_ = lean_ctor_get(v___x_4202_, 3);
lean_dec(v_unused_4218_);
v___x_4210_ = v___x_4202_;
v_isShared_4211_ = v_isSharedCheck_4217_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_closeError_4208_);
lean_inc(v_pendingIncompleteChunk_4207_);
lean_inc(v_interestWaiter_4205_);
lean_inc(v_pendingConsumer_4204_);
lean_inc(v_pendingProducer_4203_);
lean_dec(v___x_4202_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4217_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 3, v___x_4199_);
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_pendingProducer_4203_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_pendingConsumer_4204_);
lean_ctor_set(v_reuseFailAlloc_4216_, 2, v_interestWaiter_4205_);
lean_ctor_set(v_reuseFailAlloc_4216_, 3, v___x_4199_);
lean_ctor_set(v_reuseFailAlloc_4216_, 4, v_pendingIncompleteChunk_4207_);
lean_ctor_set(v_reuseFailAlloc_4216_, 5, v_closeError_4208_);
lean_ctor_set_uint8(v_reuseFailAlloc_4216_, sizeof(void*)*6, v_closed_4206_);
v___x_4213_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = lean_st_ref_put(v___y_4200_, v___x_4213_);
v___x_4215_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0___boxed(lean_object* v___x_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Std_Http_Body_stream___lam__0(v___x_4219_, v___y_4220_);
lean_dec(v___y_4220_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_x_4223_, lean_object* v_x_4224_){
_start:
{
if (lean_obj_tag(v_x_4224_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4234_; 
lean_dec_ref(v_x_4223_);
v_a_4226_ = lean_ctor_get(v_x_4224_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_x_4224_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4228_ = v_x_4224_;
v_isShared_4229_ = v_isSharedCheck_4234_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v_x_4224_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4234_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
lean_object* v___x_4232_; 
v___x_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
return v___x_4232_;
}
}
}
else
{
lean_object* v___x_4235_; 
lean_dec_ref_known(v_x_4224_, 1);
v___x_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4235_, 0, v_x_4223_);
return v___x_4235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_x_4236_, lean_object* v_x_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Std_Http_Body_stream___lam__1(v_x_4236_, v_x_4237_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v_a_4240_, lean_object* v_x_4241_){
_start:
{
if (lean_obj_tag(v_x_4241_) == 0)
{
lean_object* v___x_4243_; 
lean_dec_ref(v_a_4240_);
v___x_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4243_, 0, v_x_4241_);
return v___x_4243_;
}
else
{
lean_object* v___x_4244_; 
lean_dec_ref_known(v_x_4241_, 1);
v___x_4244_ = l_Std_Http_Body_Stream_close(v_a_4240_);
return v___x_4244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v_a_4245_, lean_object* v_x_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Std_Http_Body_stream___lam__2(v_a_4245_, v_x_4246_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_a_4249_, lean_object* v_x_4250_){
_start:
{
if (lean_obj_tag(v_x_4250_) == 0)
{
lean_object* v_a_4252_; lean_object* v___x_4253_; 
v_a_4252_ = lean_ctor_get(v_x_4250_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v_x_4250_, 1);
v___x_4253_ = l_Std_Http_Body_Stream_closeWithError(v_a_4249_, v_a_4252_);
return v___x_4253_;
}
else
{
lean_object* v___x_4254_; 
lean_dec_ref(v_a_4249_);
v___x_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4254_, 0, v_x_4250_);
return v___x_4254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_a_4255_, lean_object* v_x_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Std_Http_Body_stream___lam__3(v_a_4255_, v_x_4256_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_4259_, lean_object* v_a_4260_, lean_object* v___x_4261_, lean_object* v___f_4262_, lean_object* v___f_4263_){
_start:
{
lean_object* v___x_4265_; uint8_t v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4265_ = lean_apply_2(v_gen_4259_, v_a_4260_, lean_box(0));
v___x_4266_ = 0;
lean_inc(v___x_4261_);
v___x_4267_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4261_, v___x_4266_, v___x_4265_, v___f_4262_);
v___x_4268_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4261_, v___x_4266_, v___x_4267_, v___f_4263_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_4269_, lean_object* v_a_4270_, lean_object* v___x_4271_, lean_object* v___f_4272_, lean_object* v___f_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Std_Http_Body_stream___lam__4(v_gen_4269_, v_a_4270_, v___x_4271_, v___f_4272_, v___f_4273_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5(lean_object* v_gen_4276_, lean_object* v_a_4277_, lean_object* v___f_4278_, lean_object* v___f_4279_, lean_object* v___f_4280_, lean_object* v_x_4281_){
_start:
{
if (lean_obj_tag(v_x_4281_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref(v___f_4280_);
lean_dec_ref(v___f_4279_);
lean_dec_ref(v___f_4278_);
lean_dec_ref(v_a_4277_);
lean_dec_ref(v_gen_4276_);
v_a_4283_ = lean_ctor_get(v_x_4281_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_x_4281_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4285_ = v_x_4281_;
v_isShared_4286_ = v_isSharedCheck_4291_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v_x_4281_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4291_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4289_; 
v___x_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
return v___x_4289_;
}
}
}
else
{
lean_object* v___x_4292_; lean_object* v___f_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; lean_object* v___x_4297_; 
lean_dec_ref_known(v_x_4281_, 1);
v___x_4292_ = lean_unsigned_to_nat(0u);
v___f_4293_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 6, 5);
lean_closure_set(v___f_4293_, 0, v_gen_4276_);
lean_closure_set(v___f_4293_, 1, v_a_4277_);
lean_closure_set(v___f_4293_, 2, v___x_4292_);
lean_closure_set(v___f_4293_, 3, v___f_4278_);
lean_closure_set(v___f_4293_, 4, v___f_4279_);
v___x_4294_ = lean_io_as_task(v___f_4293_, v___x_4292_);
lean_dec_ref(v___x_4294_);
v___x_4295_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4296_ = 0;
v___x_4297_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4292_, v___x_4296_, v___x_4295_, v___f_4280_);
return v___x_4297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object* v_gen_4298_, lean_object* v_a_4299_, lean_object* v___f_4300_, lean_object* v___f_4301_, lean_object* v___f_4302_, lean_object* v_x_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Std_Http_Body_stream___lam__5(v_gen_4298_, v_a_4299_, v___f_4300_, v___f_4301_, v___f_4302_, v_x_4303_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6(lean_object* v_gen_4310_, lean_object* v_x_4311_){
_start:
{
if (lean_obj_tag(v_x_4311_) == 0)
{
lean_object* v___x_4313_; 
lean_dec_ref(v_gen_4310_);
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v_x_4311_);
return v___x_4313_;
}
else
{
lean_object* v_a_4314_; lean_object* v___f_4315_; lean_object* v___x_4316_; lean_object* v___f_4317_; lean_object* v___f_4318_; lean_object* v___f_4319_; lean_object* v___f_4320_; lean_object* v___x_4321_; uint8_t v___x_4322_; lean_object* v___x_4323_; 
v_a_4314_ = lean_ctor_get(v_x_4311_, 0);
lean_inc_n(v_a_4314_, 4);
v___f_4315_ = ((lean_object*)(l_Std_Http_Body_stream___lam__6___closed__1));
v___x_4316_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4314_, v___f_4315_);
v___f_4317_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4317_, 0, v_x_4311_);
v___f_4318_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4318_, 0, v_a_4314_);
v___f_4319_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4319_, 0, v_a_4314_);
v___f_4320_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__5___boxed), 7, 5);
lean_closure_set(v___f_4320_, 0, v_gen_4310_);
lean_closure_set(v___f_4320_, 1, v_a_4314_);
lean_closure_set(v___f_4320_, 2, v___f_4318_);
lean_closure_set(v___f_4320_, 3, v___f_4319_);
lean_closure_set(v___f_4320_, 4, v___f_4317_);
v___x_4321_ = lean_unsigned_to_nat(0u);
v___x_4322_ = 0;
v___x_4323_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4321_, v___x_4322_, v___x_4316_, v___f_4320_);
return v___x_4323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object* v_gen_4324_, lean_object* v_x_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Std_Http_Body_stream___lam__6(v_gen_4324_, v_x_4325_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object* v_gen_4328_){
_start:
{
lean_object* v___x_4330_; lean_object* v___f_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; lean_object* v___x_4334_; 
v___x_4330_ = l_Std_Http_Body_mkStream();
v___f_4331_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4331_, 0, v_gen_4328_);
v___x_4332_ = lean_unsigned_to_nat(0u);
v___x_4333_ = 0;
v___x_4334_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4332_, v___x_4333_, v___x_4330_, v___f_4331_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_Std_Http_Body_stream(v_gen_4335_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1(lean_object* v___x_4338_, lean_object* v_content_4339_, lean_object* v_s_4340_, lean_object* v_x_4341_){
_start:
{
if (lean_obj_tag(v_x_4341_) == 0)
{
lean_object* v___x_4343_; 
lean_dec_ref(v_s_4340_);
lean_dec_ref(v_content_4339_);
v___x_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4343_, 0, v_x_4341_);
return v___x_4343_;
}
else
{
lean_object* v___x_4344_; uint8_t v___x_4345_; 
lean_dec_ref_known(v_x_4341_, 1);
v___x_4344_ = lean_unsigned_to_nat(0u);
v___x_4345_ = lean_nat_dec_lt(v___x_4344_, v___x_4338_);
if (v___x_4345_ == 0)
{
lean_object* v___x_4346_; 
lean_dec_ref(v_s_4340_);
lean_dec_ref(v_content_4339_);
v___x_4346_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4346_;
}
else
{
lean_object* v___x_4347_; uint8_t v___x_4348_; lean_object* v___x_4349_; 
v___x_4347_ = l_Std_Http_Chunk_ofByteArray(v_content_4339_);
v___x_4348_ = 0;
v___x_4349_ = l_Std_Http_Body_Stream_send(v_s_4340_, v___x_4347_, v___x_4348_);
return v___x_4349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1___boxed(lean_object* v___x_4350_, lean_object* v_content_4351_, lean_object* v_s_4352_, lean_object* v_x_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l_Std_Http_Body_fromBytes___lam__1(v___x_4350_, v_content_4351_, v_s_4352_, v_x_4353_);
lean_dec(v___x_4350_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v_content_4356_, lean_object* v_s_4357_){
_start:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___f_4362_; lean_object* v___x_4363_; lean_object* v___f_4364_; lean_object* v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; 
v___x_4359_ = lean_byte_array_size(v_content_4356_);
v___x_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
v___x_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
v___f_4362_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4362_, 0, v___x_4361_);
lean_inc_ref(v_s_4357_);
v___x_4363_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_4357_, v___f_4362_);
v___f_4364_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4364_, 0, v___x_4359_);
lean_closure_set(v___f_4364_, 1, v_content_4356_);
lean_closure_set(v___f_4364_, 2, v_s_4357_);
v___x_4365_ = lean_unsigned_to_nat(0u);
v___x_4366_ = 0;
v___x_4367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4365_, v___x_4366_, v___x_4363_, v___f_4364_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v_content_4368_, lean_object* v_s_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Std_Http_Body_fromBytes___lam__0(v_content_4368_, v_s_4369_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_4372_){
_start:
{
lean_object* v___f_4374_; lean_object* v___x_4375_; 
v___f_4374_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4374_, 0, v_content_4372_);
v___x_4375_ = l_Std_Http_Body_stream(v___f_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Std_Http_Body_fromBytes(v_content_4376_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_a_4379_, lean_object* v___f_4380_, lean_object* v_x_4381_){
_start:
{
if (lean_obj_tag(v_x_4381_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4391_; 
lean_dec_ref(v___f_4380_);
lean_dec_ref(v_a_4379_);
v_a_4383_ = lean_ctor_get(v_x_4381_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v_x_4381_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4385_ = v_x_4381_;
v_isShared_4386_ = v_isSharedCheck_4391_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v_x_4381_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4391_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4389_; 
v___x_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
return v___x_4389_;
}
}
}
else
{
lean_object* v___x_4392_; lean_object* v___x_4393_; uint8_t v___x_4394_; lean_object* v___x_4395_; 
lean_dec_ref_known(v_x_4381_, 1);
v___x_4392_ = l_Std_Http_Body_Stream_close(v_a_4379_);
v___x_4393_ = lean_unsigned_to_nat(0u);
v___x_4394_ = 0;
v___x_4395_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4393_, v___x_4394_, v___x_4392_, v___f_4380_);
return v___x_4395_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_a_4396_, lean_object* v___f_4397_, lean_object* v_x_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_Std_Http_Body_empty___lam__2(v_a_4396_, v___f_4397_, v_x_4398_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0(lean_object* v_x_4407_){
_start:
{
if (lean_obj_tag(v_x_4407_) == 0)
{
lean_object* v___x_4409_; 
v___x_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4409_, 0, v_x_4407_);
return v___x_4409_;
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4411_; lean_object* v___f_4412_; lean_object* v___x_4413_; lean_object* v___f_4414_; lean_object* v___f_4415_; uint8_t v___x_4416_; lean_object* v___x_4417_; 
v_a_4410_ = lean_ctor_get(v_x_4407_, 0);
lean_inc_n(v_a_4410_, 2);
v___x_4411_ = lean_unsigned_to_nat(0u);
v___f_4412_ = ((lean_object*)(l_Std_Http_Body_empty___lam__0___closed__2));
v___x_4413_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4410_, v___f_4412_);
v___f_4414_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4414_, 0, v_x_4407_);
v___f_4415_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4415_, 0, v_a_4410_);
lean_closure_set(v___f_4415_, 1, v___f_4414_);
v___x_4416_ = 0;
v___x_4417_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4411_, v___x_4416_, v___x_4413_, v___f_4415_);
return v___x_4417_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0___boxed(lean_object* v_x_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l_Std_Http_Body_empty___lam__0(v_x_4418_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___x_4423_; lean_object* v___f_4424_; lean_object* v___x_4425_; uint8_t v___x_4426_; lean_object* v___x_4427_; 
v___x_4423_ = l_Std_Http_Body_mkStream();
v___f_4424_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_4425_ = lean_unsigned_to_nat(0u);
v___x_4426_ = 0;
v___x_4427_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4425_, v___x_4426_, v___x_4423_, v___f_4424_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Std_Http_Body_empty();
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_4452_, lean_object* v_f_4453_){
_start:
{
lean_object* v_line_4454_; lean_object* v_body_4455_; lean_object* v_extensions_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4464_; 
v_line_4454_ = lean_ctor_get(v_f_4453_, 0);
v_body_4455_ = lean_ctor_get(v_f_4453_, 1);
v_extensions_4456_ = lean_ctor_get(v_f_4453_, 2);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_f_4453_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4458_ = v_f_4453_;
v_isShared_4459_ = v_isSharedCheck_4464_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_extensions_4456_);
lean_inc(v_body_4455_);
lean_inc(v_line_4454_);
lean_dec(v_f_4453_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4464_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4460_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4452_, v_body_4455_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 1, v___x_4460_);
v___x_4462_ = v___x_4458_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_line_4454_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v___x_4460_);
lean_ctor_set(v_reuseFailAlloc_4463_, 2, v_extensions_4456_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_4468_, lean_object* v_x_4469_){
_start:
{
if (lean_obj_tag(v_x_4469_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4479_; 
lean_dec_ref(v___x_4468_);
v_a_4471_ = lean_ctor_get(v_x_4469_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_x_4469_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4473_ = v_x_4469_;
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v_x_4469_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
}
}
else
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4499_; 
v_a_4480_ = lean_ctor_get(v_x_4469_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v_x_4469_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4482_ = v_x_4469_;
v_isShared_4483_ = v_isSharedCheck_4499_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v_x_4469_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4499_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v_line_4484_; lean_object* v_body_4485_; lean_object* v_extensions_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4498_; 
v_line_4484_ = lean_ctor_get(v_a_4480_, 0);
v_body_4485_ = lean_ctor_get(v_a_4480_, 1);
v_extensions_4486_ = lean_ctor_get(v_a_4480_, 2);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_a_4480_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4488_ = v_a_4480_;
v_isShared_4489_ = v_isSharedCheck_4498_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_extensions_4486_);
lean_inc(v_body_4485_);
lean_inc(v_line_4484_);
lean_dec(v_a_4480_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4498_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4490_; lean_object* v___x_4492_; 
v___x_4490_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4468_, v_body_4485_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 1, v___x_4490_);
v___x_4492_ = v___x_4488_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_line_4484_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v___x_4490_);
lean_ctor_set(v_reuseFailAlloc_4497_, 2, v_extensions_4486_);
v___x_4492_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4494_; 
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v___x_4492_);
v___x_4494_ = v___x_4482_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4492_);
v___x_4494_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_4500_, lean_object* v_x_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_4500_, v_x_4501_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_4504_, lean_object* v_action_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; uint8_t v___x_4510_; lean_object* v___x_4511_; 
lean_inc_ref(v___y_4506_);
v___x_4508_ = lean_apply_2(v_action_4505_, v___y_4506_, lean_box(0));
v___x_4509_ = lean_unsigned_to_nat(0u);
v___x_4510_ = 0;
v___x_4511_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4509_, v___x_4510_, v___x_4508_, v___f_4504_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_4512_, lean_object* v_action_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_4512_, v_action_4513_, v___y_4514_);
lean_dec_ref(v___y_4514_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_4522_, lean_object* v_action_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; lean_object* v___x_4529_; 
v___x_4526_ = lean_apply_1(v_action_4523_, lean_box(0));
v___x_4527_ = lean_unsigned_to_nat(0u);
v___x_4528_ = 0;
v___x_4529_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4527_, v___x_4528_, v___x_4526_, v___f_4522_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_4530_, lean_object* v_action_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_4530_, v_action_4531_, v___y_4532_);
lean_dec_ref(v___y_4532_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_4538_, lean_object* v_x_4539_){
_start:
{
if (lean_obj_tag(v_x_4539_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4549_; 
v_a_4541_ = lean_ctor_get(v_x_4539_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v_x_4539_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4543_ = v_x_4539_;
v_isShared_4544_ = v_isSharedCheck_4549_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v_x_4539_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4549_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4547_; 
v___x_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
return v___x_4547_;
}
}
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4559_; 
v_a_4550_ = lean_ctor_get(v_x_4539_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_x_4539_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4552_ = v_x_4539_;
v_isShared_4553_ = v_isSharedCheck_4559_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v_x_4539_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4559_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4556_; 
v___x_4554_ = l_Std_Http_Request_Builder_body___redArg(v_builder_4538_, v_a_4550_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4554_);
v___x_4556_ = v___x_4552_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
lean_object* v___x_4557_; 
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
return v___x_4557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_4560_, lean_object* v_x_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_4560_, v_x_4561_);
lean_dec_ref(v_builder_4560_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_4564_, lean_object* v_gen_4565_){
_start:
{
lean_object* v___x_4567_; lean_object* v___f_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; lean_object* v___x_4571_; 
v___x_4567_ = l_Std_Http_Body_stream(v_gen_4565_);
v___f_4568_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4568_, 0, v_builder_4564_);
v___x_4569_ = lean_unsigned_to_nat(0u);
v___x_4570_ = 0;
v___x_4571_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4569_, v___x_4570_, v___x_4567_, v___f_4568_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_4572_, lean_object* v_gen_4573_, lean_object* v_a_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l_Std_Http_Request_Builder_stream(v_builder_4572_, v_gen_4573_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_4576_, lean_object* v_x_4577_){
_start:
{
if (lean_obj_tag(v_x_4577_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4587_; 
v_a_4579_ = lean_ctor_get(v_x_4577_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_x_4577_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4581_ = v_x_4577_;
v_isShared_4582_ = v_isSharedCheck_4587_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v_x_4577_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4587_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; 
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4597_; 
v_a_4588_ = lean_ctor_get(v_x_4577_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v_x_4577_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4590_ = v_x_4577_;
v_isShared_4591_ = v_isSharedCheck_4597_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v_x_4577_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4597_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4592_; lean_object* v___x_4594_; 
v___x_4592_ = l_Std_Http_Response_Builder_body___redArg(v_builder_4576_, v_a_4588_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 0, v___x_4592_);
v___x_4594_ = v___x_4590_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4592_);
v___x_4594_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4595_; 
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
return v___x_4595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_4598_, lean_object* v_x_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_4598_, v_x_4599_);
lean_dec_ref(v_builder_4598_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_4602_, lean_object* v_gen_4603_){
_start:
{
lean_object* v___x_4605_; lean_object* v___f_4606_; lean_object* v___x_4607_; uint8_t v___x_4608_; lean_object* v___x_4609_; 
v___x_4605_ = l_Std_Http_Body_stream(v_gen_4603_);
v___f_4606_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4606_, 0, v_builder_4602_);
v___x_4607_ = lean_unsigned_to_nat(0u);
v___x_4608_ = 0;
v___x_4609_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4607_, v___x_4608_, v___x_4605_, v___f_4606_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_4610_, lean_object* v_gen_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Std_Http_Response_Builder_stream(v_builder_4610_, v_gen_4611_);
return v_res_4613_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

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
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_51_ = lean_st_ref_set(v_finished_44_, v___x_50_);
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
v___x_99_ = lean_st_ref_set(v_finished_92_, v___x_98_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object* v_pendingProducer_867_, lean_object* v_pendingConsumer_868_, uint8_t v_closed_869_, lean_object* v_knownSize_870_, lean_object* v_pendingIncompleteChunk_871_, lean_object* v_closeError_872_, lean_object* v_interestWaiter_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_876_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_876_, 0, v_pendingProducer_867_);
lean_ctor_set(v___x_876_, 1, v_pendingConsumer_868_);
lean_ctor_set(v___x_876_, 2, v_interestWaiter_873_);
lean_ctor_set(v___x_876_, 3, v_knownSize_870_);
lean_ctor_set(v___x_876_, 4, v_pendingIncompleteChunk_871_);
lean_ctor_set(v___x_876_, 5, v_closeError_872_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*6, v_closed_869_);
v___x_877_ = lean_st_ref_set(v___y_874_, v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object* v_pendingProducer_880_, lean_object* v_pendingConsumer_881_, lean_object* v_closed_882_, lean_object* v_knownSize_883_, lean_object* v_pendingIncompleteChunk_884_, lean_object* v_closeError_885_, lean_object* v_interestWaiter_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v_closed_boxed_889_; lean_object* v_res_890_; 
v_closed_boxed_889_ = lean_unbox(v_closed_882_);
v_res_890_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_880_, v_pendingConsumer_881_, v_closed_boxed_889_, v_knownSize_883_, v_pendingIncompleteChunk_884_, v_closeError_885_, v_interestWaiter_886_, v___y_887_);
lean_dec(v___y_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object* v___f_891_, lean_object* v___y_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v___f_891_);
v_a_895_ = lean_ctor_get(v_x_893_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_903_ == 0)
{
v___x_897_ = v_x_893_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v_x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_905_; 
v_a_904_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v_x_893_, 1);
lean_inc(v___y_892_);
v___x_905_ = lean_apply_3(v___f_891_, v_a_904_, v___y_892_, lean_box(0));
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object* v___f_906_, lean_object* v___y_907_, lean_object* v_x_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_906_, v___y_907_, v_x_908_);
lean_dec(v___y_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object* v_interestWaiter_915_, lean_object* v___f_916_, lean_object* v___f_917_, lean_object* v_x_918_){
_start:
{
if (lean_obj_tag(v_x_918_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v___f_917_);
lean_dec_ref(v___f_916_);
lean_dec(v_interestWaiter_915_);
v_a_920_ = lean_ctor_get(v_x_918_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_x_918_);
if (v_isSharedCheck_928_ == 0)
{
v___x_922_ = v_x_918_;
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v_x_918_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_927_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; 
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_945_; 
v_a_929_ = lean_ctor_get(v_x_918_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_x_918_);
if (v_isSharedCheck_945_ == 0)
{
v___x_931_ = v_x_918_;
v_isShared_932_ = v_isSharedCheck_945_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v_x_918_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_945_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
uint8_t v___x_933_; 
v___x_933_ = lean_unbox(v_a_929_);
if (v___x_933_ == 0)
{
lean_object* v___x_935_; 
lean_dec_ref(v___f_917_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v_interestWaiter_915_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_interestWaiter_915_);
v___x_935_ = v_reuseFailAlloc_940_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; 
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_unbox(v_a_929_);
lean_dec(v_a_929_);
v___x_939_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_937_, v___x_938_, v___x_936_, v___f_916_);
return v___x_939_;
}
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; lean_object* v___x_944_; 
lean_del_object(v___x_931_);
lean_dec(v_a_929_);
lean_dec_ref(v___f_916_);
lean_dec(v_interestWaiter_915_);
v___x_941_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1));
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = 0;
v___x_944_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_942_, v___x_943_, v___x_941_, v___f_917_);
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object* v_interestWaiter_946_, lean_object* v___f_947_, lean_object* v___f_948_, lean_object* v_x_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_946_, v___f_947_, v___f_948_, v_x_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object* v_pendingProducer_952_, uint8_t v_closed_953_, lean_object* v_knownSize_954_, lean_object* v_pendingIncompleteChunk_955_, lean_object* v_closeError_956_, lean_object* v_interestWaiter_957_, lean_object* v_pendingConsumer_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; lean_object* v___f_962_; 
v___x_961_ = lean_box(v_closed_953_);
v___f_962_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed), 9, 6);
lean_closure_set(v___f_962_, 0, v_pendingProducer_952_);
lean_closure_set(v___f_962_, 1, v_pendingConsumer_958_);
lean_closure_set(v___f_962_, 2, v___x_961_);
lean_closure_set(v___f_962_, 3, v_knownSize_954_);
lean_closure_set(v___f_962_, 4, v_pendingIncompleteChunk_955_);
lean_closure_set(v___f_962_, 5, v_closeError_956_);
if (lean_obj_tag(v_interestWaiter_957_) == 0)
{
lean_object* v___f_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; 
lean_inc(v___y_959_);
v___f_963_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_963_, 0, v___f_962_);
lean_closure_set(v___f_963_, 1, v___y_959_);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v_interestWaiter_957_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = 0;
v___x_968_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_966_, v___x_967_, v___x_965_, v___f_963_);
return v___x_968_;
}
else
{
lean_object* v_val_969_; lean_object* v_finished_970_; lean_object* v___x_971_; lean_object* v___f_972_; lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v___x_978_; 
v_val_969_ = lean_ctor_get(v_interestWaiter_957_, 0);
v_finished_970_ = lean_ctor_get(v_val_969_, 0);
v___x_971_ = lean_st_ref_get(v_finished_970_);
lean_inc(v___y_959_);
v___f_972_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_972_, 0, v___f_962_);
lean_closure_set(v___f_972_, 1, v___y_959_);
lean_inc_ref(v___f_972_);
v___f_973_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed), 5, 3);
lean_closure_set(v___f_973_, 0, v_interestWaiter_957_);
lean_closure_set(v___f_973_, 1, v___f_972_);
lean_closure_set(v___f_973_, 2, v___f_972_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_971_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = 0;
v___x_978_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_976_, v___x_977_, v___x_975_, v___f_973_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object* v_pendingProducer_979_, lean_object* v_closed_980_, lean_object* v_knownSize_981_, lean_object* v_pendingIncompleteChunk_982_, lean_object* v_closeError_983_, lean_object* v_interestWaiter_984_, lean_object* v_pendingConsumer_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v_closed_boxed_988_; lean_object* v_res_989_; 
v_closed_boxed_988_ = lean_unbox(v_closed_980_);
v_res_989_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_979_, v_closed_boxed_988_, v_knownSize_981_, v_pendingIncompleteChunk_982_, v_closeError_983_, v_interestWaiter_984_, v_pendingConsumer_985_, v___y_986_);
lean_dec(v___y_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object* v___f_990_, lean_object* v___y_991_, lean_object* v_x_992_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v___f_990_);
v_a_994_ = lean_ctor_get(v_x_992_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_x_992_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_996_ = v_x_992_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v_x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1001_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v_x_992_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v_x_992_, 1);
lean_inc(v___y_991_);
v___x_1004_ = lean_apply_3(v___f_990_, v_a_1003_, v___y_991_, lean_box(0));
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object* v___f_1005_, lean_object* v___y_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_1005_, v___y_1006_, v_x_1007_);
lean_dec(v___y_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object* v___f_1010_, lean_object* v_a_1011_, lean_object* v_x_1012_){
_start:
{
if (lean_obj_tag(v_x_1012_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v___f_1010_);
v_a_1014_ = lean_ctor_get(v_x_1012_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_1012_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v_x_1012_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v_x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1024_; 
v_a_1023_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v_x_1012_, 1);
lean_inc(v_a_1011_);
v___x_1024_ = lean_apply_3(v___f_1010_, v_a_1023_, v_a_1011_, lean_box(0));
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object* v___f_1025_, lean_object* v_a_1026_, lean_object* v_x_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_1025_, v_a_1026_, v_x_1027_);
lean_dec(v_a_1026_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object* v_pendingConsumer_1034_, lean_object* v___f_1035_, lean_object* v___f_1036_, lean_object* v_x_1037_){
_start:
{
if (lean_obj_tag(v_x_1037_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref(v___f_1036_);
lean_dec_ref(v___f_1035_);
lean_dec(v_pendingConsumer_1034_);
v_a_1039_ = lean_ctor_get(v_x_1037_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_x_1037_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1041_ = v_x_1037_;
v_isShared_1042_ = v_isSharedCheck_1047_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v_x_1037_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1047_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1064_; 
v_a_1048_ = lean_ctor_get(v_x_1037_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1037_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1050_ = v_x_1037_;
v_isShared_1051_ = v_isSharedCheck_1064_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v_x_1037_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1064_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_unbox(v_a_1048_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1054_; 
lean_dec_ref(v___f_1036_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v_pendingConsumer_1034_);
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_pendingConsumer_1034_);
v___x_1054_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_unbox(v_a_1048_);
lean_dec(v_a_1048_);
v___x_1058_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1056_, v___x_1057_, v___x_1055_, v___f_1035_);
return v___x_1058_;
}
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
lean_del_object(v___x_1050_);
lean_dec(v_a_1048_);
lean_dec_ref(v___f_1035_);
lean_dec(v_pendingConsumer_1034_);
v___x_1060_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1));
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = 0;
v___x_1063_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1061_, v___x_1062_, v___x_1060_, v___f_1036_);
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object* v_pendingConsumer_1065_, lean_object* v___f_1066_, lean_object* v___f_1067_, lean_object* v_x_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_1065_, v___f_1066_, v___f_1067_, v_x_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object* v_a_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
v_a_1074_ = lean_ctor_get(v_x_1072_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1076_ = v_x_1072_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v_x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1123_; 
v_a_1083_ = lean_ctor_get(v_x_1072_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1085_ = v_x_1072_;
v_isShared_1086_ = v_isSharedCheck_1123_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v_x_1072_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1123_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v_pendingProducer_1087_; lean_object* v_pendingConsumer_1088_; lean_object* v_interestWaiter_1089_; uint8_t v_closed_1090_; lean_object* v_knownSize_1091_; lean_object* v_pendingIncompleteChunk_1092_; lean_object* v_closeError_1093_; lean_object* v___x_1094_; lean_object* v___f_1095_; lean_object* v___y_1097_; 
v_pendingProducer_1087_ = lean_ctor_get(v_a_1083_, 0);
lean_inc(v_pendingProducer_1087_);
v_pendingConsumer_1088_ = lean_ctor_get(v_a_1083_, 1);
lean_inc(v_pendingConsumer_1088_);
v_interestWaiter_1089_ = lean_ctor_get(v_a_1083_, 2);
lean_inc(v_interestWaiter_1089_);
v_closed_1090_ = lean_ctor_get_uint8(v_a_1083_, sizeof(void*)*6);
v_knownSize_1091_ = lean_ctor_get(v_a_1083_, 3);
lean_inc(v_knownSize_1091_);
v_pendingIncompleteChunk_1092_ = lean_ctor_get(v_a_1083_, 4);
lean_inc(v_pendingIncompleteChunk_1092_);
v_closeError_1093_ = lean_ctor_get(v_a_1083_, 5);
lean_inc(v_closeError_1093_);
lean_dec(v_a_1083_);
v___x_1094_ = lean_box(v_closed_1090_);
v___f_1095_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed), 9, 6);
lean_closure_set(v___f_1095_, 0, v_pendingProducer_1087_);
lean_closure_set(v___f_1095_, 1, v___x_1094_);
lean_closure_set(v___f_1095_, 2, v_knownSize_1091_);
lean_closure_set(v___f_1095_, 3, v_pendingIncompleteChunk_1092_);
lean_closure_set(v___f_1095_, 4, v_closeError_1093_);
lean_closure_set(v___f_1095_, 5, v_interestWaiter_1089_);
if (lean_obj_tag(v_pendingConsumer_1088_) == 1)
{
lean_object* v_val_1106_; 
v_val_1106_ = lean_ctor_get(v_pendingConsumer_1088_, 0);
lean_inc(v_val_1106_);
if (lean_obj_tag(v_val_1106_) == 1)
{
lean_object* v_finished_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1122_; 
lean_del_object(v___x_1085_);
v_finished_1107_ = lean_ctor_get(v_val_1106_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_val_1106_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1109_ = v_val_1106_;
v_isShared_1110_ = v_isSharedCheck_1122_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_finished_1107_);
lean_dec(v_val_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1122_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_finished_1111_; lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___x_1116_; 
v_finished_1111_ = lean_ctor_get(v_finished_1107_, 0);
lean_inc(v_finished_1111_);
lean_dec_ref(v_finished_1107_);
v___x_1112_ = lean_st_ref_get(v_finished_1111_);
lean_dec(v_finished_1111_);
lean_inc(v_a_1071_);
v___f_1113_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1113_, 0, v___f_1095_);
lean_closure_set(v___f_1113_, 1, v_a_1071_);
lean_inc_ref(v___f_1113_);
v___f_1114_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1114_, 0, v_pendingConsumer_1088_);
lean_closure_set(v___f_1114_, 1, v___f_1113_);
lean_closure_set(v___f_1114_, 2, v___f_1113_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1112_);
v___x_1116_ = v___x_1109_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1112_);
v___x_1116_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = 0;
v___x_1120_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1118_, v___x_1119_, v___x_1117_, v___f_1114_);
return v___x_1120_;
}
}
}
else
{
lean_dec(v_val_1106_);
v___y_1097_ = v_a_1071_;
goto v___jp_1096_;
}
}
else
{
v___y_1097_ = v_a_1071_;
goto v___jp_1096_;
}
v___jp_1096_:
{
lean_object* v___f_1098_; lean_object* v___x_1100_; 
lean_inc(v___y_1097_);
v___f_1098_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1098_, 0, v___f_1095_);
lean_closure_set(v___f_1098_, 1, v___y_1097_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v_pendingConsumer_1088_);
v___x_1100_ = v___x_1085_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_pendingConsumer_1088_);
v___x_1100_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = 0;
v___x_1104_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1102_, v___x_1103_, v___x_1101_, v___f_1098_);
return v___x_1104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object* v_a_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_1124_, v_x_1125_);
lean_dec(v_a_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object* v_a_1128_){
_start:
{
lean_object* v___x_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1130_ = lean_st_ref_get(v_a_1128_);
lean_inc(v_a_1128_);
v___f_1131_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1131_, 0, v_a_1128_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = 0;
v___x_1136_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1134_, v___x_1135_, v___x_1133_, v___f_1131_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object* v_a_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_1137_);
lean_dec(v_a_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object* v_mutex_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_io_basemutex_unlock(v_mutex_1140_);
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_1146_, lean_object* v_x_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(v_mutex_1146_, v_x_1147_);
lean_dec(v_x_1147_);
lean_dec(v_mutex_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object* v_k_1150_, lean_object* v_ref_1151_, lean_object* v_x_1152_){
_start:
{
if (lean_obj_tag(v_x_1152_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_ref_1151_);
lean_dec_ref(v_k_1150_);
v_a_1154_ = lean_ctor_get(v_x_1152_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_x_1152_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1156_ = v_x_1152_;
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v_x_1152_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
}
else
{
lean_object* v___x_1163_; 
lean_dec_ref_known(v_x_1152_, 1);
v___x_1163_ = lean_apply_2(v_k_1150_, v_ref_1151_, lean_box(0));
return v___x_1163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object* v_k_1164_, lean_object* v_ref_1165_, lean_object* v_x_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(v_k_1164_, v_ref_1165_, v_x_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object* v_mutex_1169_, lean_object* v___f_1170_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; 
v___x_1172_ = lean_io_basemutex_lock(v_mutex_1169_);
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = 0;
v___x_1177_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1175_, v___x_1176_, v___x_1174_, v___f_1170_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_1178_, lean_object* v___f_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(v_mutex_1178_, v___f_1179_);
lean_dec(v_mutex_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object* v___y_1182_){
_start:
{
if (lean_obj_tag(v___y_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___y_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___y_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___y_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
v_a_1191_ = lean_ctor_get(v___y_1182_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1193_ = v___y_1182_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___y_1182_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v_fst_1195_; lean_object* v___x_1197_; 
v_fst_1195_ = lean_ctor_get(v_a_1191_, 0);
lean_inc(v_fst_1195_);
lean_dec(v_a_1191_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v_fst_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_fst_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(lean_object* v_mutex_1201_, lean_object* v_k_1202_){
_start:
{
lean_object* v_ref_1204_; lean_object* v_mutex_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___y_1213_; 
v_ref_1204_ = lean_ctor_get(v_mutex_1201_, 0);
lean_inc(v_ref_1204_);
v_mutex_1205_ = lean_ctor_get(v_mutex_1201_, 1);
lean_inc_n(v_mutex_1205_, 2);
lean_dec_ref(v_mutex_1201_);
v___f_1206_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1206_, 0, v_mutex_1205_);
v___f_1207_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1207_, 0, v_k_1202_);
lean_closure_set(v___f_1207_, 1, v_ref_1204_);
v___f_1208_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1208_, 0, v_mutex_1205_);
lean_closure_set(v___f_1208_, 1, v___f_1207_);
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = 0;
v___x_1211_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1208_, v___f_1206_, v___x_1209_, v___x_1210_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1215_; 
v_a_1215_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1211_, 1);
if (lean_obj_tag(v_a_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
v_a_1216_ = lean_ctor_get(v_a_1215_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_a_1215_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v_a_1215_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v_a_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v___y_1213_ = v___x_1221_;
goto v___jp_1212_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1232_; 
v_a_1224_ = lean_ctor_get(v_a_1215_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_a_1215_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1226_ = v_a_1215_;
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v_a_1215_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_fst_1228_; lean_object* v___x_1230_; 
v_fst_1228_ = lean_ctor_get(v_a_1224_, 0);
lean_inc(v_fst_1228_);
lean_dec(v_a_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v_fst_1228_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_fst_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
v___y_1213_ = v___x_1230_;
goto v___jp_1212_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1242_; 
v_a_1233_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1235_ = v___x_1211_;
v_isShared_1236_ = v_isSharedCheck_1242_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1211_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1242_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___f_1237_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0));
v___x_1238_ = lean_task_map(v___f_1237_, v_a_1233_, v___x_1209_, v___x_1210_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1238_);
v___x_1240_ = v___x_1235_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
v___jp_1212_:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___y_1213_);
return v___x_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___boxed(lean_object* v_mutex_1243_, lean_object* v_k_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1243_, v_k_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(lean_object* v_00_u03b1_1247_, lean_object* v_00_u03b2_1248_, lean_object* v_mutex_1249_, lean_object* v_k_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1249_, v_k_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_00_u03b2_1254_, lean_object* v_mutex_1255_, lean_object* v_k_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(v_00_u03b1_1253_, v_00_u03b2_1254_, v_mutex_1255_, v_k_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0(lean_object* v_x_1259_){
_start:
{
if (lean_obj_tag(v_x_1259_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1269_; 
v_a_1261_ = lean_ctor_get(v_x_1259_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_x_1259_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1263_ = v_x_1259_;
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v_x_1259_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v_x_1259_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v_x_1259_, 1);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_a_1270_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(lean_object* v_x_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Std_Http_Body_Stream_tryRecv___lam__0(v_x_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object* v_a_1275_, lean_object* v___f_1276_, lean_object* v_x_1277_){
_start:
{
if (lean_obj_tag(v_x_1277_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v___f_1276_);
v_a_1279_ = lean_ctor_get(v_x_1277_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_x_1277_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1281_ = v_x_1277_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v_x_1277_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
return v___x_1285_;
}
}
}
else
{
lean_object* v_a_1288_; 
v_a_1288_ = lean_ctor_get(v_x_1277_, 0);
lean_inc(v_a_1288_);
if (lean_obj_tag(v_a_1288_) == 1)
{
lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v___f_1276_);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_a_1288_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v_a_1288_, 0);
lean_dec(v_unused_1297_);
v___x_1290_ = v_a_1288_;
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
else
{
lean_dec(v_a_1288_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v_x_1277_);
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_x_1277_);
v___x_1293_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
}
else
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_a_1288_);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_x_1277_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_x_1277_, 0);
lean_dec(v_unused_1310_);
v___x_1299_ = v_x_1277_;
v_isShared_1300_ = v_isSharedCheck_1309_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v_x_1277_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1309_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_st_ref_get(v_a_1275_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1301_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = 0;
v___x_1307_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1305_, v___x_1306_, v___x_1304_, v___f_1276_);
return v___x_1307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object* v_a_1311_, lean_object* v___f_1312_, lean_object* v_x_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_a_1311_, v___f_1312_, v_x_1313_);
lean_dec(v_a_1311_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object* v_x_1320_){
_start:
{
if (lean_obj_tag(v_x_1320_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1330_; 
v_a_1322_ = lean_ctor_get(v_x_1320_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1320_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1324_ = v_x_1320_;
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v_x_1320_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1349_; 
v_a_1331_ = lean_ctor_get(v_x_1320_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_x_1320_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1333_ = v_x_1320_;
v_isShared_1334_ = v_isSharedCheck_1349_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v_x_1320_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1349_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_closeError_1335_; 
v_closeError_1335_ = lean_ctor_get(v_a_1331_, 5);
lean_inc(v_closeError_1335_);
lean_dec(v_a_1331_);
if (lean_obj_tag(v_closeError_1335_) == 1)
{
lean_object* v_val_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1347_; 
v_val_1336_ = lean_ctor_get(v_closeError_1335_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_closeError_1335_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1338_ = v_closeError_1335_;
v_isShared_1339_ = v_isSharedCheck_1347_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_val_1336_);
lean_dec(v_closeError_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1347_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 0);
lean_ctor_set(v___x_1333_, 0, v_val_1336_);
v___x_1341_ = v___x_1333_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_val_1336_);
v___x_1341_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1343_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1341_);
v___x_1343_ = v___x_1338_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
}
}
}
else
{
lean_object* v___x_1348_; 
lean_dec(v_closeError_1335_);
lean_del_object(v___x_1333_);
v___x_1348_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__1));
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object* v_x_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_x_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(lean_object* v_done_1357_, lean_object* v___f_1358_, lean_object* v_x_1359_){
_start:
{
if (lean_obj_tag(v_x_1359_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v___f_1358_);
v_a_1361_ = lean_ctor_get(v_x_1359_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_x_1359_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v_x_1359_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v_x_1359_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
}
}
else
{
uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; 
lean_dec_ref_known(v_x_1359_, 1);
v___x_1370_ = 1;
v___x_1371_ = lean_box(v___x_1370_);
v___x_1372_ = lean_io_promise_resolve(v___x_1371_, v_done_1357_);
v___x_1373_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = 0;
v___x_1376_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1374_, v___x_1375_, v___x_1373_, v___f_1358_);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed(lean_object* v_done_1377_, lean_object* v___f_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(v_done_1377_, v___f_1378_, v_x_1379_);
lean_dec(v_done_1377_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(lean_object* v_chunk_1382_, lean_object* v_x_1383_){
_start:
{
if (lean_obj_tag(v_x_1383_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v_chunk_1382_);
v_a_1385_ = lean_ctor_get(v_x_1383_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_x_1383_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1387_ = v_x_1383_;
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v_x_1383_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
else
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1402_; 
v_isSharedCheck_1402_ = !lean_is_exclusive(v_x_1383_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v_x_1383_, 0);
lean_dec(v_unused_1403_);
v___x_1395_ = v_x_1383_;
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v_x_1383_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_chunk_1382_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed(lean_object* v_chunk_1404_, lean_object* v_x_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(v_chunk_1404_, v_x_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(lean_object* v_a_1410_, lean_object* v_x_1411_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
v_a_1413_ = lean_ctor_get(v_x_1411_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_x_1411_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1415_ = v_x_1411_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v_x_1411_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1463_; 
v_a_1422_ = lean_ctor_get(v_x_1411_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1411_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1424_ = v_x_1411_;
v_isShared_1425_ = v_isSharedCheck_1463_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v_x_1411_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1463_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v_pendingProducer_1426_; 
v_pendingProducer_1426_ = lean_ctor_get(v_a_1422_, 0);
lean_inc(v_pendingProducer_1426_);
if (lean_obj_tag(v_pendingProducer_1426_) == 1)
{
lean_object* v_val_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1461_; 
v_val_1427_ = lean_ctor_get(v_pendingProducer_1426_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_pendingProducer_1426_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1429_ = v_pendingProducer_1426_;
v_isShared_1430_ = v_isSharedCheck_1461_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_val_1427_);
lean_dec(v_pendingProducer_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1461_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_pendingConsumer_1431_; lean_object* v_interestWaiter_1432_; uint8_t v_closed_1433_; lean_object* v_knownSize_1434_; lean_object* v_pendingIncompleteChunk_1435_; lean_object* v_closeError_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1459_; 
v_pendingConsumer_1431_ = lean_ctor_get(v_a_1422_, 1);
v_interestWaiter_1432_ = lean_ctor_get(v_a_1422_, 2);
v_closed_1433_ = lean_ctor_get_uint8(v_a_1422_, sizeof(void*)*6);
v_knownSize_1434_ = lean_ctor_get(v_a_1422_, 3);
v_pendingIncompleteChunk_1435_ = lean_ctor_get(v_a_1422_, 4);
v_closeError_1436_ = lean_ctor_get(v_a_1422_, 5);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_a_1422_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v_a_1422_, 0);
lean_dec(v_unused_1460_);
v___x_1438_ = v_a_1422_;
v_isShared_1439_ = v_isSharedCheck_1459_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_closeError_1436_);
lean_inc(v_pendingIncompleteChunk_1435_);
lean_inc(v_knownSize_1434_);
lean_inc(v_interestWaiter_1432_);
lean_inc(v_pendingConsumer_1431_);
lean_dec(v_a_1422_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1459_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_chunk_1440_; lean_object* v_done_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v_chunk_1440_ = lean_ctor_get(v_val_1427_, 0);
lean_inc_ref(v_chunk_1440_);
v_done_1441_ = lean_ctor_get(v_val_1427_, 1);
lean_inc(v_done_1441_);
lean_dec(v_val_1427_);
v___x_1442_ = lean_box(0);
v___x_1443_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1434_, v_chunk_1440_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 3, v___x_1443_);
lean_ctor_set(v___x_1438_, 0, v___x_1442_);
v___x_1445_ = v___x_1438_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_pendingConsumer_1431_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_interestWaiter_1432_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_pendingIncompleteChunk_1435_);
lean_ctor_set(v_reuseFailAlloc_1458_, 5, v_closeError_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1458_, sizeof(void*)*6, v_closed_1433_);
v___x_1445_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___f_1447_; lean_object* v___f_1448_; lean_object* v___x_1450_; 
v___x_1446_ = lean_st_ref_set(v_a_1410_, v___x_1445_);
v___f_1447_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1447_, 0, v_chunk_1440_);
v___f_1448_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1448_, 0, v_done_1441_);
lean_closure_set(v___f_1448_, 1, v___f_1447_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1446_);
v___x_1450_ = v___x_1424_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1446_);
v___x_1450_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1450_);
v___x_1452_ = v___x_1429_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = 0;
v___x_1455_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1453_, v___x_1454_, v___x_1452_, v___f_1448_);
return v___x_1455_;
}
}
}
}
}
}
else
{
lean_object* v___x_1462_; 
lean_dec(v_pendingProducer_1426_);
lean_del_object(v___x_1424_);
lean_dec(v_a_1422_);
v___x_1462_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1464_, lean_object* v_x_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(v_a_1464_, v_x_1465_);
lean_dec(v_a_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1470_ = lean_st_ref_get(v_a_1468_);
lean_inc(v_a_1468_);
v___f_1471_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1471_, 0, v_a_1468_);
v___x_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = 0;
v___x_1476_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1474_, v___x_1475_, v___x_1473_, v___f_1471_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___boxed(lean_object* v_a_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1477_);
lean_dec(v_a_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v___f_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1481_);
v___f_1484_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0));
lean_inc(v_a_1481_);
v___f_1485_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1485_, 0, v_a_1481_);
lean_closure_set(v___f_1485_, 1, v___f_1484_);
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = 0;
v___x_1488_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1486_, v___x_1487_, v___x_1483_, v___f_1485_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object* v_a_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_1489_);
lean_dec(v_a_1489_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1(lean_object* v___y_1492_, lean_object* v___f_1493_, lean_object* v_x_1494_){
_start:
{
if (lean_obj_tag(v_x_1494_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v___f_1493_);
v_a_1496_ = lean_ctor_get(v_x_1494_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_x_1494_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1498_ = v_x_1494_;
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v_x_1494_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
return v___x_1502_;
}
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; 
lean_dec_ref_known(v_x_1494_, 1);
v___x_1505_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1492_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = 0;
v___x_1508_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1506_, v___x_1507_, v___x_1505_, v___f_1493_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(lean_object* v___y_1509_, lean_object* v___f_1510_, lean_object* v_x_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Std_Http_Body_Stream_tryRecv___lam__1(v___y_1509_, v___f_1510_, v_x_1511_);
lean_dec(v___y_1509_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2(lean_object* v___f_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; lean_object* v___f_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1517_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1515_);
lean_inc(v___y_1515_);
v___f_1518_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecv___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1518_, 0, v___y_1515_);
lean_closure_set(v___f_1518_, 1, v___f_1514_);
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = 0;
v___x_1521_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1519_, v___x_1520_, v___x_1517_, v___f_1518_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2___boxed(lean_object* v___f_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_Http_Body_Stream_tryRecv___lam__2(v___f_1522_, v___y_1523_);
lean_dec(v___y_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv(lean_object* v_stream_1529_){
_start:
{
lean_object* v___f_1531_; lean_object* v___x_1532_; 
v___f_1531_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecv___closed__1));
v___x_1532_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1529_, v___f_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___boxed(lean_object* v_stream_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Std_Http_Body_Stream_tryRecv(v_stream_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(lean_object* v_x_1536_){
_start:
{
uint8_t v___y_1539_; 
if (lean_obj_tag(v_x_1536_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1551_; 
v_a_1543_ = lean_ctor_get(v_x_1536_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1545_ = v_x_1536_;
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v_x_1536_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v_pendingProducer_1553_; 
v_a_1552_ = lean_ctor_get(v_x_1536_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v_x_1536_, 1);
v_pendingProducer_1553_ = lean_ctor_get(v_a_1552_, 0);
if (lean_obj_tag(v_pendingProducer_1553_) == 0)
{
uint8_t v_closed_1554_; 
v_closed_1554_ = lean_ctor_get_uint8(v_a_1552_, sizeof(void*)*6);
lean_dec(v_a_1552_);
v___y_1539_ = v_closed_1554_;
goto v___jp_1538_;
}
else
{
uint8_t v___x_1555_; 
lean_dec(v_a_1552_);
v___x_1555_ = 1;
v___y_1539_ = v___x_1555_;
goto v___jp_1538_;
}
}
v___jp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_box(v___y_1539_);
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed(lean_object* v_x_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(v_x_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(lean_object* v_a_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1562_ = lean_st_ref_get(v_a_1560_);
v___f_1563_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0));
v___x_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
v___x_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = 0;
v___x_1568_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1566_, v___x_1567_, v___x_1565_, v___f_1563_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___boxed(lean_object* v_a_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v_a_1569_);
lean_dec(v_a_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0(lean_object* v_x_1572_){
_start:
{
if (lean_obj_tag(v_x_1572_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1582_; 
v_a_1574_ = lean_ctor_get(v_x_1572_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1576_ = v_x_1572_;
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v_x_1572_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
return v___x_1580_;
}
}
}
else
{
lean_object* v_a_1583_; 
v_a_1583_ = lean_ctor_get(v_x_1572_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v_x_1572_, 1);
if (lean_obj_tag(v_a_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1592_; 
v_a_1584_ = lean_ctor_get(v_a_1583_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_a_1583_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1586_ = v_a_1583_;
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v_a_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1602_; 
v_a_1593_ = lean_ctor_get(v_a_1583_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_a_1583_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1595_ = v_a_1583_;
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v_a_1583_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_a_1593_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1597_);
v___x_1599_ = v___x_1595_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed(lean_object* v_x_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Std_Http_Body_Stream_tryRecvBody___lam__0(v_x_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1(lean_object* v___y_1610_, lean_object* v___f_1611_, lean_object* v_x_1612_){
_start:
{
if (lean_obj_tag(v_x_1612_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v___f_1611_);
v_a_1614_ = lean_ctor_get(v_x_1612_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1612_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1616_ = v_x_1612_;
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v_x_1612_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
}
}
else
{
lean_object* v_a_1623_; uint8_t v___x_1624_; 
v_a_1623_ = lean_ctor_get(v_x_1612_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v_x_1612_, 1);
v___x_1624_ = lean_unbox(v_a_1623_);
lean_dec(v_a_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; 
lean_dec_ref(v___f_1611_);
v___x_1625_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1));
return v___x_1625_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; 
v___x_1626_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1610_);
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = 0;
v___x_1629_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1627_, v___x_1628_, v___x_1626_, v___f_1611_);
return v___x_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed(lean_object* v___y_1630_, lean_object* v___f_1631_, lean_object* v_x_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1(v___y_1630_, v___f_1631_, v_x_1632_);
lean_dec(v___y_1630_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2(lean_object* v___y_1635_, lean_object* v___f_1636_, lean_object* v_x_1637_){
_start:
{
if (lean_obj_tag(v_x_1637_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___f_1636_);
v_a_1639_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1641_ = v_x_1637_;
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v_x_1637_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
return v___x_1645_;
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; 
lean_dec_ref_known(v_x_1637_, 1);
v___x_1648_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_1635_);
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = 0;
v___x_1651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1649_, v___x_1650_, v___x_1648_, v___f_1636_);
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed(lean_object* v___y_1652_, lean_object* v___f_1653_, lean_object* v_x_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Std_Http_Body_Stream_tryRecvBody___lam__2(v___y_1652_, v___f_1653_, v_x_1654_);
lean_dec(v___y_1652_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3(lean_object* v___f_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; 
v___x_1660_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1658_);
lean_inc_n(v___y_1658_, 2);
v___f_1661_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1661_, 0, v___y_1658_);
lean_closure_set(v___f_1661_, 1, v___f_1657_);
v___f_1662_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1662_, 0, v___y_1658_);
lean_closure_set(v___f_1662_, 1, v___f_1661_);
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = 0;
v___x_1665_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1663_, v___x_1664_, v___x_1660_, v___f_1662_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed(lean_object* v___f_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Std_Http_Body_Stream_tryRecvBody___lam__3(v___f_1666_, v___y_1667_);
lean_dec(v___y_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody(lean_object* v_stream_1673_){
_start:
{
lean_object* v___f_1675_; lean_object* v___x_1676_; 
v___f_1675_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_1676_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1673_, v___f_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___boxed(lean_object* v_stream_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object* v_a_1680_){
_start:
{
lean_object* v___x_1682_; lean_object* v_pendingProducer_1683_; lean_object* v_pendingConsumer_1684_; lean_object* v_interestWaiter_1685_; uint8_t v_closed_1686_; lean_object* v_knownSize_1687_; lean_object* v_pendingIncompleteChunk_1688_; lean_object* v_closeError_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1715_; 
v___x_1682_ = lean_st_ref_get(v_a_1680_);
v_pendingProducer_1683_ = lean_ctor_get(v___x_1682_, 0);
v_pendingConsumer_1684_ = lean_ctor_get(v___x_1682_, 1);
v_interestWaiter_1685_ = lean_ctor_get(v___x_1682_, 2);
v_closed_1686_ = lean_ctor_get_uint8(v___x_1682_, sizeof(void*)*6);
v_knownSize_1687_ = lean_ctor_get(v___x_1682_, 3);
v_pendingIncompleteChunk_1688_ = lean_ctor_get(v___x_1682_, 4);
v_closeError_1689_ = lean_ctor_get(v___x_1682_, 5);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1691_ = v___x_1682_;
v_isShared_1692_ = v_isSharedCheck_1715_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_closeError_1689_);
lean_inc(v_pendingIncompleteChunk_1688_);
lean_inc(v_knownSize_1687_);
lean_inc(v_interestWaiter_1685_);
lean_inc(v_pendingConsumer_1684_);
lean_inc(v_pendingProducer_1683_);
lean_dec(v___x_1682_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1715_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___y_1694_; lean_object* v_interestWaiter_1695_; lean_object* v___y_1696_; lean_object* v_pendingConsumer_1702_; lean_object* v___y_1703_; 
if (lean_obj_tag(v_pendingConsumer_1684_) == 1)
{
lean_object* v_val_1709_; 
v_val_1709_ = lean_ctor_get(v_pendingConsumer_1684_, 0);
if (lean_obj_tag(v_val_1709_) == 1)
{
lean_object* v_finished_1710_; lean_object* v_finished_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v_finished_1710_ = lean_ctor_get(v_val_1709_, 0);
v_finished_1711_ = lean_ctor_get(v_finished_1710_, 0);
v___x_1712_ = lean_st_ref_get(v_finished_1711_);
v___x_1713_ = lean_unbox(v___x_1712_);
lean_dec(v___x_1712_);
if (v___x_1713_ == 0)
{
v_pendingConsumer_1702_ = v_pendingConsumer_1684_;
v___y_1703_ = v_a_1680_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1714_; 
lean_dec_ref_known(v_pendingConsumer_1684_, 1);
v___x_1714_ = lean_box(0);
v_pendingConsumer_1702_ = v___x_1714_;
v___y_1703_ = v_a_1680_;
goto v___jp_1701_;
}
}
else
{
v_pendingConsumer_1702_ = v_pendingConsumer_1684_;
v___y_1703_ = v_a_1680_;
goto v___jp_1701_;
}
}
else
{
v_pendingConsumer_1702_ = v_pendingConsumer_1684_;
v___y_1703_ = v_a_1680_;
goto v___jp_1701_;
}
v___jp_1693_:
{
lean_object* v___x_1698_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 2, v_interestWaiter_1695_);
lean_ctor_set(v___x_1691_, 1, v___y_1694_);
v___x_1698_ = v___x_1691_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_pendingProducer_1683_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___y_1694_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_interestWaiter_1695_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_knownSize_1687_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_pendingIncompleteChunk_1688_);
lean_ctor_set(v_reuseFailAlloc_1700_, 5, v_closeError_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*6, v_closed_1686_);
v___x_1698_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_st_ref_set(v___y_1696_, v___x_1698_);
return v___x_1699_;
}
}
v___jp_1701_:
{
if (lean_obj_tag(v_interestWaiter_1685_) == 0)
{
v___y_1694_ = v_pendingConsumer_1702_;
v_interestWaiter_1695_ = v_interestWaiter_1685_;
v___y_1696_ = v___y_1703_;
goto v___jp_1693_;
}
else
{
lean_object* v_val_1704_; lean_object* v_finished_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v_val_1704_ = lean_ctor_get(v_interestWaiter_1685_, 0);
v_finished_1705_ = lean_ctor_get(v_val_1704_, 0);
v___x_1706_ = lean_st_ref_get(v_finished_1705_);
v___x_1707_ = lean_unbox(v___x_1706_);
lean_dec(v___x_1706_);
if (v___x_1707_ == 0)
{
v___y_1694_ = v_pendingConsumer_1702_;
v_interestWaiter_1695_ = v_interestWaiter_1685_;
v___y_1696_ = v___y_1703_;
goto v___jp_1693_;
}
else
{
lean_object* v___x_1708_; 
lean_dec_ref_known(v_interestWaiter_1685_, 1);
v___x_1708_ = lean_box(0);
v___y_1694_ = v_pendingConsumer_1702_;
v_interestWaiter_1695_ = v___x_1708_;
v___y_1696_ = v___y_1703_;
goto v___jp_1693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object* v_a_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_1716_);
lean_dec(v_a_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v_pendingProducer_1722_; 
v___x_1721_ = lean_st_ref_get(v_a_1719_);
v_pendingProducer_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_pendingProducer_1722_);
if (lean_obj_tag(v_pendingProducer_1722_) == 1)
{
lean_object* v_val_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1752_; 
v_val_1723_ = lean_ctor_get(v_pendingProducer_1722_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_pendingProducer_1722_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1725_ = v_pendingProducer_1722_;
v_isShared_1726_ = v_isSharedCheck_1752_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_val_1723_);
lean_dec(v_pendingProducer_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1752_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_pendingConsumer_1727_; lean_object* v_interestWaiter_1728_; uint8_t v_closed_1729_; lean_object* v_knownSize_1730_; lean_object* v_pendingIncompleteChunk_1731_; lean_object* v_closeError_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1750_; 
v_pendingConsumer_1727_ = lean_ctor_get(v___x_1721_, 1);
v_interestWaiter_1728_ = lean_ctor_get(v___x_1721_, 2);
v_closed_1729_ = lean_ctor_get_uint8(v___x_1721_, sizeof(void*)*6);
v_knownSize_1730_ = lean_ctor_get(v___x_1721_, 3);
v_pendingIncompleteChunk_1731_ = lean_ctor_get(v___x_1721_, 4);
v_closeError_1732_ = lean_ctor_get(v___x_1721_, 5);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v___x_1721_, 0);
lean_dec(v_unused_1751_);
v___x_1734_ = v___x_1721_;
v_isShared_1735_ = v_isSharedCheck_1750_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_closeError_1732_);
lean_inc(v_pendingIncompleteChunk_1731_);
lean_inc(v_knownSize_1730_);
lean_inc(v_interestWaiter_1728_);
lean_inc(v_pendingConsumer_1727_);
lean_dec(v___x_1721_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1750_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_chunk_1736_; lean_object* v_done_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v_chunk_1736_ = lean_ctor_get(v_val_1723_, 0);
lean_inc_ref(v_chunk_1736_);
v_done_1737_ = lean_ctor_get(v_val_1723_, 1);
lean_inc(v_done_1737_);
lean_dec(v_val_1723_);
v___x_1738_ = lean_box(0);
v___x_1739_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1730_, v_chunk_1736_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 3, v___x_1739_);
lean_ctor_set(v___x_1734_, 0, v___x_1738_);
v___x_1741_ = v___x_1734_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_pendingConsumer_1727_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_interestWaiter_1728_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v_pendingIncompleteChunk_1731_);
lean_ctor_set(v_reuseFailAlloc_1749_, 5, v_closeError_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1749_, sizeof(void*)*6, v_closed_1729_);
v___x_1741_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1742_ = lean_st_ref_set(v_a_1719_, v___x_1741_);
v___x_1743_ = 1;
v___x_1744_ = lean_box(v___x_1743_);
v___x_1745_ = lean_io_promise_resolve(v___x_1744_, v_done_1737_);
lean_dec(v_done_1737_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v_chunk_1736_);
v___x_1747_ = v___x_1725_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_chunk_1736_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
else
{
lean_object* v___x_1753_; 
lean_dec(v_pendingProducer_1722_);
lean_dec(v___x_1721_);
v___x_1753_ = lean_box(0);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object* v_a_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_1754_);
lean_dec(v_a_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object* v_a_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v_interestWaiter_1760_; 
v___x_1759_ = lean_st_ref_get(v_a_1757_);
v_interestWaiter_1760_ = lean_ctor_get(v___x_1759_, 2);
lean_inc(v_interestWaiter_1760_);
if (lean_obj_tag(v_interestWaiter_1760_) == 1)
{
lean_object* v_pendingProducer_1761_; lean_object* v_pendingConsumer_1762_; uint8_t v_closed_1763_; lean_object* v_knownSize_1764_; lean_object* v_pendingIncompleteChunk_1765_; lean_object* v_closeError_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1778_; 
v_pendingProducer_1761_ = lean_ctor_get(v___x_1759_, 0);
v_pendingConsumer_1762_ = lean_ctor_get(v___x_1759_, 1);
v_closed_1763_ = lean_ctor_get_uint8(v___x_1759_, sizeof(void*)*6);
v_knownSize_1764_ = lean_ctor_get(v___x_1759_, 3);
v_pendingIncompleteChunk_1765_ = lean_ctor_get(v___x_1759_, 4);
v_closeError_1766_ = lean_ctor_get(v___x_1759_, 5);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v___x_1759_, 2);
lean_dec(v_unused_1779_);
v___x_1768_ = v___x_1759_;
v_isShared_1769_ = v_isSharedCheck_1778_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_closeError_1766_);
lean_inc(v_pendingIncompleteChunk_1765_);
lean_inc(v_knownSize_1764_);
lean_inc(v_pendingConsumer_1762_);
lean_inc(v_pendingProducer_1761_);
lean_dec(v___x_1759_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1778_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_val_1770_; uint8_t v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v_val_1770_ = lean_ctor_get(v_interestWaiter_1760_, 0);
lean_inc(v_val_1770_);
lean_dec_ref_known(v_interestWaiter_1760_, 1);
v___x_1771_ = 1;
v___x_1772_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1770_, v___x_1771_);
lean_dec(v_val_1770_);
v___x_1773_ = lean_box(0);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 2, v___x_1773_);
v___x_1775_ = v___x_1768_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_pendingProducer_1761_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_pendingConsumer_1762_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_knownSize_1764_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v_pendingIncompleteChunk_1765_);
lean_ctor_set(v_reuseFailAlloc_1777_, 5, v_closeError_1766_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*6, v_closed_1763_);
v___x_1775_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_st_ref_set(v_a_1757_, v___x_1775_);
return v___x_1776_;
}
}
}
else
{
lean_object* v___x_1780_; 
lean_dec(v_interestWaiter_1760_);
lean_dec(v___x_1759_);
v___x_1780_ = lean_box(0);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object* v_a_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_1781_);
lean_dec(v_a_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object* v_mutex_1784_, lean_object* v_k_1785_){
_start:
{
lean_object* v_ref_1787_; lean_object* v_mutex_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_ref_1787_ = lean_ctor_get(v_mutex_1784_, 0);
lean_inc(v_ref_1787_);
v_mutex_1788_ = lean_ctor_get(v_mutex_1784_, 1);
lean_inc(v_mutex_1788_);
lean_dec_ref(v_mutex_1784_);
v___x_1789_ = lean_io_basemutex_lock(v_mutex_1788_);
v___x_1790_ = lean_apply_2(v_k_1785_, v_ref_1787_, lean_box(0));
v___x_1791_ = lean_io_basemutex_unlock(v_mutex_1788_);
lean_dec(v_mutex_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object* v_mutex_1792_, lean_object* v_k_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1792_, v_k_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object* v_00_u03b1_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_mutex_1798_, lean_object* v_k_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1798_, v_k_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_00_u03b2_1803_, lean_object* v_mutex_1804_, lean_object* v_k_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(v_00_u03b1_1802_, v_00_u03b2_1803_, v_mutex_1804_, v_k_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object* v_x_1813_){
_start:
{
if (lean_obj_tag(v_x_1813_) == 0)
{
lean_object* v___x_1814_; 
v___x_1814_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2));
return v___x_1814_;
}
else
{
lean_object* v_val_1815_; 
v_val_1815_ = lean_ctor_get(v_x_1813_, 0);
lean_inc(v_val_1815_);
return v_val_1815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___boxed(lean_object* v_x_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(v_x_1816_);
lean_dec(v_x_1816_);
return v_res_1817_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2));
v___x_1824_ = lean_task_pure(v___x_1823_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_1826_ = lean_task_pure(v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object* v___f_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v_closed_1832_; 
v___x_1830_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_1828_);
v___x_1831_ = lean_st_ref_get(v___y_1828_);
v_closed_1832_ = lean_ctor_get_uint8(v___x_1831_, sizeof(void*)*6);
if (v_closed_1832_ == 0)
{
lean_object* v___x_1833_; 
lean_dec(v___x_1831_);
v___x_1833_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_1828_);
if (lean_obj_tag(v___x_1833_) == 1)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec_ref(v___f_1827_);
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
v___x_1835_ = lean_task_pure(v___x_1834_);
return v___x_1835_;
}
else
{
lean_object* v___x_1836_; lean_object* v_pendingConsumer_1837_; 
lean_dec(v___x_1833_);
v___x_1836_ = lean_st_ref_get(v___y_1828_);
v_pendingConsumer_1837_ = lean_ctor_get(v___x_1836_, 1);
lean_inc(v_pendingConsumer_1837_);
if (lean_obj_tag(v_pendingConsumer_1837_) == 0)
{
lean_object* v_pendingProducer_1838_; lean_object* v_interestWaiter_1839_; uint8_t v_closed_1840_; lean_object* v_knownSize_1841_; lean_object* v_pendingIncompleteChunk_1842_; lean_object* v_closeError_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1859_; 
v_pendingProducer_1838_ = lean_ctor_get(v___x_1836_, 0);
v_interestWaiter_1839_ = lean_ctor_get(v___x_1836_, 2);
v_closed_1840_ = lean_ctor_get_uint8(v___x_1836_, sizeof(void*)*6);
v_knownSize_1841_ = lean_ctor_get(v___x_1836_, 3);
v_pendingIncompleteChunk_1842_ = lean_ctor_get(v___x_1836_, 4);
v_closeError_1843_ = lean_ctor_get(v___x_1836_, 5);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1836_, 1);
lean_dec(v_unused_1860_);
v___x_1845_ = v___x_1836_;
v_isShared_1846_ = v_isSharedCheck_1859_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_closeError_1843_);
lean_inc(v_pendingIncompleteChunk_1842_);
lean_inc(v_knownSize_1841_);
lean_inc(v_interestWaiter_1839_);
lean_inc(v_pendingProducer_1838_);
lean_dec(v___x_1836_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1859_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1847_ = lean_io_promise_new();
lean_inc(v___x_1847_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v___x_1849_);
v___x_1851_ = v___x_1845_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_pendingProducer_1838_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_interestWaiter_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_knownSize_1841_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_pendingIncompleteChunk_1842_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v_closeError_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*6, v_closed_1840_);
v___x_1851_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1852_ = lean_st_ref_set(v___y_1828_, v___x_1851_);
v___x_1853_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_1828_);
v___x_1854_ = 1;
v___x_1855_ = lean_io_promise_result_opt(v___x_1847_);
lean_dec(v___x_1847_);
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = lean_task_map(v___f_1827_, v___x_1855_, v___x_1856_, v___x_1854_);
return v___x_1857_;
}
}
}
else
{
lean_object* v___x_1861_; 
lean_dec_ref_known(v_pendingConsumer_1837_, 1);
lean_dec(v___x_1836_);
lean_dec_ref(v___f_1827_);
v___x_1861_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3);
return v___x_1861_;
}
}
}
else
{
lean_object* v_closeError_1862_; 
lean_dec_ref(v___f_1827_);
v_closeError_1862_ = lean_ctor_get(v___x_1831_, 5);
lean_inc(v_closeError_1862_);
lean_dec(v___x_1831_);
if (lean_obj_tag(v_closeError_1862_) == 0)
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4);
return v___x_1863_;
}
else
{
lean_object* v_val_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1872_; 
v_val_1864_ = lean_ctor_get(v_closeError_1862_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_closeError_1862_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1866_ = v_closeError_1862_;
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_val_1864_);
lean_dec(v_closeError_1862_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set_tag(v___x_1866_, 0);
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_val_1864_);
v___x_1869_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_task_pure(v___x_1869_);
return v___x_1870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object* v___f_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(v___f_1873_, v___y_1874_);
lean_dec(v___y_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object* v_stream_1880_){
_start:
{
lean_object* v___f_1882_; lean_object* v___x_1883_; 
v___f_1882_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1));
v___x_1883_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_1880_, v___f_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object* v_stream_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object* v_x_1887_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_a_1889_ = lean_ctor_get(v_x_1887_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_x_1887_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1891_ = v_x_1887_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v_x_1887_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v_x_1887_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v_x_1887_, 1);
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v_a_1898_);
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object* v_x_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv(lean_object* v_stream_1904_){
_start:
{
lean_object* v___x_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; 
v___x_1906_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1904_);
v___f_1907_ = ((lean_object*)(l_Std_Http_Body_Stream_recv___closed__0));
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = 0;
v___x_1912_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1910_, v___x_1911_, v___x_1909_, v___f_1907_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object* v_stream_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Std_Http_Body_Stream_recv(v_stream_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(uint8_t v___x_1916_, lean_object* v_knownSize_1917_, lean_object* v_closeError_1918_, lean_object* v_____r_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1922_ = lean_box(0);
v___x_1923_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
lean_ctor_set(v___x_1923_, 2, v___x_1922_);
lean_ctor_set(v___x_1923_, 3, v_knownSize_1917_);
lean_ctor_set(v___x_1923_, 4, v___x_1922_);
lean_ctor_set(v___x_1923_, 5, v_closeError_1918_);
lean_ctor_set_uint8(v___x_1923_, sizeof(void*)*6, v___x_1916_);
v___x_1924_ = lean_st_ref_set(v___y_1920_, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(lean_object* v___x_1927_, lean_object* v_knownSize_1928_, lean_object* v_closeError_1929_, lean_object* v_____r_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
uint8_t v___x_2175__boxed_1933_; lean_object* v_res_1934_; 
v___x_2175__boxed_1933_ = lean_unbox(v___x_1927_);
v_res_1934_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(v___x_2175__boxed_1933_, v_knownSize_1928_, v_closeError_1929_, v_____r_1930_, v___y_1931_);
lean_dec(v___y_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(lean_object* v___f_1935_, lean_object* v___y_1936_, lean_object* v_x_1937_){
_start:
{
if (lean_obj_tag(v_x_1937_) == 0)
{
lean_object* v___x_1939_; 
lean_dec_ref(v___f_1935_);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v_x_1937_);
return v___x_1939_;
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1941_; 
v_a_1940_ = lean_ctor_get(v_x_1937_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v_x_1937_, 1);
lean_inc(v___y_1936_);
v___x_1941_ = lean_apply_3(v___f_1935_, v_a_1940_, v___y_1936_, lean_box(0));
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed(lean_object* v___f_1942_, lean_object* v___y_1943_, lean_object* v_x_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(v___f_1942_, v___y_1943_, v_x_1944_);
lean_dec(v___y_1943_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object* v_pendingProducer_1947_, uint8_t v_closed_1948_, lean_object* v___f_1949_, lean_object* v_____r_1950_, lean_object* v___y_1951_){
_start:
{
if (lean_obj_tag(v_pendingProducer_1947_) == 1)
{
lean_object* v_val_1953_; lean_object* v_done_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v_val_1953_ = lean_ctor_get(v_pendingProducer_1947_, 0);
v_done_1954_ = lean_ctor_get(v_val_1953_, 1);
v___x_1955_ = lean_box(v_closed_1948_);
v___x_1956_ = lean_io_promise_resolve(v___x_1955_, v_done_1954_);
lean_inc(v___y_1951_);
v___f_1957_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1957_, 0, v___f_1949_);
lean_closure_set(v___f_1957_, 1, v___y_1951_);
v___x_1958_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1959_, v_closed_1948_, v___x_1958_, v___f_1957_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_box(0);
lean_inc(v___y_1951_);
v___x_1962_ = lean_apply_3(v___f_1949_, v___x_1961_, v___y_1951_, lean_box(0));
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object* v_pendingProducer_1963_, lean_object* v_closed_1964_, lean_object* v___f_1965_, lean_object* v_____r_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
uint8_t v_closed_boxed_1969_; lean_object* v_res_1970_; 
v_closed_boxed_1969_ = lean_unbox(v_closed_1964_);
v_res_1970_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(v_pendingProducer_1963_, v_closed_boxed_1969_, v___f_1965_, v_____r_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec(v_pendingProducer_1963_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object* v_interestWaiter_1971_, uint8_t v_closed_1972_, lean_object* v___f_1973_, lean_object* v_____r_1974_, lean_object* v___y_1975_){
_start:
{
if (lean_obj_tag(v_interestWaiter_1971_) == 1)
{
lean_object* v_val_1977_; uint8_t v___x_1978_; lean_object* v___f_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_val_1977_ = lean_ctor_get(v_interestWaiter_1971_, 0);
v___x_1978_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1977_, v_closed_1972_);
lean_inc(v___y_1975_);
v___f_1979_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1979_, 0, v___f_1973_);
lean_closure_set(v___f_1979_, 1, v___y_1975_);
v___x_1980_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1981_, v_closed_1972_, v___x_1980_, v___f_1979_);
return v___x_1982_;
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_box(0);
lean_inc(v___y_1975_);
v___x_1984_ = lean_apply_3(v___f_1973_, v___x_1983_, v___y_1975_, lean_box(0));
return v___x_1984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(lean_object* v_interestWaiter_1985_, lean_object* v_closed_1986_, lean_object* v___f_1987_, lean_object* v_____r_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
uint8_t v_closed_boxed_1991_; lean_object* v_res_1992_; 
v_closed_boxed_1991_ = lean_unbox(v_closed_1986_);
v_res_1992_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_1985_, v_closed_boxed_1991_, v___f_1987_, v_____r_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec(v_interestWaiter_1985_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(lean_object* v___f_1993_, lean_object* v_a_1994_, lean_object* v_x_1995_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
lean_object* v___x_1997_; 
lean_dec_ref(v___f_1993_);
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_x_1995_);
return v___x_1997_;
}
else
{
lean_object* v_a_1998_; lean_object* v___x_1999_; 
v_a_1998_ = lean_ctor_get(v_x_1995_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v_x_1995_, 1);
lean_inc(v_a_1994_);
v___x_1999_ = lean_apply_3(v___f_1993_, v_a_1998_, v_a_1994_, lean_box(0));
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed(lean_object* v___f_2000_, lean_object* v_a_2001_, lean_object* v_x_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(v___f_2000_, v_a_2001_, v_x_2002_);
lean_dec(v_a_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(lean_object* v_a_2005_, lean_object* v_x_2006_){
_start:
{
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v_a_2008_ = lean_ctor_get(v_x_2006_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_x_2006_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2010_ = v_x_2006_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v_x_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2050_; 
v_a_2017_ = lean_ctor_get(v_x_2006_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_x_2006_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2019_ = v_x_2006_;
v_isShared_2020_ = v_isSharedCheck_2050_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v_x_2006_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2050_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
uint8_t v_closed_2021_; 
v_closed_2021_ = lean_ctor_get_uint8(v_a_2017_, sizeof(void*)*6);
if (v_closed_2021_ == 0)
{
lean_object* v_pendingProducer_2022_; lean_object* v_pendingConsumer_2023_; lean_object* v_interestWaiter_2024_; lean_object* v_knownSize_2025_; lean_object* v_closeError_2026_; uint8_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___f_2029_; lean_object* v___x_2030_; lean_object* v___f_2031_; lean_object* v___x_2032_; lean_object* v___f_2033_; 
v_pendingProducer_2022_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_pendingProducer_2022_);
v_pendingConsumer_2023_ = lean_ctor_get(v_a_2017_, 1);
lean_inc(v_pendingConsumer_2023_);
v_interestWaiter_2024_ = lean_ctor_get(v_a_2017_, 2);
lean_inc_n(v_interestWaiter_2024_, 2);
v_knownSize_2025_ = lean_ctor_get(v_a_2017_, 3);
lean_inc(v_knownSize_2025_);
v_closeError_2026_ = lean_ctor_get(v_a_2017_, 5);
lean_inc_n(v_closeError_2026_, 2);
lean_dec(v_a_2017_);
v___x_2027_ = 1;
v___x_2028_ = lean_box(v___x_2027_);
v___f_2029_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2029_, 0, v___x_2028_);
lean_closure_set(v___f_2029_, 1, v_knownSize_2025_);
lean_closure_set(v___f_2029_, 2, v_closeError_2026_);
v___x_2030_ = lean_box(v_closed_2021_);
v___f_2031_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2031_, 0, v_pendingProducer_2022_);
lean_closure_set(v___f_2031_, 1, v___x_2030_);
lean_closure_set(v___f_2031_, 2, v___f_2029_);
v___x_2032_ = lean_box(v_closed_2021_);
lean_inc_ref(v___f_2031_);
v___f_2033_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2033_, 0, v_interestWaiter_2024_);
lean_closure_set(v___f_2033_, 1, v___x_2032_);
lean_closure_set(v___f_2033_, 2, v___f_2031_);
if (lean_obj_tag(v_pendingConsumer_2023_) == 1)
{
lean_object* v_val_2034_; lean_object* v___f_2035_; lean_object* v___y_2037_; 
lean_dec_ref(v___f_2031_);
lean_dec(v_interestWaiter_2024_);
v_val_2034_ = lean_ctor_get(v_pendingConsumer_2023_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v_pendingConsumer_2023_, 1);
lean_inc(v_a_2005_);
v___f_2035_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2035_, 0, v___f_2033_);
lean_closure_set(v___f_2035_, 1, v_a_2005_);
if (lean_obj_tag(v_closeError_2026_) == 0)
{
lean_object* v___x_2042_; 
lean_del_object(v___x_2019_);
v___x_2042_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___y_2037_ = v___x_2042_;
goto v___jp_2036_;
}
else
{
lean_object* v_val_2043_; lean_object* v___x_2045_; 
v_val_2043_ = lean_ctor_get(v_closeError_2026_, 0);
lean_inc(v_val_2043_);
lean_dec_ref_known(v_closeError_2026_, 1);
if (v_isShared_2020_ == 0)
{
lean_ctor_set_tag(v___x_2019_, 0);
lean_ctor_set(v___x_2019_, 0, v_val_2043_);
v___x_2045_ = v___x_2019_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_val_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
v___y_2037_ = v___x_2045_;
goto v___jp_2036_;
}
}
v___jp_2036_:
{
uint8_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2038_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_2034_, v___y_2037_);
lean_dec(v_val_2034_);
v___x_2039_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2040_, v_closed_2021_, v___x_2039_, v___f_2035_);
return v___x_2041_;
}
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v___f_2033_);
lean_dec(v_closeError_2026_);
lean_dec(v_pendingConsumer_2023_);
lean_del_object(v___x_2019_);
v___x_2047_ = lean_box(0);
v___x_2048_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_2024_, v_closed_2021_, v___f_2031_, v___x_2047_, v_a_2005_);
lean_dec(v_interestWaiter_2024_);
return v___x_2048_;
}
}
else
{
lean_object* v___x_2049_; 
lean_del_object(v___x_2019_);
lean_dec(v_a_2017_);
v___x_2049_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
return v___x_2049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed(lean_object* v_a_2051_, lean_object* v_x_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(v_a_2051_, v_x_2052_);
lean_dec(v_a_2051_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v___f_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; 
v___x_2057_ = lean_st_ref_get(v_a_2055_);
lean_inc(v_a_2055_);
v___f_2058_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed), 3, 1);
lean_closure_set(v___f_2058_, 0, v_a_2055_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = 0;
v___x_2063_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2061_, v___x_2062_, v___x_2060_, v___f_2058_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed(lean_object* v_a_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v_a_2064_);
lean_dec(v_a_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close(lean_object* v_stream_2068_){
_start:
{
lean_object* v___f_2070_; lean_object* v___x_2071_; 
v___f_2070_ = ((lean_object*)(l_Std_Http_Body_Stream_close___closed__0));
v___x_2071_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2068_, v___f_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object* v_stream_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Std_Http_Body_Stream_close(v_stream_2072_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(uint8_t v___x_2075_, lean_object* v_x_2076_){
_start:
{
if (lean_obj_tag(v_x_2076_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2086_; 
v_a_2078_ = lean_ctor_get(v_x_2076_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_x_2076_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2080_ = v_x_2076_;
v_isShared_2081_ = v_isSharedCheck_2086_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v_x_2076_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2086_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
}
else
{
lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2095_; 
v_isSharedCheck_2095_ = !lean_is_exclusive(v_x_2076_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v_x_2076_, 0);
lean_dec(v_unused_2096_);
v___x_2088_ = v_x_2076_;
v_isShared_2089_ = v_isSharedCheck_2095_;
goto v_resetjp_2087_;
}
else
{
lean_dec(v_x_2076_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2095_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_box(v___x_2075_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2090_);
v___x_2092_ = v___x_2088_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0___boxed(lean_object* v___x_2097_, lean_object* v_x_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v___x_1490__boxed_2100_; lean_object* v_res_2101_; 
v___x_1490__boxed_2100_ = lean_unbox(v___x_2097_);
v_res_2101_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(v___x_1490__boxed_2100_, v_x_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(lean_object* v___y_2105_, lean_object* v_x_2106_){
_start:
{
uint8_t v___y_2109_; 
if (lean_obj_tag(v_x_2106_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2121_; 
v_a_2113_ = lean_ctor_get(v_x_2106_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_x_2106_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2115_ = v_x_2106_;
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v_x_2106_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
}
else
{
lean_object* v_a_2122_; uint8_t v_closed_2123_; 
v_a_2122_ = lean_ctor_get(v_x_2106_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v_x_2106_, 1);
v_closed_2123_ = lean_ctor_get_uint8(v_a_2122_, sizeof(void*)*6);
if (v_closed_2123_ == 0)
{
lean_object* v_pendingConsumer_2124_; 
v_pendingConsumer_2124_ = lean_ctor_get(v_a_2122_, 1);
lean_inc(v_pendingConsumer_2124_);
lean_dec(v_a_2122_);
if (lean_obj_tag(v_pendingConsumer_2124_) == 0)
{
lean_object* v___x_2125_; lean_object* v___f_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2125_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v___y_2105_);
v___f_2126_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0));
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2127_, v_closed_2123_, v___x_2125_, v___f_2126_);
return v___x_2128_;
}
else
{
lean_dec_ref_known(v_pendingConsumer_2124_, 1);
v___y_2109_ = v_closed_2123_;
goto v___jp_2108_;
}
}
else
{
uint8_t v___x_2129_; 
lean_dec(v_a_2122_);
v___x_2129_ = 0;
v___y_2109_ = v___x_2129_;
goto v___jp_2108_;
}
}
v___jp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = lean_box(v___y_2109_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed(lean_object* v___y_2130_, lean_object* v_x_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(v___y_2130_, v_x_2131_);
lean_dec(v___y_2130_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(lean_object* v___y_2134_, lean_object* v___f_2135_, lean_object* v_x_2136_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v___f_2135_);
v_a_2138_ = lean_ctor_get(v_x_2136_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_x_2136_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2140_ = v_x_2136_;
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v_x_2136_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
return v___x_2144_;
}
}
}
else
{
lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2158_; 
v_isSharedCheck_2158_ = !lean_is_exclusive(v_x_2136_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v_x_2136_, 0);
lean_dec(v_unused_2159_);
v___x_2148_ = v_x_2136_;
v_isShared_2149_ = v_isSharedCheck_2158_;
goto v_resetjp_2147_;
}
else
{
lean_dec(v_x_2136_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2158_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_st_ref_get(v___y_2134_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; 
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = 0;
v___x_2156_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2154_, v___x_2155_, v___x_2153_, v___f_2135_);
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed(lean_object* v___y_2160_, lean_object* v___f_2161_, lean_object* v_x_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(v___y_2160_, v___f_2161_, v_x_2162_);
lean_dec(v___y_2160_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v___f_2168_; lean_object* v___f_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2167_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2165_);
lean_inc_n(v___y_2165_, 2);
v___f_2168_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2168_, 0, v___y_2165_);
v___f_2169_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2169_, 0, v___y_2165_);
lean_closure_set(v___f_2169_, 1, v___f_2168_);
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = 0;
v___x_2172_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2170_, v___x_2171_, v___x_2167_, v___f_2169_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3___boxed(lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(v___y_2173_);
lean_dec(v___y_2173_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned(lean_object* v_stream_2177_){
_start:
{
lean_object* v___f_2179_; lean_object* v___x_2180_; 
v___f_2179_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___closed__0));
v___x_2180_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2177_, v___f_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___boxed(lean_object* v_stream_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Std_Http_Body_Stream_closeIfAbandoned(v_stream_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0(lean_object* v___y_2184_, lean_object* v_x_2185_){
_start:
{
if (lean_obj_tag(v_x_2185_) == 0)
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_x_2185_);
return v___x_2187_;
}
else
{
lean_object* v___x_2188_; 
lean_dec_ref_known(v_x_2185_, 1);
v___x_2188_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v___y_2184_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0___boxed(lean_object* v___y_2189_, lean_object* v_x_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Std_Http_Body_Stream_closeWithError___lam__0(v___y_2189_, v_x_2190_);
lean_dec(v___y_2189_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1(lean_object* v_err_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; lean_object* v_pendingProducer_2197_; lean_object* v_pendingConsumer_2198_; lean_object* v_interestWaiter_2199_; uint8_t v_closed_2200_; lean_object* v_knownSize_2201_; lean_object* v_pendingIncompleteChunk_2202_; lean_object* v_closeError_2203_; lean_object* v___f_2204_; lean_object* v_fst_2206_; lean_object* v_snd_2207_; lean_object* v___x_2214_; 
v___x_2196_ = lean_st_ref_take(v___y_2194_);
v_pendingProducer_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_pendingProducer_2197_);
v_pendingConsumer_2198_ = lean_ctor_get(v___x_2196_, 1);
lean_inc(v_pendingConsumer_2198_);
v_interestWaiter_2199_ = lean_ctor_get(v___x_2196_, 2);
lean_inc(v_interestWaiter_2199_);
v_closed_2200_ = lean_ctor_get_uint8(v___x_2196_, sizeof(void*)*6);
v_knownSize_2201_ = lean_ctor_get(v___x_2196_, 3);
lean_inc(v_knownSize_2201_);
v_pendingIncompleteChunk_2202_ = lean_ctor_get(v___x_2196_, 4);
lean_inc(v_pendingIncompleteChunk_2202_);
v_closeError_2203_ = lean_ctor_get(v___x_2196_, 5);
lean_inc(v_closeError_2203_);
lean_inc(v___y_2194_);
v___f_2204_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2204_, 0, v___y_2194_);
v___x_2214_ = lean_box(0);
if (lean_obj_tag(v_closeError_2203_) == 0)
{
lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2222_; 
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; lean_object* v_unused_2224_; lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; lean_object* v_unused_2228_; 
v_unused_2223_ = lean_ctor_get(v___x_2196_, 5);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v___x_2196_, 4);
lean_dec(v_unused_2224_);
v_unused_2225_ = lean_ctor_get(v___x_2196_, 3);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v___x_2196_, 2);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v___x_2196_, 1);
lean_dec(v_unused_2227_);
v_unused_2228_ = lean_ctor_get(v___x_2196_, 0);
lean_dec(v_unused_2228_);
v___x_2216_ = v___x_2196_;
v_isShared_2217_ = v_isSharedCheck_2222_;
goto v_resetjp_2215_;
}
else
{
lean_dec(v___x_2196_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2222_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2218_, 0, v_err_2193_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 5, v___x_2218_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_pendingProducer_2197_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_pendingConsumer_2198_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_interestWaiter_2199_);
lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_knownSize_2201_);
lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_pendingIncompleteChunk_2202_);
lean_ctor_set(v_reuseFailAlloc_2221_, 5, v___x_2218_);
lean_ctor_set_uint8(v_reuseFailAlloc_2221_, sizeof(void*)*6, v_closed_2200_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
v_fst_2206_ = v___x_2214_;
v_snd_2207_ = v___x_2220_;
goto v___jp_2205_;
}
}
}
else
{
lean_dec_ref_known(v_closeError_2203_, 1);
lean_dec(v_pendingIncompleteChunk_2202_);
lean_dec(v_knownSize_2201_);
lean_dec(v_interestWaiter_2199_);
lean_dec(v_pendingConsumer_2198_);
lean_dec(v_pendingProducer_2197_);
lean_dec(v_err_2193_);
v_fst_2206_ = v___x_2214_;
v_snd_2207_ = v___x_2196_;
goto v___jp_2205_;
}
v___jp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; lean_object* v___x_2213_; 
v___x_2208_ = lean_st_ref_set(v___y_2194_, v_snd_2207_);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_fst_2206_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = 0;
v___x_2213_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2211_, v___x_2212_, v___x_2210_, v___f_2204_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1___boxed(lean_object* v_err_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Std_Http_Body_Stream_closeWithError___lam__1(v_err_2229_, v___y_2230_);
lean_dec(v___y_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError(lean_object* v_stream_2233_, lean_object* v_err_2234_){
_start:
{
lean_object* v___f_2236_; lean_object* v___x_2237_; 
v___f_2236_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2236_, 0, v_err_2234_);
v___x_2237_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2233_, v___f_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___boxed(lean_object* v_stream_2238_, lean_object* v_err_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Std_Http_Body_Stream_closeWithError(v_stream_2238_, v_err_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object* v_____do__lift_2242_, lean_object* v___y_2243_){
_start:
{
uint8_t v_closed_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_closed_2245_ = lean_ctor_get_uint8(v_____do__lift_2242_, sizeof(void*)*6);
v___x_2246_ = lean_box(v_closed_2245_);
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object* v_____do__lift_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v_____do__lift_2249_);
return v_res_2252_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__1(void){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_2254_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__2(void){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_2255_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__6(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; 
v___x_2261_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2262_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___f_2263_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2263_, 0, v___f_2262_);
lean_closure_set(v___f_2263_, 1, v___x_2261_);
return v___f_2263_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__11(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___f_2273_; lean_object* v___f_2274_; 
v___x_2272_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2273_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__10));
v___f_2274_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2274_, 0, v___f_2273_);
lean_closure_set(v___f_2274_, 1, v___x_2272_);
return v___f_2274_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__12(void){
_start:
{
lean_object* v___f_2275_; lean_object* v___x_2276_; 
v___f_2275_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__11, &l_Std_Http_Body_Stream_isClosed___closed__11_once, _init_l_Std_Http_Body_Stream_isClosed___closed__11);
v___x_2276_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2276_, 0, lean_box(0));
lean_closure_set(v___x_2276_, 1, lean_box(0));
lean_closure_set(v___x_2276_, 2, lean_box(0));
lean_closure_set(v___x_2276_, 3, v___f_2275_);
return v___x_2276_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__13(void){
_start:
{
lean_object* v___f_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___f_2277_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__0));
v___x_2278_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2279_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2280_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2280_, 0, lean_box(0));
lean_closure_set(v___x_2280_, 1, lean_box(0));
lean_closure_set(v___x_2280_, 2, v___x_2279_);
lean_closure_set(v___x_2280_, 3, lean_box(0));
lean_closure_set(v___x_2280_, 4, lean_box(0));
lean_closure_set(v___x_2280_, 5, v___x_2278_);
lean_closure_set(v___x_2280_, 6, v___f_2277_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed(lean_object* v_stream_2281_){
_start:
{
lean_object* v___x_2283_; lean_object* v___f_2284_; lean_object* v___f_2285_; lean_object* v___x_2286_; lean_object* v___x_29__overap_2287_; lean_object* v___x_2288_; 
v___x_2283_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2284_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2285_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2286_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__13, &l_Std_Http_Body_Stream_isClosed___closed__13_once, _init_l_Std_Http_Body_Stream_isClosed___closed__13);
v___x_29__overap_2287_ = l_Std_Mutex_atomically___redArg(v___x_2283_, v___f_2284_, v___f_2285_, v_stream_2281_, v___x_2286_);
v___x_2288_ = lean_apply_1(v___x_29__overap_2287_, lean_box(0));
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___boxed(lean_object* v_stream_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Std_Http_Body_Stream_isClosed(v_stream_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0(lean_object* v_____do__lift_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_knownSize_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_knownSize_2295_ = lean_ctor_get(v_____do__lift_2292_, 3);
lean_inc(v_knownSize_2295_);
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_knownSize_2295_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(lean_object* v_____do__lift_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v_____do__lift_2298_);
return v_res_2301_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_getKnownSize___closed__1(void){
_start:
{
lean_object* v___f_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___f_2303_ = ((lean_object*)(l_Std_Http_Body_Stream_getKnownSize___closed__0));
v___x_2304_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2305_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2306_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2306_, 0, lean_box(0));
lean_closure_set(v___x_2306_, 1, lean_box(0));
lean_closure_set(v___x_2306_, 2, v___x_2305_);
lean_closure_set(v___x_2306_, 3, lean_box(0));
lean_closure_set(v___x_2306_, 4, lean_box(0));
lean_closure_set(v___x_2306_, 5, v___x_2304_);
lean_closure_set(v___x_2306_, 6, v___f_2303_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize(lean_object* v_stream_2307_){
_start:
{
lean_object* v___x_2309_; lean_object* v___f_2310_; lean_object* v___f_2311_; lean_object* v___x_2312_; lean_object* v___x_29__overap_2313_; lean_object* v___x_2314_; 
v___x_2309_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2310_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2311_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2312_ = lean_obj_once(&l_Std_Http_Body_Stream_getKnownSize___closed__1, &l_Std_Http_Body_Stream_getKnownSize___closed__1_once, _init_l_Std_Http_Body_Stream_getKnownSize___closed__1);
v___x_29__overap_2313_ = l_Std_Mutex_atomically___redArg(v___x_2309_, v___f_2310_, v___f_2311_, v_stream_2307_, v___x_2312_);
v___x_2314_ = lean_apply_1(v___x_29__overap_2313_, lean_box(0));
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___boxed(lean_object* v_stream_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0(lean_object* v_size_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; lean_object* v_pendingProducer_2322_; lean_object* v_pendingConsumer_2323_; lean_object* v_interestWaiter_2324_; uint8_t v_closed_2325_; lean_object* v_pendingIncompleteChunk_2326_; lean_object* v_closeError_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2336_; 
v___x_2321_ = lean_st_ref_take(v___y_2319_);
v_pendingProducer_2322_ = lean_ctor_get(v___x_2321_, 0);
v_pendingConsumer_2323_ = lean_ctor_get(v___x_2321_, 1);
v_interestWaiter_2324_ = lean_ctor_get(v___x_2321_, 2);
v_closed_2325_ = lean_ctor_get_uint8(v___x_2321_, sizeof(void*)*6);
v_pendingIncompleteChunk_2326_ = lean_ctor_get(v___x_2321_, 4);
v_closeError_2327_ = lean_ctor_get(v___x_2321_, 5);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; 
v_unused_2337_ = lean_ctor_get(v___x_2321_, 3);
lean_dec(v_unused_2337_);
v___x_2329_ = v___x_2321_;
v_isShared_2330_ = v_isSharedCheck_2336_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_closeError_2327_);
lean_inc(v_pendingIncompleteChunk_2326_);
lean_inc(v_interestWaiter_2324_);
lean_inc(v_pendingConsumer_2323_);
lean_inc(v_pendingProducer_2322_);
lean_dec(v___x_2321_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2336_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 3, v_size_2318_);
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_pendingProducer_2322_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_pendingConsumer_2323_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_interestWaiter_2324_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_size_2318_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_pendingIncompleteChunk_2326_);
lean_ctor_set(v_reuseFailAlloc_2335_, 5, v_closeError_2327_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*6, v_closed_2325_);
v___x_2332_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_st_ref_set(v___y_2319_, v___x_2332_);
v___x_2334_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
return v___x_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(lean_object* v_size_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_2338_, v___y_2339_);
lean_dec(v___y_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize(lean_object* v_stream_2342_, lean_object* v_size_2343_){
_start:
{
lean_object* v___f_2345_; lean_object* v___x_2346_; lean_object* v___f_2347_; lean_object* v___f_2348_; lean_object* v___x_26__overap_2349_; lean_object* v___x_2350_; 
v___f_2345_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2345_, 0, v_size_2343_);
v___x_2346_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2347_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2348_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_26__overap_2349_ = l_Std_Mutex_atomically___redArg(v___x_2346_, v___f_2347_, v___f_2348_, v_stream_2342_, v___f_2345_);
v___x_2350_ = lean_apply_1(v___x_26__overap_2349_, lean_box(0));
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___boxed(lean_object* v_stream_2351_, lean_object* v_size_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_2351_, v_size_2352_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object* v_pendingProducer_2355_, lean_object* v_pendingConsumer_2356_, uint8_t v_closed_2357_, lean_object* v_knownSize_2358_, lean_object* v_pendingIncompleteChunk_2359_, lean_object* v_closeError_2360_, lean_object* v_a_2361_, lean_object* v_x_2362_){
_start:
{
if (lean_obj_tag(v_x_2362_) == 0)
{
lean_object* v___x_2364_; 
lean_dec(v_closeError_2360_);
lean_dec(v_pendingIncompleteChunk_2359_);
lean_dec(v_knownSize_2358_);
lean_dec(v_pendingConsumer_2356_);
lean_dec(v_pendingProducer_2355_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v_x_2362_);
return v___x_2364_;
}
else
{
lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2375_; 
v_isSharedCheck_2375_ = !lean_is_exclusive(v_x_2362_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v_x_2362_, 0);
lean_dec(v_unused_2376_);
v___x_2366_ = v_x_2362_;
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v_x_2362_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2369_, 0, v_pendingProducer_2355_);
lean_ctor_set(v___x_2369_, 1, v_pendingConsumer_2356_);
lean_ctor_set(v___x_2369_, 2, v___x_2368_);
lean_ctor_set(v___x_2369_, 3, v_knownSize_2358_);
lean_ctor_set(v___x_2369_, 4, v_pendingIncompleteChunk_2359_);
lean_ctor_set(v___x_2369_, 5, v_closeError_2360_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*6, v_closed_2357_);
v___x_2370_ = lean_st_ref_set(v_a_2361_, v___x_2369_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2370_);
v___x_2372_ = v___x_2366_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object* v_pendingProducer_2377_, lean_object* v_pendingConsumer_2378_, lean_object* v_closed_2379_, lean_object* v_knownSize_2380_, lean_object* v_pendingIncompleteChunk_2381_, lean_object* v_closeError_2382_, lean_object* v_a_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v_closed_boxed_2386_; lean_object* v_res_2387_; 
v_closed_boxed_2386_ = lean_unbox(v_closed_2379_);
v_res_2387_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_2377_, v_pendingConsumer_2378_, v_closed_boxed_2386_, v_knownSize_2380_, v_pendingIncompleteChunk_2381_, v_closeError_2382_, v_a_2383_, v_x_2384_);
lean_dec(v_a_2383_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object* v_a_2388_, lean_object* v_x_2389_){
_start:
{
if (lean_obj_tag(v_x_2389_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2399_; 
v_a_2391_ = lean_ctor_get(v_x_2389_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_x_2389_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2393_ = v_x_2389_;
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v_x_2389_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v_interestWaiter_2401_; 
v_a_2400_ = lean_ctor_get(v_x_2389_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v_x_2389_, 1);
v_interestWaiter_2401_ = lean_ctor_get(v_a_2400_, 2);
lean_inc(v_interestWaiter_2401_);
if (lean_obj_tag(v_interestWaiter_2401_) == 1)
{
lean_object* v_pendingProducer_2402_; lean_object* v_pendingConsumer_2403_; uint8_t v_closed_2404_; lean_object* v_knownSize_2405_; lean_object* v_pendingIncompleteChunk_2406_; lean_object* v_closeError_2407_; lean_object* v_val_2408_; uint8_t v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___f_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; 
v_pendingProducer_2402_ = lean_ctor_get(v_a_2400_, 0);
lean_inc(v_pendingProducer_2402_);
v_pendingConsumer_2403_ = lean_ctor_get(v_a_2400_, 1);
lean_inc(v_pendingConsumer_2403_);
v_closed_2404_ = lean_ctor_get_uint8(v_a_2400_, sizeof(void*)*6);
v_knownSize_2405_ = lean_ctor_get(v_a_2400_, 3);
lean_inc(v_knownSize_2405_);
v_pendingIncompleteChunk_2406_ = lean_ctor_get(v_a_2400_, 4);
lean_inc(v_pendingIncompleteChunk_2406_);
v_closeError_2407_ = lean_ctor_get(v_a_2400_, 5);
lean_inc(v_closeError_2407_);
lean_dec(v_a_2400_);
v_val_2408_ = lean_ctor_get(v_interestWaiter_2401_, 0);
lean_inc(v_val_2408_);
lean_dec_ref_known(v_interestWaiter_2401_, 1);
v___x_2409_ = 1;
v___x_2410_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2408_, v___x_2409_);
lean_dec(v_val_2408_);
v___x_2411_ = lean_box(v_closed_2404_);
lean_inc(v_a_2388_);
v___f_2412_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed), 9, 7);
lean_closure_set(v___f_2412_, 0, v_pendingProducer_2402_);
lean_closure_set(v___f_2412_, 1, v_pendingConsumer_2403_);
lean_closure_set(v___f_2412_, 2, v___x_2411_);
lean_closure_set(v___f_2412_, 3, v_knownSize_2405_);
lean_closure_set(v___f_2412_, 4, v_pendingIncompleteChunk_2406_);
lean_closure_set(v___f_2412_, 5, v_closeError_2407_);
lean_closure_set(v___f_2412_, 6, v_a_2388_);
v___x_2413_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = 0;
v___x_2416_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2414_, v___x_2415_, v___x_2413_, v___f_2412_);
return v___x_2416_;
}
else
{
lean_object* v___x_2417_; 
lean_dec(v_interestWaiter_2401_);
lean_dec(v_a_2400_);
v___x_2417_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
return v___x_2417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object* v_a_2418_, lean_object* v_x_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_2418_, v_x_2419_);
lean_dec(v_a_2418_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2424_; lean_object* v___f_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; 
v___x_2424_ = lean_st_ref_get(v_a_2422_);
lean_inc(v_a_2422_);
v___f_2425_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2425_, 0, v_a_2422_);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = 0;
v___x_2430_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2428_, v___x_2429_, v___x_2427_, v___f_2425_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object* v_a_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_2431_);
lean_dec(v_a_2431_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object* v_promise_2434_, lean_object* v_x_2435_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2445_; 
v_a_2437_ = lean_ctor_get(v_x_2435_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_x_2435_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2439_ = v_x_2435_;
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v_x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2437_);
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
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2455_; 
v_a_2446_ = lean_ctor_get(v_x_2435_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_x_2435_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2448_ = v_x_2435_;
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v_x_2435_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_io_promise_resolve(v_a_2446_, v_promise_2434_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2450_);
v___x_2452_ = v___x_2448_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_2456_, lean_object* v_x_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(v_promise_2456_, v_x_2457_);
lean_dec(v_promise_2456_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object* v_lose_2460_, lean_object* v___y_2461_, lean_object* v___f_2462_, lean_object* v_x_2463_){
_start:
{
if (lean_obj_tag(v_x_2463_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v___f_2462_);
lean_dec_ref(v_lose_2460_);
v_a_2465_ = lean_ctor_get(v_x_2463_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_x_2463_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2467_ = v_x_2463_;
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v_x_2463_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
}
}
else
{
lean_object* v_a_2474_; uint8_t v___x_2475_; 
v_a_2474_ = lean_ctor_get(v_x_2463_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v_x_2463_, 1);
v___x_2475_ = lean_unbox(v_a_2474_);
lean_dec(v_a_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; 
lean_dec_ref(v___f_2462_);
lean_inc(v___y_2461_);
v___x_2476_ = lean_apply_2(v_lose_2460_, v___y_2461_, lean_box(0));
return v___x_2476_;
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; 
lean_dec_ref(v_lose_2460_);
v___x_2477_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2461_);
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = 0;
v___x_2480_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2478_, v___x_2479_, v___x_2477_, v___f_2462_);
return v___x_2480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object* v_lose_2481_, lean_object* v___y_2482_, lean_object* v___f_2483_, lean_object* v_x_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(v_lose_2481_, v___y_2482_, v___f_2483_, v_x_2484_);
lean_dec(v___y_2482_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object* v_w_2487_, lean_object* v_lose_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_finished_2491_; lean_object* v_promise_2492_; lean_object* v___x_2493_; lean_object* v___f_2494_; lean_object* v___f_2495_; uint8_t v___y_2497_; uint8_t v___x_2507_; 
v_finished_2491_ = lean_ctor_get(v_w_2487_, 0);
lean_inc(v_finished_2491_);
v_promise_2492_ = lean_ctor_get(v_w_2487_, 1);
lean_inc(v_promise_2492_);
lean_dec_ref(v_w_2487_);
v___x_2493_ = lean_st_ref_take(v_finished_2491_);
v___f_2494_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2494_, 0, v_promise_2492_);
lean_inc(v___y_2489_);
v___f_2495_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2495_, 0, v_lose_2488_);
lean_closure_set(v___f_2495_, 1, v___y_2489_);
lean_closure_set(v___f_2495_, 2, v___f_2494_);
v___x_2507_ = lean_unbox(v___x_2493_);
lean_dec(v___x_2493_);
if (v___x_2507_ == 0)
{
uint8_t v___x_2508_; 
v___x_2508_ = 1;
v___y_2497_ = v___x_2508_;
goto v___jp_2496_;
}
else
{
uint8_t v___x_2509_; 
v___x_2509_ = 0;
v___y_2497_ = v___x_2509_;
goto v___jp_2496_;
}
v___jp_2496_:
{
uint8_t v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; 
v___x_2498_ = 1;
v___x_2499_ = lean_box(v___x_2498_);
v___x_2500_ = lean_st_ref_set(v_finished_2491_, v___x_2499_);
lean_dec(v_finished_2491_);
v___x_2501_ = lean_box(v___y_2497_);
v___x_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
v___x_2504_ = lean_unsigned_to_nat(0u);
v___x_2505_ = 0;
v___x_2506_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2504_, v___x_2505_, v___x_2503_, v___f_2495_);
return v___x_2506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object* v_w_2510_, lean_object* v_lose_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_2510_, v_lose_2511_, v___y_2512_);
lean_dec(v___y_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object* v___y_2515_, lean_object* v_x_2516_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_x_2516_);
return v___x_2518_;
}
else
{
lean_object* v___x_2519_; 
lean_dec_ref_known(v_x_2516_, 1);
v___x_2519_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_2515_);
return v___x_2519_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object* v___y_2520_, lean_object* v_x_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_2520_, v_x_2521_);
lean_dec(v___y_2520_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object* v_waiter_2524_, lean_object* v_pendingProducer_2525_, lean_object* v_interestWaiter_2526_, uint8_t v_closed_2527_, lean_object* v_knownSize_2528_, lean_object* v_pendingIncompleteChunk_2529_, lean_object* v_closeError_2530_, uint8_t v_a_2531_, lean_object* v_____r_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_waiter_2524_);
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
v___x_2537_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2537_, 0, v_pendingProducer_2525_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
lean_ctor_set(v___x_2537_, 2, v_interestWaiter_2526_);
lean_ctor_set(v___x_2537_, 3, v_knownSize_2528_);
lean_ctor_set(v___x_2537_, 4, v_pendingIncompleteChunk_2529_);
lean_ctor_set(v___x_2537_, 5, v_closeError_2530_);
lean_ctor_set_uint8(v___x_2537_, sizeof(void*)*6, v_closed_2527_);
v___x_2538_ = lean_st_ref_set(v___y_2533_, v___x_2537_);
lean_inc(v___y_2533_);
v___f_2539_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2539_, 0, v___y_2533_);
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2542_, v_a_2531_, v___x_2541_, v___f_2539_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object* v_waiter_2544_, lean_object* v_pendingProducer_2545_, lean_object* v_interestWaiter_2546_, lean_object* v_closed_2547_, lean_object* v_knownSize_2548_, lean_object* v_pendingIncompleteChunk_2549_, lean_object* v_closeError_2550_, lean_object* v_a_2551_, lean_object* v_____r_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
uint8_t v_closed_boxed_2555_; uint8_t v_a_6248__boxed_2556_; lean_object* v_res_2557_; 
v_closed_boxed_2555_ = lean_unbox(v_closed_2547_);
v_a_6248__boxed_2556_ = lean_unbox(v_a_2551_);
v_res_2557_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2544_, v_pendingProducer_2545_, v_interestWaiter_2546_, v_closed_boxed_2555_, v_knownSize_2548_, v_pendingIncompleteChunk_2549_, v_closeError_2550_, v_a_6248__boxed_2556_, v_____r_2552_, v___y_2553_);
lean_dec(v___y_2553_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object* v_waiter_2562_, uint8_t v_a_2563_, lean_object* v___y_2564_, lean_object* v_x_2565_){
_start:
{
if (lean_obj_tag(v_x_2565_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2575_; 
lean_dec_ref(v_waiter_2562_);
v_a_2567_ = lean_ctor_get(v_x_2565_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_x_2565_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2569_ = v_x_2565_;
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v_x_2565_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
return v___x_2573_;
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v_pendingProducer_2577_; lean_object* v_pendingConsumer_2578_; lean_object* v_interestWaiter_2579_; uint8_t v_closed_2580_; lean_object* v_knownSize_2581_; lean_object* v_pendingIncompleteChunk_2582_; lean_object* v_closeError_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___f_2586_; 
v_a_2576_ = lean_ctor_get(v_x_2565_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v_x_2565_, 1);
v_pendingProducer_2577_ = lean_ctor_get(v_a_2576_, 0);
lean_inc_n(v_pendingProducer_2577_, 2);
v_pendingConsumer_2578_ = lean_ctor_get(v_a_2576_, 1);
lean_inc(v_pendingConsumer_2578_);
v_interestWaiter_2579_ = lean_ctor_get(v_a_2576_, 2);
lean_inc_n(v_interestWaiter_2579_, 2);
v_closed_2580_ = lean_ctor_get_uint8(v_a_2576_, sizeof(void*)*6);
v_knownSize_2581_ = lean_ctor_get(v_a_2576_, 3);
lean_inc_n(v_knownSize_2581_, 2);
v_pendingIncompleteChunk_2582_ = lean_ctor_get(v_a_2576_, 4);
lean_inc_n(v_pendingIncompleteChunk_2582_, 2);
v_closeError_2583_ = lean_ctor_get(v_a_2576_, 5);
lean_inc_n(v_closeError_2583_, 2);
lean_dec(v_a_2576_);
v___x_2584_ = lean_box(v_closed_2580_);
v___x_2585_ = lean_box(v_a_2563_);
lean_inc_ref(v_waiter_2562_);
v___f_2586_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__0___boxed), 11, 8);
lean_closure_set(v___f_2586_, 0, v_waiter_2562_);
lean_closure_set(v___f_2586_, 1, v_pendingProducer_2577_);
lean_closure_set(v___f_2586_, 2, v_interestWaiter_2579_);
lean_closure_set(v___f_2586_, 3, v___x_2584_);
lean_closure_set(v___f_2586_, 4, v_knownSize_2581_);
lean_closure_set(v___f_2586_, 5, v_pendingIncompleteChunk_2582_);
lean_closure_set(v___f_2586_, 6, v_closeError_2583_);
lean_closure_set(v___f_2586_, 7, v___x_2585_);
if (lean_obj_tag(v_pendingConsumer_2578_) == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec_ref(v___f_2586_);
v___x_2587_ = lean_box(0);
v___x_2588_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2562_, v_pendingProducer_2577_, v_interestWaiter_2579_, v_closed_2580_, v_knownSize_2581_, v_pendingIncompleteChunk_2582_, v_closeError_2583_, v_a_2563_, v___x_2587_, v___y_2564_);
return v___x_2588_;
}
else
{
lean_object* v___f_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec_ref_known(v_pendingConsumer_2578_, 1);
lean_dec(v_closeError_2583_);
lean_dec(v_pendingIncompleteChunk_2582_);
lean_dec(v_knownSize_2581_);
lean_dec(v_interestWaiter_2579_);
lean_dec(v_pendingProducer_2577_);
lean_dec_ref(v_waiter_2562_);
lean_inc(v___y_2564_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2589_, 0, v___f_2586_);
lean_closure_set(v___f_2589_, 1, v___y_2564_);
v___x_2590_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1));
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2591_, v_a_2563_, v___x_2590_, v___f_2589_);
return v___x_2592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object* v_waiter_2593_, lean_object* v_a_2594_, lean_object* v___y_2595_, lean_object* v_x_2596_, lean_object* v___y_2597_){
_start:
{
uint8_t v_a_6289__boxed_2598_; lean_object* v_res_2599_; 
v_a_6289__boxed_2598_ = lean_unbox(v_a_2594_);
v_res_2599_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v_waiter_2593_, v_a_6289__boxed_2598_, v___y_2595_, v_x_2596_);
lean_dec(v___y_2595_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object* v___x_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2600_);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object* v___x_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_2605_, v___y_2606_);
lean_dec(v___y_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object* v___y_2611_, lean_object* v_waiter_2612_, lean_object* v_x_2613_){
_start:
{
if (lean_obj_tag(v_x_2613_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_waiter_2612_);
v_a_2615_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2617_ = v_x_2613_;
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v_x_2613_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2621_; 
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
return v___x_2621_;
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2640_; 
v_a_2624_ = lean_ctor_get(v_x_2613_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2626_ = v_x_2613_;
v_isShared_2627_ = v_isSharedCheck_2640_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v_x_2613_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2640_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_unbox(v_a_2624_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___f_2630_; lean_object* v___x_2632_; 
v___x_2629_ = lean_st_ref_get(v___y_2611_);
lean_inc(v___y_2611_);
lean_inc(v_a_2624_);
v___f_2630_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2630_, 0, v_waiter_2612_);
lean_closure_set(v___f_2630_, 1, v_a_2624_);
lean_closure_set(v___f_2630_, 2, v___y_2611_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2629_);
v___x_2632_ = v___x_2626_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2629_);
v___x_2632_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; 
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_unbox(v_a_2624_);
lean_dec(v_a_2624_);
v___x_2636_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2634_, v___x_2635_, v___x_2633_, v___f_2630_);
return v___x_2636_;
}
}
else
{
lean_object* v___f_2638_; lean_object* v___x_2639_; 
lean_del_object(v___x_2626_);
lean_dec(v_a_2624_);
v___f_2638_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_2639_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_waiter_2612_, v___f_2638_, v___y_2611_);
return v___x_2639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object* v___y_2641_, lean_object* v_waiter_2642_, lean_object* v_x_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v___y_2641_, v_waiter_2642_, v_x_2643_);
lean_dec(v___y_2641_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object* v___y_2646_, lean_object* v___f_2647_, lean_object* v_x_2648_){
_start:
{
if (lean_obj_tag(v_x_2648_) == 0)
{
lean_object* v___x_2650_; 
lean_dec_ref(v___f_2647_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_x_2648_);
return v___x_2650_;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; 
lean_dec_ref_known(v_x_2648_, 1);
v___x_2651_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_2646_);
v___x_2652_ = lean_unsigned_to_nat(0u);
v___x_2653_ = 0;
v___x_2654_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2652_, v___x_2653_, v___x_2651_, v___f_2647_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object* v___y_2655_, lean_object* v___f_2656_, lean_object* v_x_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_2655_, v___f_2656_, v_x_2657_);
lean_dec(v___y_2655_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object* v_waiter_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; lean_object* v___f_2664_; lean_object* v___f_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2663_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2661_);
lean_inc_n(v___y_2661_, 2);
v___f_2664_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__4___boxed), 4, 2);
lean_closure_set(v___f_2664_, 0, v___y_2661_);
lean_closure_set(v___f_2664_, 1, v_waiter_2660_);
v___f_2665_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2665_, 0, v___y_2661_);
lean_closure_set(v___f_2665_, 1, v___f_2664_);
v___x_2666_ = lean_unsigned_to_nat(0u);
v___x_2667_ = 0;
v___x_2668_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2666_, v___x_2667_, v___x_2663_, v___f_2665_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object* v_waiter_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_2669_, v___y_2670_);
lean_dec(v___y_2670_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object* v_stream_2673_, lean_object* v_waiter_2674_){
_start:
{
lean_object* v___f_2676_; lean_object* v___x_2677_; 
v___f_2676_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2676_, 0, v_waiter_2674_);
v___x_2677_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2673_, v___f_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object* v_stream_2678_, lean_object* v_waiter_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_2678_, v_waiter_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object* v_stream_2683_){
_start:
{
lean_object* v___f_2684_; lean_object* v___f_2685_; lean_object* v___f_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___f_2684_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_2683_, 2);
v___f_2685_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2685_, 0, v_stream_2683_);
v___f_2686_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_2687_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2687_, 0, lean_box(0));
lean_closure_set(v___x_2687_, 1, lean_box(0));
lean_closure_set(v___x_2687_, 2, v_stream_2683_);
lean_closure_set(v___x_2687_, 3, v___f_2686_);
v___x_2688_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2688_, 0, lean_box(0));
lean_closure_set(v___x_2688_, 1, lean_box(0));
lean_closure_set(v___x_2688_, 2, v_stream_2683_);
lean_closure_set(v___x_2688_, 3, v___f_2684_);
v___x_2689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___f_2685_);
lean_ctor_set(v___x_2689_, 2, v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(lean_object* v_step_2690_, lean_object* v_acc_2691_, lean_object* v___f_2692_, lean_object* v_x_2693_){
_start:
{
if (lean_obj_tag(v_x_2693_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v___f_2692_);
lean_dec(v_acc_2691_);
lean_dec_ref(v_step_2690_);
v_a_2695_ = lean_ctor_get(v_x_2693_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_x_2693_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2697_ = v_x_2693_;
v_isShared_2698_ = v_isSharedCheck_2703_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v_x_2693_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2703_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2717_; 
v_a_2704_ = lean_ctor_get(v_x_2693_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_x_2693_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2706_ = v_x_2693_;
v_isShared_2707_ = v_isSharedCheck_2717_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v_x_2693_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2717_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
if (lean_obj_tag(v_a_2704_) == 1)
{
lean_object* v_val_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; 
lean_del_object(v___x_2706_);
v_val_2708_ = lean_ctor_get(v_a_2704_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v_a_2704_, 1);
v___x_2709_ = lean_apply_3(v_step_2690_, v_val_2708_, v_acc_2691_, lean_box(0));
v___x_2710_ = lean_unsigned_to_nat(0u);
v___x_2711_ = 0;
v___x_2712_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2710_, v___x_2711_, v___x_2709_, v___f_2692_);
return v___x_2712_;
}
else
{
lean_object* v___x_2714_; 
lean_dec(v_a_2704_);
lean_dec_ref(v___f_2692_);
lean_dec_ref(v_step_2690_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v_acc_2691_);
v___x_2714_ = v___x_2706_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_acc_2691_);
v___x_2714_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed(lean_object* v_step_2718_, lean_object* v_acc_2719_, lean_object* v___f_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(v_step_2718_, v_acc_2719_, v___f_2720_, v_x_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(lean_object* v_step_2724_, lean_object* v_stream_2725_, lean_object* v_x_2726_){
_start:
{
if (lean_obj_tag(v_x_2726_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v_stream_2725_);
lean_dec_ref(v_step_2724_);
v_a_2728_ = lean_ctor_get(v_x_2726_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_x_2726_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2730_ = v_x_2726_;
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v_x_2726_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
return v___x_2734_;
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2754_; 
v_a_2737_ = lean_ctor_get(v_x_2726_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_x_2726_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2739_ = v_x_2726_;
v_isShared_2740_ = v_isSharedCheck_2754_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v_x_2726_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2754_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
if (lean_obj_tag(v_a_2737_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v_stream_2725_);
lean_dec_ref(v_step_2724_);
v_a_2741_ = lean_ctor_get(v_a_2737_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_a_2737_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2743_ = v_a_2737_;
v_isShared_2744_ = v_isSharedCheck_2751_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v_a_2737_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2751_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v_a_2741_);
v___x_2746_ = v___x_2739_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2748_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2746_);
v___x_2748_ = v___x_2743_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2753_; 
lean_del_object(v___x_2739_);
v_a_2752_ = lean_ctor_get(v_a_2737_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v_a_2737_, 1);
v___x_2753_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2724_, v_stream_2725_, v_a_2752_);
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed(lean_object* v_step_2755_, lean_object* v_stream_2756_, lean_object* v_x_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(v_step_2755_, v_stream_2756_, v_x_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(lean_object* v_step_2760_, lean_object* v_stream_2761_, lean_object* v_acc_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v___f_2765_; lean_object* v___f_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; lean_object* v___x_2769_; 
lean_inc_ref(v_stream_2761_);
v___x_2764_ = l_Std_Http_Body_Stream_recv(v_stream_2761_);
lean_inc_ref(v_step_2760_);
v___f_2765_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2765_, 0, v_step_2760_);
lean_closure_set(v___f_2765_, 1, v_stream_2761_);
v___f_2766_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2766_, 0, v_step_2760_);
lean_closure_set(v___f_2766_, 1, v_acc_2762_);
lean_closure_set(v___f_2766_, 2, v___f_2765_);
v___x_2767_ = lean_unsigned_to_nat(0u);
v___x_2768_ = 0;
v___x_2769_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2767_, v___x_2768_, v___x_2764_, v___f_2766_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___boxed(lean_object* v_step_2770_, lean_object* v_stream_2771_, lean_object* v_acc_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2770_, v_stream_2771_, v_acc_2772_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(lean_object* v_00_u03b2_2775_, lean_object* v_step_2776_, lean_object* v_stream_2777_, lean_object* v_acc_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2776_, v_stream_2777_, v_acc_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___boxed(lean_object* v_00_u03b2_2781_, lean_object* v_step_2782_, lean_object* v_stream_2783_, lean_object* v_acc_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(v_00_u03b2_2781_, v_step_2782_, v_stream_2783_, v_acc_2784_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_2787_, lean_object* v_acc_2788_, lean_object* v_step_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2789_, v_stream_2787_, v_acc_2788_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_2792_, lean_object* v_acc_2793_, lean_object* v_step_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_2792_, v_acc_2793_, v_step_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_2797_, lean_object* v_stream_2798_, lean_object* v_acc_2799_, lean_object* v_step_2800_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2800_, v_stream_2798_, v_acc_2799_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_2803_, lean_object* v_stream_2804_, lean_object* v_acc_2805_, lean_object* v_step_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_2803_, v_stream_2804_, v_acc_2805_, v_step_2806_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(lean_object* v_x_2809_){
_start:
{
if (lean_obj_tag(v_x_2809_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2819_; 
v_a_2811_ = lean_ctor_get(v_x_2809_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_x_2809_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2813_ = v_x_2809_;
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v_x_2809_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2811_);
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
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2830_; 
v_a_2820_ = lean_ctor_get(v_x_2809_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_x_2809_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2822_ = v_x_2809_;
v_isShared_2823_ = v_isSharedCheck_2830_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v_x_2809_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2830_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v_token_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
v_token_2824_ = lean_ctor_get(v_a_2820_, 1);
lean_inc_ref(v_token_2824_);
lean_dec(v_a_2820_);
v___x_2825_ = l_Std_CancellationToken_selector(v_token_2824_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v___x_2825_);
v___x_2827_ = v___x_2822_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_x_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(v_x_2831_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___y_2834_);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed(lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(v___y_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(lean_object* v_x_2841_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed(lean_object* v_x_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(v_x_2844_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(lean_object* v_stream_2847_, lean_object* v___f_2848_, lean_object* v___f_2849_, lean_object* v___f_2850_, lean_object* v_x_2851_){
_start:
{
if (lean_obj_tag(v_x_2851_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2861_; 
lean_dec_ref(v___f_2850_);
lean_dec_ref(v___f_2849_);
lean_dec_ref(v___f_2848_);
lean_dec_ref(v_stream_2847_);
v_a_2853_ = lean_ctor_get(v_x_2851_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2855_ = v_x_2851_;
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v_x_2851_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; 
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
return v___x_2859_;
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; lean_object* v___x_2873_; 
v_a_2862_ = lean_ctor_get(v_x_2851_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v_x_2851_, 1);
v___x_2863_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2847_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v___f_2848_);
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v_a_2862_);
lean_ctor_set(v___x_2865_, 1, v___f_2849_);
v___x_2866_ = lean_unsigned_to_nat(2u);
v___x_2867_ = lean_mk_empty_array_with_capacity(v___x_2866_);
v___x_2868_ = lean_array_push(v___x_2867_, v___x_2864_);
v___x_2869_ = lean_array_push(v___x_2868_, v___x_2865_);
v___x_2870_ = l_Std_Async_Selectable_one___redArg(v___x_2869_);
v___x_2871_ = lean_unsigned_to_nat(0u);
v___x_2872_ = 0;
v___x_2873_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2871_, v___x_2872_, v___x_2870_, v___f_2850_);
return v___x_2873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed(lean_object* v_stream_2874_, lean_object* v___f_2875_, lean_object* v___f_2876_, lean_object* v___f_2877_, lean_object* v_x_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(v_stream_2874_, v___f_2875_, v___f_2876_, v___f_2877_, v_x_2878_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(lean_object* v_step_2881_, lean_object* v_acc_2882_, lean_object* v_a_2883_, lean_object* v___f_2884_, lean_object* v_x_2885_){
_start:
{
if (lean_obj_tag(v_x_2885_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v___f_2884_);
lean_dec(v_acc_2882_);
lean_dec_ref(v_step_2881_);
v_a_2887_ = lean_ctor_get(v_x_2885_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_x_2885_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2889_ = v_x_2885_;
v_isShared_2890_ = v_isSharedCheck_2895_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v_x_2885_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2895_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
return v___x_2893_;
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2909_; 
v_a_2896_ = lean_ctor_get(v_x_2885_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_x_2885_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2898_ = v_x_2885_;
v_isShared_2899_ = v_isSharedCheck_2909_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v_x_2885_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2909_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
if (lean_obj_tag(v_a_2896_) == 1)
{
lean_object* v_val_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; lean_object* v___x_2904_; 
lean_del_object(v___x_2898_);
v_val_2900_ = lean_ctor_get(v_a_2896_, 0);
lean_inc(v_val_2900_);
lean_dec_ref_known(v_a_2896_, 1);
lean_inc_ref(v_a_2883_);
v___x_2901_ = lean_apply_4(v_step_2881_, v_val_2900_, v_acc_2882_, v_a_2883_, lean_box(0));
v___x_2902_ = lean_unsigned_to_nat(0u);
v___x_2903_ = 0;
v___x_2904_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2902_, v___x_2903_, v___x_2901_, v___f_2884_);
return v___x_2904_;
}
else
{
lean_object* v___x_2906_; 
lean_dec(v_a_2896_);
lean_dec_ref(v___f_2884_);
lean_dec_ref(v_step_2881_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v_acc_2882_);
v___x_2906_ = v___x_2898_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_acc_2882_);
v___x_2906_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed(lean_object* v_step_2910_, lean_object* v_acc_2911_, lean_object* v_a_2912_, lean_object* v___f_2913_, lean_object* v_x_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(v_step_2910_, v_acc_2911_, v_a_2912_, v___f_2913_, v_x_2914_);
lean_dec_ref(v_a_2912_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed(lean_object* v_step_2920_, lean_object* v_stream_2921_, lean_object* v_a_2922_, lean_object* v_x_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(v_step_2920_, v_stream_2921_, v_a_2922_, v_x_2923_);
lean_dec_ref(v_a_2922_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(lean_object* v_step_2926_, lean_object* v_stream_2927_, lean_object* v_acc_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v___f_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; lean_object* v___x_2936_; lean_object* v___f_2937_; lean_object* v___f_2938_; lean_object* v___f_2939_; lean_object* v___f_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; 
v___f_2931_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0));
lean_inc_ref_n(v_a_2929_, 3);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_a_2929_);
v___x_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
v___x_2934_ = lean_unsigned_to_nat(0u);
v___x_2935_ = 0;
v___x_2936_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2934_, v___x_2935_, v___x_2933_, v___f_2931_);
v___f_2937_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1));
v___f_2938_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2));
lean_inc_ref(v_stream_2927_);
lean_inc_ref(v_step_2926_);
v___f_2939_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2939_, 0, v_step_2926_);
lean_closure_set(v___f_2939_, 1, v_stream_2927_);
lean_closure_set(v___f_2939_, 2, v_a_2929_);
v___f_2940_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_2940_, 0, v_step_2926_);
lean_closure_set(v___f_2940_, 1, v_acc_2928_);
lean_closure_set(v___f_2940_, 2, v_a_2929_);
lean_closure_set(v___f_2940_, 3, v___f_2939_);
v___f_2941_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_2941_, 0, v_stream_2927_);
lean_closure_set(v___f_2941_, 1, v___f_2937_);
lean_closure_set(v___f_2941_, 2, v___f_2938_);
lean_closure_set(v___f_2941_, 3, v___f_2940_);
v___x_2942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2934_, v___x_2935_, v___x_2936_, v___f_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(lean_object* v_step_2943_, lean_object* v_stream_2944_, lean_object* v_a_2945_, lean_object* v_x_2946_){
_start:
{
if (lean_obj_tag(v_x_2946_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_stream_2944_);
lean_dec_ref(v_step_2943_);
v_a_2948_ = lean_ctor_get(v_x_2946_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_x_2946_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2950_ = v_x_2946_;
v_isShared_2951_ = v_isSharedCheck_2956_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v_x_2946_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2956_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2974_; 
v_a_2957_ = lean_ctor_get(v_x_2946_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_x_2946_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2959_ = v_x_2946_;
v_isShared_2960_ = v_isSharedCheck_2974_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v_x_2946_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2974_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
if (lean_obj_tag(v_a_2957_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2971_; 
lean_dec_ref(v_stream_2944_);
lean_dec_ref(v_step_2943_);
v_a_2961_ = lean_ctor_get(v_a_2957_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2963_ = v_a_2957_;
v_isShared_2964_ = v_isSharedCheck_2971_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v_a_2957_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2971_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v_a_2961_);
v___x_2966_ = v___x_2959_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2968_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2966_);
v___x_2968_ = v___x_2963_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2973_; 
lean_del_object(v___x_2959_);
v_a_2972_ = lean_ctor_get(v_a_2957_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v_a_2957_, 1);
v___x_2973_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2943_, v_stream_2944_, v_a_2972_, v_a_2945_);
return v___x_2973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___boxed(lean_object* v_step_2975_, lean_object* v_stream_2976_, lean_object* v_acc_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2975_, v_stream_2976_, v_acc_2977_, v_a_2978_);
lean_dec_ref(v_a_2978_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(lean_object* v_00_u03b2_2981_, lean_object* v_step_2982_, lean_object* v_stream_2983_, lean_object* v_acc_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2982_, v_stream_2983_, v_acc_2984_, v_a_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___boxed(lean_object* v_00_u03b2_2988_, lean_object* v_step_2989_, lean_object* v_stream_2990_, lean_object* v_acc_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(v_00_u03b2_2988_, v_step_2989_, v_stream_2990_, v_acc_2991_, v_a_2992_);
lean_dec_ref(v_a_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_2995_, lean_object* v_acc_2996_, lean_object* v_step_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2997_, v_stream_2995_, v_acc_2996_, v_a_2998_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_3001_, lean_object* v_acc_3002_, lean_object* v_step_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_3001_, v_acc_3002_, v_step_3003_, v_a_3004_);
lean_dec_ref(v_a_3004_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_3007_, lean_object* v_stream_3008_, lean_object* v_acc_3009_, lean_object* v_step_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_3010_, v_stream_3008_, v_acc_3009_, v_a_3011_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_3014_, lean_object* v_stream_3015_, lean_object* v_acc_3016_, lean_object* v_step_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_3014_, v_stream_3015_, v_acc_3016_, v_step_3017_, v_a_3018_);
lean_dec_ref(v_a_3018_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v_x_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v_x_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v_x_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___y_3029_);
v___x_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed(lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(v___y_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(lean_object* v_x_3036_){
_start:
{
if (lean_obj_tag(v_x_3036_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3046_; 
v_a_3038_ = lean_ctor_get(v_x_3036_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_x_3036_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3040_ = v_x_3036_;
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v_x_3036_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3038_);
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
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3057_; 
v_a_3047_ = lean_ctor_get(v_x_3036_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_x_3036_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3049_ = v_x_3036_;
v_isShared_3050_ = v_isSharedCheck_3057_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v_x_3036_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3057_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_token_3051_; lean_object* v___x_3052_; lean_object* v___x_3054_; 
v_token_3051_ = lean_ctor_get(v_a_3047_, 1);
lean_inc_ref(v_token_3051_);
lean_dec(v_a_3047_);
v___x_3052_ = l_Std_CancellationToken_selector(v_token_3051_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3052_);
v___x_3054_ = v___x_3049_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed(lean_object* v_x_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(v_x_3058_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v_stream_3061_, lean_object* v___f_3062_, lean_object* v___f_3063_, lean_object* v_x_3064_){
_start:
{
if (lean_obj_tag(v_x_3064_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v___f_3063_);
lean_dec_ref(v___f_3062_);
lean_dec_ref(v_stream_3061_);
v_a_3066_ = lean_ctor_get(v_x_3064_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_x_3064_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3068_ = v_x_3064_;
v_isShared_3069_ = v_isSharedCheck_3074_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v_x_3064_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3074_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
return v___x_3072_;
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_a_3075_ = lean_ctor_get(v_x_3064_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v_x_3064_, 1);
v___x_3076_ = l_Std_Http_Body_Stream_recvSelector(v_stream_3061_);
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3076_);
lean_ctor_set(v___x_3077_, 1, v___f_3062_);
v___x_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3078_, 0, v_a_3075_);
lean_ctor_set(v___x_3078_, 1, v___f_3063_);
v___x_3079_ = lean_unsigned_to_nat(2u);
v___x_3080_ = lean_mk_empty_array_with_capacity(v___x_3079_);
v___x_3081_ = lean_array_push(v___x_3080_, v___x_3077_);
v___x_3082_ = lean_array_push(v___x_3081_, v___x_3078_);
v___x_3083_ = l_Std_Async_Selectable_one___redArg(v___x_3082_);
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v_stream_3084_, lean_object* v___f_3085_, lean_object* v___f_3086_, lean_object* v_x_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_3084_, v___f_3085_, v___f_3086_, v_x_3087_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(lean_object* v___f_3090_, lean_object* v___f_3091_, lean_object* v___f_3092_, lean_object* v_stream_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; lean_object* v___x_3100_; lean_object* v___f_3101_; lean_object* v___x_3102_; 
lean_inc_ref(v___y_3094_);
v___x_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___y_3094_);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = 0;
v___x_3100_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3098_, v___x_3099_, v___x_3097_, v___f_3090_);
v___f_3101_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3101_, 0, v_stream_3093_);
lean_closure_set(v___f_3101_, 1, v___f_3091_);
lean_closure_set(v___f_3101_, 2, v___f_3092_);
v___x_3102_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3098_, v___x_3099_, v___x_3100_, v___f_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4___boxed(lean_object* v___f_3103_, lean_object* v___f_3104_, lean_object* v___f_3105_, lean_object* v_stream_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(v___f_3103_, v___f_3104_, v___f_3105_, v_stream_3106_, v___y_3107_);
lean_dec_ref(v___y_3107_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v_toPure_3120_, lean_object* v_result_3121_, lean_object* v_maximumSize_3122_, lean_object* v_inst_3123_, lean_object* v_inst_3124_, lean_object* v_inst_3125_, lean_object* v_stream_3126_, lean_object* v_toBind_3127_, lean_object* v_____do__lift_3128_){
_start:
{
if (lean_obj_tag(v_____do__lift_3128_) == 0)
{
lean_object* v___x_3129_; 
lean_dec(v_toBind_3127_);
lean_dec_ref(v_stream_3126_);
lean_dec(v_inst_3125_);
lean_dec_ref(v_inst_3124_);
lean_dec_ref(v_inst_3123_);
lean_dec(v_maximumSize_3122_);
v___x_3129_ = lean_apply_2(v_toPure_3120_, lean_box(0), v_result_3121_);
return v___x_3129_;
}
else
{
lean_object* v_val_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_toPure_3120_);
v_val_3130_ = lean_ctor_get(v_____do__lift_3128_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_____do__lift_3128_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3132_ = v_____do__lift_3128_;
v_isShared_3133_ = v_isSharedCheck_3161_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_val_3130_);
lean_dec(v_____do__lift_3128_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3161_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v_data_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; lean_object* v_result_3139_; 
v_data_3134_ = lean_ctor_get(v_val_3130_, 0);
lean_inc_ref(v_data_3134_);
lean_dec(v_val_3130_);
v___x_3135_ = lean_unsigned_to_nat(0u);
v___x_3136_ = lean_byte_array_size(v_result_3121_);
v___x_3137_ = lean_byte_array_size(v_data_3134_);
v___x_3138_ = 0;
v_result_3139_ = lean_byte_array_copy_slice(v_data_3134_, v___x_3135_, v_result_3121_, v___x_3136_, v___x_3137_, v___x_3138_);
lean_dec_ref(v_data_3134_);
if (lean_obj_tag(v_maximumSize_3122_) == 1)
{
lean_object* v_val_3140_; lean_object* v___x_3141_; uint64_t v___x_3142_; uint64_t v___x_3143_; uint8_t v___x_3144_; 
v_val_3140_ = lean_ctor_get(v_maximumSize_3122_, 0);
v___x_3141_ = lean_byte_array_size(v_result_3139_);
v___x_3142_ = lean_uint64_of_nat(v___x_3141_);
v___x_3143_ = lean_unbox_uint64(v_val_3140_);
v___x_3144_ = lean_uint64_dec_lt(v___x_3143_, v___x_3142_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; 
lean_del_object(v___x_3132_);
lean_dec(v_toBind_3127_);
v___x_3145_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3123_, v_inst_3124_, v_inst_3125_, v_stream_3126_, v_maximumSize_3122_, v_result_3139_);
return v___x_3145_;
}
else
{
lean_object* v_throw_3146_; lean_object* v___f_3147_; lean_object* v___x_3148_; uint64_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
lean_inc(v_val_3140_);
v_throw_3146_ = lean_ctor_get(v_inst_3124_, 0);
lean_inc(v_throw_3146_);
v___f_3147_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0), 7, 6);
lean_closure_set(v___f_3147_, 0, v_inst_3123_);
lean_closure_set(v___f_3147_, 1, v_inst_3124_);
lean_closure_set(v___f_3147_, 2, v_inst_3125_);
lean_closure_set(v___f_3147_, 3, v_stream_3126_);
lean_closure_set(v___f_3147_, 4, v_maximumSize_3122_);
lean_closure_set(v___f_3147_, 5, v_result_3139_);
v___x_3148_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0));
v___x_3149_ = lean_unbox_uint64(v_val_3140_);
lean_dec(v_val_3140_);
v___x_3150_ = lean_uint64_to_nat(v___x_3149_);
v___x_3151_ = l_Nat_reprFast(v___x_3150_);
v___x_3152_ = lean_string_append(v___x_3148_, v___x_3151_);
lean_dec_ref(v___x_3151_);
v___x_3153_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1));
v___x_3154_ = lean_string_append(v___x_3152_, v___x_3153_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set_tag(v___x_3132_, 18);
lean_ctor_set(v___x_3132_, 0, v___x_3154_);
v___x_3156_ = v___x_3132_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3154_);
v___x_3156_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_apply_2(v_throw_3146_, lean_box(0), v___x_3156_);
v___x_3158_ = lean_apply_4(v_toBind_3127_, lean_box(0), lean_box(0), v___x_3157_, v___f_3147_);
return v___x_3158_;
}
}
}
else
{
lean_object* v___x_3160_; 
lean_del_object(v___x_3132_);
lean_dec(v_toBind_3127_);
v___x_3160_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3123_, v_inst_3124_, v_inst_3125_, v_stream_3126_, v_maximumSize_3122_, v_result_3139_);
return v___x_3160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_stream_3165_, lean_object* v_maximumSize_3166_, lean_object* v_result_3167_){
_start:
{
lean_object* v_toApplicative_3168_; lean_object* v_toBind_3169_; lean_object* v_toPure_3170_; lean_object* v___x_3171_; lean_object* v___f_3172_; lean_object* v___x_3173_; 
v_toApplicative_3168_ = lean_ctor_get(v_inst_3162_, 0);
v_toBind_3169_ = lean_ctor_get(v_inst_3162_, 1);
lean_inc_n(v_toBind_3169_, 2);
v_toPure_3170_ = lean_ctor_get(v_toApplicative_3168_, 1);
lean_inc(v_toPure_3170_);
lean_inc(v_inst_3164_);
lean_inc_ref(v_stream_3165_);
v___x_3171_ = lean_apply_1(v_inst_3164_, v_stream_3165_);
v___f_3172_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 9, 8);
lean_closure_set(v___f_3172_, 0, v_toPure_3170_);
lean_closure_set(v___f_3172_, 1, v_result_3167_);
lean_closure_set(v___f_3172_, 2, v_maximumSize_3166_);
lean_closure_set(v___f_3172_, 3, v_inst_3162_);
lean_closure_set(v___f_3172_, 4, v_inst_3163_);
lean_closure_set(v___f_3172_, 5, v_inst_3164_);
lean_closure_set(v___f_3172_, 6, v_stream_3165_);
lean_closure_set(v___f_3172_, 7, v_toBind_3169_);
v___x_3173_ = lean_apply_4(v_toBind_3169_, lean_box(0), lean_box(0), v___x_3171_, v___f_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_stream_3177_, lean_object* v_maximumSize_3178_, lean_object* v_result_3179_, lean_object* v_____r_3180_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3174_, v_inst_3175_, v_inst_3176_, v_stream_3177_, v_maximumSize_3178_, v_result_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_stream_3186_, lean_object* v_maximumSize_3187_, lean_object* v_result_3188_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3183_, v_inst_3184_, v_inst_3185_, v_stream_3186_, v_maximumSize_3187_, v_result_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_toPure_3192_, lean_object* v_result_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = lean_apply_1(v_inst_3190_, v_result_3193_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_toPure_3192_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3204_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3204_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_throw_3199_; lean_object* v___x_3201_; 
v_throw_3199_ = lean_ctor_get(v_inst_3191_, 0);
lean_inc(v_throw_3199_);
lean_dec_ref(v_inst_3191_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 18);
v___x_3201_ = v___x_3197_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3195_);
v___x_3201_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_apply_2(v_throw_3199_, lean_box(0), v___x_3201_);
return v___x_3202_;
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3206_; 
lean_dec_ref(v_inst_3191_);
v_a_3205_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3206_ = lean_apply_2(v_toPure_3192_, lean_box(0), v_a_3205_);
return v___x_3206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_stream_3211_, lean_object* v_maximumSize_3212_){
_start:
{
lean_object* v_toApplicative_3213_; lean_object* v_toBind_3214_; lean_object* v_toPure_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; 
v_toApplicative_3213_ = lean_ctor_get(v_inst_3208_, 0);
v_toBind_3214_ = lean_ctor_get(v_inst_3208_, 1);
lean_inc(v_toBind_3214_);
v_toPure_3215_ = lean_ctor_get(v_toApplicative_3213_, 1);
lean_inc(v_toPure_3215_);
v___x_3216_ = l_ByteArray_empty;
lean_inc_ref(v_inst_3209_);
v___x_3217_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3208_, v_inst_3209_, v_inst_3210_, v_stream_3211_, v_maximumSize_3212_, v___x_3216_);
v___f_3218_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3218_, 0, v_inst_3207_);
lean_closure_set(v___f_3218_, 1, v_inst_3209_);
lean_closure_set(v___f_3218_, 2, v_toPure_3215_);
v___x_3219_ = lean_apply_4(v_toBind_3214_, lean_box(0), lean_box(0), v___x_3217_, v___f_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_3220_, lean_object* v_m_3221_, lean_object* v_inst_3222_, lean_object* v_inst_3223_, lean_object* v_inst_3224_, lean_object* v_inst_3225_, lean_object* v_stream_3226_, lean_object* v_maximumSize_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_3222_, v_inst_3223_, v_inst_3224_, v_inst_3225_, v_stream_3226_, v_maximumSize_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0(lean_object* v_toPure_3229_, lean_object* v_____r_3230_){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_box(0);
v___x_3232_ = lean_apply_2(v_toPure_3229_, lean_box(0), v___x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(lean_object* v_toPure_3233_, uint64_t v_consumed_3234_, lean_object* v_drainLimit_3235_, lean_object* v_inst_3236_, lean_object* v_inst_3237_, lean_object* v_stream_3238_, lean_object* v_closeStream_3239_, lean_object* v_toBind_3240_, lean_object* v___f_3241_, lean_object* v_____do__lift_3242_){
_start:
{
if (lean_obj_tag(v_____do__lift_3242_) == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_dec(v___f_3241_);
lean_dec(v_toBind_3240_);
lean_dec(v_closeStream_3239_);
lean_dec_ref(v_stream_3238_);
lean_dec(v_inst_3237_);
lean_dec_ref(v_inst_3236_);
lean_dec(v_drainLimit_3235_);
v___x_3243_ = lean_box(0);
v___x_3244_ = lean_apply_2(v_toPure_3233_, lean_box(0), v___x_3243_);
return v___x_3244_;
}
else
{
lean_object* v_val_3245_; lean_object* v_data_3246_; lean_object* v___x_3247_; uint64_t v___x_3248_; uint64_t v_consumed_3249_; 
lean_dec(v_toPure_3233_);
v_val_3245_ = lean_ctor_get(v_____do__lift_3242_, 0);
v_data_3246_ = lean_ctor_get(v_val_3245_, 0);
v___x_3247_ = lean_byte_array_size(v_data_3246_);
v___x_3248_ = lean_uint64_of_nat(v___x_3247_);
v_consumed_3249_ = lean_uint64_add(v_consumed_3234_, v___x_3248_);
if (lean_obj_tag(v_drainLimit_3235_) == 1)
{
lean_object* v_val_3250_; uint64_t v___x_3251_; uint8_t v___x_3252_; 
v_val_3250_ = lean_ctor_get(v_drainLimit_3235_, 0);
v___x_3251_ = lean_unbox_uint64(v_val_3250_);
v___x_3252_ = lean_uint64_dec_lt(v___x_3251_, v_consumed_3249_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; 
lean_dec(v___f_3241_);
lean_dec(v_toBind_3240_);
v___x_3253_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3236_, v_inst_3237_, v_stream_3238_, v_drainLimit_3235_, v_closeStream_3239_, v_consumed_3249_);
return v___x_3253_;
}
else
{
lean_object* v___x_3254_; 
lean_dec_ref_known(v_drainLimit_3235_, 1);
lean_dec_ref(v_stream_3238_);
lean_dec(v_inst_3237_);
lean_dec_ref(v_inst_3236_);
v___x_3254_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v_closeStream_3239_, v___f_3241_);
return v___x_3254_;
}
}
else
{
lean_object* v___x_3255_; 
lean_dec(v___f_3241_);
lean_dec(v_toBind_3240_);
v___x_3255_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3236_, v_inst_3237_, v_stream_3238_, v_drainLimit_3235_, v_closeStream_3239_, v_consumed_3249_);
return v___x_3255_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed(lean_object* v_toPure_3256_, lean_object* v_consumed_3257_, lean_object* v_drainLimit_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_stream_3261_, lean_object* v_closeStream_3262_, lean_object* v_toBind_3263_, lean_object* v___f_3264_, lean_object* v_____do__lift_3265_){
_start:
{
uint64_t v_consumed_boxed_3266_; lean_object* v_res_3267_; 
v_consumed_boxed_3266_ = lean_unbox_uint64(v_consumed_3257_);
lean_dec_ref(v_consumed_3257_);
v_res_3267_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(v_toPure_3256_, v_consumed_boxed_3266_, v_drainLimit_3258_, v_inst_3259_, v_inst_3260_, v_stream_3261_, v_closeStream_3262_, v_toBind_3263_, v___f_3264_, v_____do__lift_3265_);
lean_dec(v_____do__lift_3265_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_stream_3270_, lean_object* v_drainLimit_3271_, lean_object* v_closeStream_3272_, uint64_t v_consumed_3273_){
_start:
{
lean_object* v_toApplicative_3274_; lean_object* v_toBind_3275_; lean_object* v_toPure_3276_; lean_object* v___x_3277_; lean_object* v___f_3278_; lean_object* v___x_3279_; lean_object* v___f_3280_; lean_object* v___x_3281_; 
v_toApplicative_3274_ = lean_ctor_get(v_inst_3268_, 0);
v_toBind_3275_ = lean_ctor_get(v_inst_3268_, 1);
lean_inc_n(v_toBind_3275_, 2);
v_toPure_3276_ = lean_ctor_get(v_toApplicative_3274_, 1);
lean_inc_n(v_toPure_3276_, 2);
lean_inc(v_inst_3269_);
lean_inc_ref(v_stream_3270_);
v___x_3277_ = lean_apply_1(v_inst_3269_, v_stream_3270_);
v___f_3278_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3278_, 0, v_toPure_3276_);
v___x_3279_ = lean_box_uint64(v_consumed_3273_);
v___f_3280_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3280_, 0, v_toPure_3276_);
lean_closure_set(v___f_3280_, 1, v___x_3279_);
lean_closure_set(v___f_3280_, 2, v_drainLimit_3271_);
lean_closure_set(v___f_3280_, 3, v_inst_3268_);
lean_closure_set(v___f_3280_, 4, v_inst_3269_);
lean_closure_set(v___f_3280_, 5, v_stream_3270_);
lean_closure_set(v___f_3280_, 6, v_closeStream_3272_);
lean_closure_set(v___f_3280_, 7, v_toBind_3275_);
lean_closure_set(v___f_3280_, 8, v___f_3278_);
v___x_3281_ = lean_apply_4(v_toBind_3275_, lean_box(0), lean_box(0), v___x_3277_, v___f_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___boxed(lean_object* v_inst_3282_, lean_object* v_inst_3283_, lean_object* v_stream_3284_, lean_object* v_drainLimit_3285_, lean_object* v_closeStream_3286_, lean_object* v_consumed_3287_){
_start:
{
uint64_t v_consumed_boxed_3288_; lean_object* v_res_3289_; 
v_consumed_boxed_3288_ = lean_unbox_uint64(v_consumed_3287_);
lean_dec_ref(v_consumed_3287_);
v_res_3289_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3282_, v_inst_3283_, v_stream_3284_, v_drainLimit_3285_, v_closeStream_3286_, v_consumed_boxed_3288_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_object* v_m_3290_, lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_stream_3293_, lean_object* v_drainLimit_3294_, lean_object* v_closeStream_3295_, uint64_t v_consumed_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3291_, v_inst_3292_, v_stream_3293_, v_drainLimit_3294_, v_closeStream_3295_, v_consumed_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___boxed(lean_object* v_m_3298_, lean_object* v_inst_3299_, lean_object* v_inst_3300_, lean_object* v_stream_3301_, lean_object* v_drainLimit_3302_, lean_object* v_closeStream_3303_, lean_object* v_consumed_3304_){
_start:
{
uint64_t v_consumed_boxed_3305_; lean_object* v_res_3306_; 
v_consumed_boxed_3305_ = lean_unbox_uint64(v_consumed_3304_);
lean_dec_ref(v_consumed_3304_);
v_res_3306_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(v_m_3298_, v_inst_3299_, v_inst_3300_, v_stream_3301_, v_drainLimit_3302_, v_closeStream_3303_, v_consumed_boxed_3305_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain___redArg(lean_object* v_inst_3307_, lean_object* v_inst_3308_, lean_object* v_stream_3309_, lean_object* v_drainLimit_3310_, lean_object* v_closeStream_3311_){
_start:
{
uint64_t v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = 0ULL;
v___x_3313_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3307_, v_inst_3308_, v_stream_3309_, v_drainLimit_3310_, v_closeStream_3311_, v___x_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain(lean_object* v_m_3314_, lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_stream_3317_, lean_object* v_drainLimit_3318_, lean_object* v_closeStream_3319_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Std_Http_Body_Stream_drain___redArg(v_inst_3315_, v_inst_3316_, v_stream_3317_, v_drainLimit_3318_, v_closeStream_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t v_incomplete_3326_, lean_object* v_chunk_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v_pendingProducer_3332_; lean_object* v_pendingConsumer_3333_; lean_object* v_interestWaiter_3334_; uint8_t v_closed_3335_; lean_object* v_knownSize_3336_; lean_object* v_pendingIncompleteChunk_3337_; lean_object* v_closeError_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3379_; 
v___x_3330_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_3328_);
v___x_3331_ = lean_st_ref_get(v___y_3328_);
v_pendingProducer_3332_ = lean_ctor_get(v___x_3331_, 0);
v_pendingConsumer_3333_ = lean_ctor_get(v___x_3331_, 1);
v_interestWaiter_3334_ = lean_ctor_get(v___x_3331_, 2);
v_closed_3335_ = lean_ctor_get_uint8(v___x_3331_, sizeof(void*)*6);
v_knownSize_3336_ = lean_ctor_get(v___x_3331_, 3);
v_pendingIncompleteChunk_3337_ = lean_ctor_get(v___x_3331_, 4);
v_closeError_3338_ = lean_ctor_get(v___x_3331_, 5);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3340_ = v___x_3331_;
v_isShared_3341_ = v_isSharedCheck_3379_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_closeError_3338_);
lean_inc(v_pendingIncompleteChunk_3337_);
lean_inc(v_knownSize_3336_);
lean_inc(v_interestWaiter_3334_);
lean_inc(v_pendingConsumer_3333_);
lean_inc(v_pendingProducer_3332_);
lean_dec(v___x_3331_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3379_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___y_3343_; 
if (v_closed_3335_ == 0)
{
if (lean_obj_tag(v_pendingIncompleteChunk_3337_) == 0)
{
v___y_3343_ = v_chunk_3327_;
goto v___jp_3342_;
}
else
{
lean_object* v_val_3357_; lean_object* v_data_3358_; lean_object* v_extensions_3359_; lean_object* v_data_3360_; lean_object* v_extensions_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3377_; 
v_val_3357_ = lean_ctor_get(v_pendingIncompleteChunk_3337_, 0);
lean_inc(v_val_3357_);
lean_dec_ref_known(v_pendingIncompleteChunk_3337_, 1);
v_data_3358_ = lean_ctor_get(v_val_3357_, 0);
lean_inc_ref(v_data_3358_);
v_extensions_3359_ = lean_ctor_get(v_val_3357_, 1);
lean_inc_ref(v_extensions_3359_);
lean_dec(v_val_3357_);
v_data_3360_ = lean_ctor_get(v_chunk_3327_, 0);
v_extensions_3361_ = lean_ctor_get(v_chunk_3327_, 1);
v_isSharedCheck_3377_ = !lean_is_exclusive(v_chunk_3327_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3363_ = v_chunk_3327_;
v_isShared_3364_ = v_isSharedCheck_3377_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_extensions_3361_);
lean_inc(v_data_3360_);
lean_dec(v_chunk_3327_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3377_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3365_ = lean_unsigned_to_nat(0u);
v___x_3366_ = lean_byte_array_size(v_data_3358_);
v___x_3367_ = lean_byte_array_size(v_data_3360_);
v___x_3368_ = lean_byte_array_copy_slice(v_data_3360_, v___x_3365_, v_data_3358_, v___x_3366_, v___x_3367_, v_closed_3335_);
lean_dec_ref(v_data_3360_);
v___x_3369_ = lean_array_get_size(v_extensions_3359_);
v___x_3370_ = lean_nat_dec_eq(v___x_3369_, v___x_3365_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3372_; 
lean_dec_ref(v_extensions_3361_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 1, v_extensions_3359_);
lean_ctor_set(v___x_3363_, 0, v___x_3368_);
v___x_3372_ = v___x_3363_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_extensions_3359_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
v___y_3343_ = v___x_3372_;
goto v___jp_3342_;
}
}
else
{
lean_object* v___x_3375_; 
lean_dec_ref(v_extensions_3359_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3368_);
v___x_3375_ = v___x_3363_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_extensions_3361_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
v___y_3343_ = v___x_3375_;
goto v___jp_3342_;
}
}
}
}
}
else
{
lean_object* v___x_3378_; 
lean_del_object(v___x_3340_);
lean_dec(v_closeError_3338_);
lean_dec(v_pendingIncompleteChunk_3337_);
lean_dec(v_knownSize_3336_);
lean_dec(v_interestWaiter_3334_);
lean_dec(v_pendingConsumer_3333_);
lean_dec(v_pendingProducer_3332_);
lean_dec_ref(v_chunk_3327_);
v___x_3378_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_3378_;
}
v___jp_3342_:
{
if (v_incomplete_3326_ == 0)
{
lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3344_ = lean_box(0);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 4, v___x_3344_);
v___x_3346_ = v___x_3340_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_pendingProducer_3332_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_pendingConsumer_3333_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_interestWaiter_3334_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_knownSize_3336_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3350_, 5, v_closeError_3338_);
lean_ctor_set_uint8(v_reuseFailAlloc_3350_, sizeof(void*)*6, v_closed_3335_);
v___x_3346_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = lean_st_ref_set(v___y_3328_, v___x_3346_);
v___x_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___y_3343_);
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
return v___x_3349_;
}
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___y_3343_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 4, v___x_3351_);
v___x_3353_ = v___x_3340_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_pendingProducer_3332_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_pendingConsumer_3333_);
lean_ctor_set(v_reuseFailAlloc_3356_, 2, v_interestWaiter_3334_);
lean_ctor_set(v_reuseFailAlloc_3356_, 3, v_knownSize_3336_);
lean_ctor_set(v_reuseFailAlloc_3356_, 4, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3356_, 5, v_closeError_3338_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, sizeof(void*)*6, v_closed_3335_);
v___x_3353_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = lean_st_ref_set(v___y_3328_, v___x_3353_);
v___x_3355_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
return v___x_3355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_incomplete_3380_, lean_object* v_chunk_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
uint8_t v_incomplete_boxed_3384_; lean_object* v_res_3385_; 
v_incomplete_boxed_3384_ = lean_unbox(v_incomplete_3380_);
v_res_3385_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_incomplete_boxed_3384_, v_chunk_3381_, v___y_3382_);
lean_dec(v___y_3382_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_3386_, lean_object* v_chunk_3387_, uint8_t v_incomplete_3388_){
_start:
{
lean_object* v___x_3390_; lean_object* v___f_3391_; lean_object* v___x_3392_; 
v___x_3390_ = lean_box(v_incomplete_3388_);
v___f_3391_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3391_, 0, v___x_3390_);
lean_closure_set(v___f_3391_, 1, v_chunk_3387_);
v___x_3392_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_3386_, v___f_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_3393_, lean_object* v_chunk_3394_, lean_object* v_incomplete_3395_, lean_object* v_a_3396_){
_start:
{
uint8_t v_incomplete_boxed_3397_; lean_object* v_res_3398_; 
v_incomplete_boxed_3397_ = lean_unbox(v_incomplete_3395_);
v_res_3398_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3393_, v_chunk_3394_, v_incomplete_boxed_3397_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_3405_){
_start:
{
if (lean_obj_tag(v_x_3405_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3415_; 
v_a_3407_ = lean_ctor_get(v_x_3405_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_x_3405_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3409_ = v_x_3405_;
v_isShared_3410_ = v_isSharedCheck_3415_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v_x_3405_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3415_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
return v___x_3413_;
}
}
}
else
{
lean_object* v___x_3416_; 
lean_dec_ref_known(v_x_3405_, 1);
v___x_3416_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_3416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_3417_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___3420_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___3423_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_3430_, lean_object* v_x_3431_){
_start:
{
if (lean_obj_tag(v_x_3431_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v___f_3430_);
v_a_3435_ = lean_ctor_get(v_x_3431_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_x_3431_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3437_ = v_x_3431_;
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v_x_3431_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; 
v___x_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
}
}
else
{
lean_object* v_a_3444_; 
v_a_3444_ = lean_ctor_get(v_x_3431_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v_x_3431_, 1);
if (lean_obj_tag(v_a_3444_) == 1)
{
lean_object* v_val_3445_; uint8_t v___x_3446_; 
v_val_3445_ = lean_ctor_get(v_a_3444_, 0);
lean_inc(v_val_3445_);
lean_dec_ref_known(v_a_3444_, 1);
v___x_3446_ = lean_unbox(v_val_3445_);
lean_dec(v_val_3445_);
if (v___x_3446_ == 1)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_apply_2(v___f_3430_, v___x_3447_, lean_box(0));
return v___x_3448_;
}
else
{
lean_dec_ref(v___f_3430_);
goto v___jp_3433_;
}
}
else
{
lean_dec(v_a_3444_);
lean_dec_ref(v___f_3430_);
goto v___jp_3433_;
}
}
v___jp_3433_:
{
lean_object* v___x_3434_; 
v___x_3434_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_3434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_3449_, lean_object* v_x_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_3449_, v_x_3450_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_3453_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3454_, 0, v_a_3453_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_3455_, lean_object* v_x_3456_){
_start:
{
if (lean_obj_tag(v_x_3456_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3466_; 
v_a_3458_ = lean_ctor_get(v_x_3456_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_x_3456_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3460_ = v_x_3456_;
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v_x_3456_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
return v___x_3464_;
}
}
}
else
{
lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3477_; 
v_isSharedCheck_3477_ = !lean_is_exclusive(v_x_3456_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v_x_3456_, 0);
lean_dec(v_unused_3478_);
v___x_3468_ = v_x_3456_;
v_isShared_3469_ = v_isSharedCheck_3477_;
goto v_resetjp_3467_;
}
else
{
lean_dec(v_x_3456_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3477_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3470_ = lean_box(v___x_3455_);
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3471_);
v___x_3473_ = v___x_3468_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
v___x_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
return v___x_3475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_3479_, lean_object* v_x_3480_, lean_object* v___y_3481_){
_start:
{
uint8_t v___x_5743__boxed_3482_; lean_object* v_res_3483_; 
v___x_5743__boxed_3482_ = lean_unbox(v___x_3479_);
v_res_3483_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5743__boxed_3482_, v_x_3480_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_3484_, lean_object* v_x_3485_){
_start:
{
if (lean_obj_tag(v_x_3485_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3495_; 
v_a_3487_ = lean_ctor_get(v_x_3485_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_x_3485_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3489_ = v_x_3485_;
v_isShared_3490_ = v_isSharedCheck_3495_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v_x_3485_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3495_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
return v___x_3493_;
}
}
}
else
{
lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3506_; 
v_isSharedCheck_3506_ = !lean_is_exclusive(v_x_3485_);
if (v_isSharedCheck_3506_ == 0)
{
lean_object* v_unused_3507_; 
v_unused_3507_ = lean_ctor_get(v_x_3485_, 0);
lean_dec(v_unused_3507_);
v___x_3497_ = v_x_3485_;
v_isShared_3498_ = v_isSharedCheck_3506_;
goto v_resetjp_3496_;
}
else
{
lean_dec(v_x_3485_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3506_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3502_; 
v___x_3499_ = lean_box(v_a_3484_);
v___x_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3500_);
v___x_3502_ = v___x_3497_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
return v___x_3504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_3508_, lean_object* v_x_3509_, lean_object* v___y_3510_){
_start:
{
uint8_t v_a_5795__boxed_3511_; lean_object* v_res_3512_; 
v_a_5795__boxed_3511_ = lean_unbox(v_a_3508_);
v_res_3512_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5795__boxed_3511_, v_x_3509_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_3513_, lean_object* v_interestWaiter_3514_, uint8_t v_closed_3515_, lean_object* v_knownSize_3516_, lean_object* v_pendingIncompleteChunk_3517_, lean_object* v_closeError_3518_, lean_object* v___y_3519_, lean_object* v_chunk_3520_, lean_object* v___f_3521_, lean_object* v_x_3522_){
_start:
{
if (lean_obj_tag(v_x_3522_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3532_; 
lean_dec_ref(v___f_3521_);
lean_dec(v_closeError_3518_);
lean_dec(v_pendingIncompleteChunk_3517_);
lean_dec(v_knownSize_3516_);
lean_dec(v_interestWaiter_3514_);
lean_dec(v_pendingProducer_3513_);
v_a_3524_ = lean_ctor_get(v_x_3522_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_x_3522_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3526_ = v_x_3522_;
v_isShared_3527_ = v_isSharedCheck_3532_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v_x_3522_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3532_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
return v___x_3530_;
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3559_; 
v_a_3533_ = lean_ctor_get(v_x_3522_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_x_3522_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3535_ = v_x_3522_;
v_isShared_3536_ = v_isSharedCheck_3559_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v_x_3522_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3559_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
uint8_t v___x_3537_; 
v___x_3537_ = lean_unbox(v_a_3533_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___f_3541_; lean_object* v___x_3543_; 
lean_dec_ref(v___f_3521_);
v___x_3538_ = lean_box(0);
v___x_3539_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3539_, 0, v_pendingProducer_3513_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
lean_ctor_set(v___x_3539_, 2, v_interestWaiter_3514_);
lean_ctor_set(v___x_3539_, 3, v_knownSize_3516_);
lean_ctor_set(v___x_3539_, 4, v_pendingIncompleteChunk_3517_);
lean_ctor_set(v___x_3539_, 5, v_closeError_3518_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*6, v_closed_3515_);
v___x_3540_ = lean_st_ref_set(v___y_3519_, v___x_3539_);
lean_inc(v_a_3533_);
v___f_3541_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3541_, 0, v_a_3533_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3540_);
v___x_3543_ = v___x_3535_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3540_);
v___x_3543_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; uint8_t v___x_3546_; lean_object* v___x_3547_; 
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
v___x_3545_ = lean_unsigned_to_nat(0u);
v___x_3546_ = lean_unbox(v_a_3533_);
lean_dec(v_a_3533_);
v___x_3547_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3545_, v___x_3546_, v___x_3544_, v___f_3541_);
return v___x_3547_;
}
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3554_; 
lean_dec(v_a_3533_);
v___x_3549_ = lean_box(0);
v___x_3550_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_3516_, v_chunk_3520_);
v___x_3551_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3551_, 0, v_pendingProducer_3513_);
lean_ctor_set(v___x_3551_, 1, v___x_3549_);
lean_ctor_set(v___x_3551_, 2, v_interestWaiter_3514_);
lean_ctor_set(v___x_3551_, 3, v___x_3550_);
lean_ctor_set(v___x_3551_, 4, v_pendingIncompleteChunk_3517_);
lean_ctor_set(v___x_3551_, 5, v_closeError_3518_);
lean_ctor_set_uint8(v___x_3551_, sizeof(void*)*6, v_closed_3515_);
v___x_3552_ = lean_st_ref_set(v___y_3519_, v___x_3551_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3552_);
v___x_3554_ = v___x_3535_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
v___x_3556_ = lean_unsigned_to_nat(0u);
v___x_3557_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3556_, v_closed_3515_, v___x_3555_, v___f_3521_);
return v___x_3557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_3560_, lean_object* v_interestWaiter_3561_, lean_object* v_closed_3562_, lean_object* v_knownSize_3563_, lean_object* v_pendingIncompleteChunk_3564_, lean_object* v_closeError_3565_, lean_object* v___y_3566_, lean_object* v_chunk_3567_, lean_object* v___f_3568_, lean_object* v_x_3569_, lean_object* v___y_3570_){
_start:
{
uint8_t v_closed_boxed_3571_; lean_object* v_res_3572_; 
v_closed_boxed_3571_ = lean_unbox(v_closed_3562_);
v_res_3572_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_3560_, v_interestWaiter_3561_, v_closed_boxed_3571_, v_knownSize_3563_, v_pendingIncompleteChunk_3564_, v_closeError_3565_, v___y_3566_, v_chunk_3567_, v___f_3568_, v_x_3569_);
lean_dec_ref(v_chunk_3567_);
lean_dec(v___y_3566_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v_chunk_3591_, lean_object* v___y_3592_, lean_object* v_a_3593_, lean_object* v___f_3594_, lean_object* v_x_3595_){
_start:
{
if (lean_obj_tag(v_x_3595_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3605_; 
lean_dec_ref(v___f_3594_);
lean_dec(v_a_3593_);
lean_dec_ref(v_chunk_3591_);
v_a_3597_ = lean_ctor_get(v_x_3595_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_x_3595_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3599_ = v_x_3595_;
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v_x_3595_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
return v___x_3603_;
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3662_; 
v_a_3606_ = lean_ctor_get(v_x_3595_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_x_3595_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3608_ = v_x_3595_;
v_isShared_3609_ = v_isSharedCheck_3662_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v_x_3595_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3662_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
uint8_t v_closed_3610_; 
v_closed_3610_ = lean_ctor_get_uint8(v_a_3606_, sizeof(void*)*6);
if (v_closed_3610_ == 0)
{
lean_object* v_pendingConsumer_3611_; 
v_pendingConsumer_3611_ = lean_ctor_get(v_a_3606_, 1);
lean_inc(v_pendingConsumer_3611_);
if (lean_obj_tag(v_pendingConsumer_3611_) == 1)
{
lean_object* v_pendingProducer_3612_; lean_object* v_interestWaiter_3613_; lean_object* v_knownSize_3614_; lean_object* v_pendingIncompleteChunk_3615_; lean_object* v_closeError_3616_; lean_object* v_val_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3636_; 
lean_dec_ref(v___f_3594_);
lean_dec(v_a_3593_);
v_pendingProducer_3612_ = lean_ctor_get(v_a_3606_, 0);
lean_inc(v_pendingProducer_3612_);
v_interestWaiter_3613_ = lean_ctor_get(v_a_3606_, 2);
lean_inc(v_interestWaiter_3613_);
v_knownSize_3614_ = lean_ctor_get(v_a_3606_, 3);
lean_inc(v_knownSize_3614_);
v_pendingIncompleteChunk_3615_ = lean_ctor_get(v_a_3606_, 4);
lean_inc(v_pendingIncompleteChunk_3615_);
v_closeError_3616_ = lean_ctor_get(v_a_3606_, 5);
lean_inc(v_closeError_3616_);
lean_dec(v_a_3606_);
v_val_3617_ = lean_ctor_get(v_pendingConsumer_3611_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_pendingConsumer_3611_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3619_ = v_pendingConsumer_3611_;
v_isShared_3620_ = v_isSharedCheck_3636_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_val_3617_);
lean_dec(v_pendingConsumer_3611_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3636_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
lean_inc_ref(v_chunk_3591_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 0, v_chunk_3591_);
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_chunk_3591_);
v___x_3622_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3624_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3622_);
v___x_3624_ = v___x_3608_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
uint8_t v___x_3625_; lean_object* v___f_3626_; lean_object* v___x_3627_; lean_object* v___f_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3625_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_3617_, v___x_3624_);
lean_dec(v_val_3617_);
v___f_3626_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_3627_ = lean_box(v_closed_3610_);
lean_inc(v___y_3592_);
v___f_3628_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 11, 9);
lean_closure_set(v___f_3628_, 0, v_pendingProducer_3612_);
lean_closure_set(v___f_3628_, 1, v_interestWaiter_3613_);
lean_closure_set(v___f_3628_, 2, v___x_3627_);
lean_closure_set(v___f_3628_, 3, v_knownSize_3614_);
lean_closure_set(v___f_3628_, 4, v_pendingIncompleteChunk_3615_);
lean_closure_set(v___f_3628_, 5, v_closeError_3616_);
lean_closure_set(v___f_3628_, 6, v___y_3592_);
lean_closure_set(v___f_3628_, 7, v_chunk_3591_);
lean_closure_set(v___f_3628_, 8, v___f_3626_);
v___x_3629_ = lean_box(v___x_3625_);
v___x_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
v___x_3632_ = lean_unsigned_to_nat(0u);
v___x_3633_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3632_, v_closed_3610_, v___x_3631_, v___f_3628_);
return v___x_3633_;
}
}
}
}
else
{
lean_object* v_pendingProducer_3637_; 
v_pendingProducer_3637_ = lean_ctor_get(v_a_3606_, 0);
if (lean_obj_tag(v_pendingProducer_3637_) == 0)
{
lean_object* v_interestWaiter_3638_; lean_object* v_knownSize_3639_; lean_object* v_pendingIncompleteChunk_3640_; lean_object* v_closeError_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3657_; 
v_interestWaiter_3638_ = lean_ctor_get(v_a_3606_, 2);
v_knownSize_3639_ = lean_ctor_get(v_a_3606_, 3);
v_pendingIncompleteChunk_3640_ = lean_ctor_get(v_a_3606_, 4);
v_closeError_3641_ = lean_ctor_get(v_a_3606_, 5);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_a_3606_);
if (v_isSharedCheck_3657_ == 0)
{
lean_object* v_unused_3658_; lean_object* v_unused_3659_; 
v_unused_3658_ = lean_ctor_get(v_a_3606_, 1);
lean_dec(v_unused_3658_);
v_unused_3659_ = lean_ctor_get(v_a_3606_, 0);
lean_dec(v_unused_3659_);
v___x_3643_ = v_a_3606_;
v_isShared_3644_ = v_isSharedCheck_3657_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_closeError_3641_);
lean_inc(v_pendingIncompleteChunk_3640_);
lean_inc(v_knownSize_3639_);
lean_inc(v_interestWaiter_3638_);
lean_dec(v_a_3606_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3657_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v_chunk_3591_);
lean_ctor_set(v___x_3645_, 1, v_a_3593_);
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 0, v___x_3646_);
v___x_3648_ = v___x_3643_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_pendingConsumer_3611_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v_interestWaiter_3638_);
lean_ctor_set(v_reuseFailAlloc_3656_, 3, v_knownSize_3639_);
lean_ctor_set(v_reuseFailAlloc_3656_, 4, v_pendingIncompleteChunk_3640_);
lean_ctor_set(v_reuseFailAlloc_3656_, 5, v_closeError_3641_);
lean_ctor_set_uint8(v_reuseFailAlloc_3656_, sizeof(void*)*6, v_closed_3610_);
v___x_3648_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3649_ = lean_st_ref_set(v___y_3592_, v___x_3648_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3649_);
v___x_3651_ = v___x_3608_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
v___x_3653_ = lean_unsigned_to_nat(0u);
v___x_3654_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3653_, v_closed_3610_, v___x_3652_, v___f_3594_);
return v___x_3654_;
}
}
}
}
else
{
lean_object* v___x_3660_; 
lean_dec(v_pendingConsumer_3611_);
lean_del_object(v___x_3608_);
lean_dec(v_a_3606_);
lean_dec_ref(v___f_3594_);
lean_dec(v_a_3593_);
lean_dec_ref(v_chunk_3591_);
v___x_3660_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_3660_;
}
}
}
else
{
lean_object* v___x_3661_; 
lean_del_object(v___x_3608_);
lean_dec(v_a_3606_);
lean_dec_ref(v___f_3594_);
lean_dec(v_a_3593_);
lean_dec_ref(v_chunk_3591_);
v___x_3661_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_3661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v_chunk_3663_, lean_object* v___y_3664_, lean_object* v_a_3665_, lean_object* v___f_3666_, lean_object* v_x_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v_chunk_3663_, v___y_3664_, v_a_3665_, v___f_3666_, v_x_3667_);
lean_dec(v___y_3664_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_3670_, lean_object* v___f_3671_, lean_object* v_x_3672_){
_start:
{
if (lean_obj_tag(v_x_3672_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3682_; 
lean_dec_ref(v___f_3671_);
v_a_3674_ = lean_ctor_get(v_x_3672_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_x_3672_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3676_ = v_x_3672_;
v_isShared_3677_ = v_isSharedCheck_3682_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v_x_3672_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3682_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
lean_object* v___x_3680_; 
v___x_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3679_);
return v___x_3680_;
}
}
}
else
{
lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3694_; 
v_isSharedCheck_3694_ = !lean_is_exclusive(v_x_3672_);
if (v_isSharedCheck_3694_ == 0)
{
lean_object* v_unused_3695_; 
v_unused_3695_ = lean_ctor_get(v_x_3672_, 0);
lean_dec(v_unused_3695_);
v___x_3684_ = v_x_3672_;
v_isShared_3685_ = v_isSharedCheck_3694_;
goto v_resetjp_3683_;
}
else
{
lean_dec(v_x_3672_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3694_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3686_ = lean_st_ref_get(v___y_3670_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3686_);
v___x_3688_ = v___x_3684_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; lean_object* v___x_3692_; 
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
v___x_3690_ = lean_unsigned_to_nat(0u);
v___x_3691_ = 0;
v___x_3692_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3690_, v___x_3691_, v___x_3689_, v___f_3671_);
return v___x_3692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_3696_, lean_object* v___f_3697_, lean_object* v_x_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_3696_, v___f_3697_, v_x_3698_);
lean_dec(v___y_3696_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_3701_, lean_object* v_a_3702_, lean_object* v___f_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; lean_object* v___f_3707_; lean_object* v___f_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; lean_object* v___x_3711_; 
v___x_3706_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3704_);
lean_inc_n(v___y_3704_, 2);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_3707_, 0, v_chunk_3701_);
lean_closure_set(v___f_3707_, 1, v___y_3704_);
lean_closure_set(v___f_3707_, 2, v_a_3702_);
lean_closure_set(v___f_3707_, 3, v___f_3703_);
v___f_3708_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_3708_, 0, v___y_3704_);
lean_closure_set(v___f_3708_, 1, v___f_3707_);
v___x_3709_ = lean_unsigned_to_nat(0u);
v___x_3710_ = 0;
v___x_3711_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3709_, v___x_3710_, v___x_3706_, v___f_3708_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_3712_, lean_object* v_a_3713_, lean_object* v___f_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_3712_, v_a_3713_, v___f_3714_, v___y_3715_);
lean_dec(v___y_3715_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_3723_, lean_object* v___f_3724_, lean_object* v___f_3725_, lean_object* v_stream_3726_, lean_object* v_chunk_3727_, lean_object* v___f_3728_, lean_object* v_x_3729_){
_start:
{
if (lean_obj_tag(v_x_3729_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v___f_3728_);
lean_dec_ref(v_chunk_3727_);
lean_dec_ref(v_stream_3726_);
lean_dec_ref(v___f_3725_);
lean_dec_ref(v___f_3724_);
v_a_3731_ = lean_ctor_get(v_x_3729_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v_x_3729_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3733_ = v_x_3729_;
v_isShared_3734_ = v_isSharedCheck_3739_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v_x_3729_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3739_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3737_; 
v___x_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
return v___x_3737_;
}
}
}
else
{
lean_object* v_a_3740_; 
v_a_3740_ = lean_ctor_get(v_x_3729_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v_x_3729_, 1);
if (lean_obj_tag(v_a_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref(v___f_3728_);
lean_dec_ref(v_chunk_3727_);
lean_dec_ref(v_stream_3726_);
lean_dec_ref(v___f_3725_);
lean_dec_ref(v___f_3724_);
v_a_3741_ = lean_ctor_get(v_a_3740_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_a_3740_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3743_ = v_a_3740_;
v_isShared_3744_ = v_isSharedCheck_3749_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v_a_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3749_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3747_; 
v___x_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
return v___x_3747_;
}
}
}
else
{
lean_object* v_a_3750_; 
v_a_3750_ = lean_ctor_get(v_a_3740_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v_a_3740_, 1);
if (lean_obj_tag(v_a_3750_) == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
lean_dec_ref(v___f_3728_);
lean_dec_ref(v_chunk_3727_);
lean_dec_ref(v_stream_3726_);
v___x_3751_ = lean_io_promise_result_opt(v_a_3723_);
v___x_3752_ = lean_unsigned_to_nat(0u);
v___x_3753_ = 0;
v___x_3754_ = lean_task_map(v___f_3724_, v___x_3751_, v___x_3752_, v___x_3753_);
v___x_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
v___x_3756_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3752_, v___x_3753_, v___x_3755_, v___f_3725_);
return v___x_3756_;
}
else
{
lean_object* v_val_3757_; uint8_t v___x_3758_; 
lean_dec_ref(v___f_3725_);
lean_dec_ref(v___f_3724_);
v_val_3757_ = lean_ctor_get(v_a_3750_, 0);
lean_inc(v_val_3757_);
lean_dec_ref_known(v_a_3750_, 1);
v___x_3758_ = lean_unbox(v_val_3757_);
lean_dec(v_val_3757_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; 
lean_dec_ref(v___f_3728_);
v___x_3759_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3726_, v_chunk_3727_);
return v___x_3759_;
}
else
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
lean_dec_ref(v_chunk_3727_);
lean_dec_ref(v_stream_3726_);
v___x_3760_ = lean_box(0);
v___x_3761_ = lean_apply_2(v___f_3728_, v___x_3760_, lean_box(0));
return v___x_3761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_3762_, lean_object* v___f_3763_, lean_object* v___f_3764_, lean_object* v_stream_3765_, lean_object* v_chunk_3766_, lean_object* v___f_3767_, lean_object* v_x_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_3762_, v___f_3763_, v___f_3764_, v_stream_3765_, v_chunk_3766_, v___f_3767_, v_x_3768_);
lean_dec(v_a_3762_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_3771_, lean_object* v___f_3772_, lean_object* v_stream_3773_, lean_object* v___f_3774_, lean_object* v___f_3775_, lean_object* v___f_3776_, lean_object* v_x_3777_){
_start:
{
if (lean_obj_tag(v_x_3777_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3787_; 
lean_dec_ref(v___f_3776_);
lean_dec_ref(v___f_3775_);
lean_dec_ref(v___f_3774_);
lean_dec_ref(v_stream_3773_);
lean_dec_ref(v___f_3772_);
lean_dec_ref(v_chunk_3771_);
v_a_3779_ = lean_ctor_get(v_x_3777_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_x_3777_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3781_ = v_x_3777_;
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v_x_3777_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
return v___x_3785_;
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___f_3789_; lean_object* v___x_3790_; lean_object* v___f_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; lean_object* v___x_3794_; 
v_a_3788_ = lean_ctor_get(v_x_3777_, 0);
lean_inc_n(v_a_3788_, 2);
lean_dec_ref_known(v_x_3777_, 1);
lean_inc_ref(v_chunk_3771_);
v___f_3789_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_3789_, 0, v_chunk_3771_);
lean_closure_set(v___f_3789_, 1, v_a_3788_);
lean_closure_set(v___f_3789_, 2, v___f_3772_);
lean_inc_ref(v_stream_3773_);
v___x_3790_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3773_, v___f_3789_);
v___f_3791_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3791_, 0, v_a_3788_);
lean_closure_set(v___f_3791_, 1, v___f_3774_);
lean_closure_set(v___f_3791_, 2, v___f_3775_);
lean_closure_set(v___f_3791_, 3, v_stream_3773_);
lean_closure_set(v___f_3791_, 4, v_chunk_3771_);
lean_closure_set(v___f_3791_, 5, v___f_3776_);
v___x_3792_ = lean_unsigned_to_nat(0u);
v___x_3793_ = 0;
v___x_3794_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3792_, v___x_3793_, v___x_3790_, v___f_3791_);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_3795_, lean_object* v___f_3796_, lean_object* v_stream_3797_, lean_object* v___f_3798_, lean_object* v___f_3799_, lean_object* v___f_3800_, lean_object* v_x_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_3795_, v___f_3796_, v_stream_3797_, v___f_3798_, v___f_3799_, v___f_3800_, v_x_3801_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_3804_, lean_object* v_chunk_3805_){
_start:
{
lean_object* v___x_3807_; lean_object* v___f_3808_; lean_object* v___f_3809_; lean_object* v___f_3810_; lean_object* v___f_3811_; lean_object* v___f_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; lean_object* v___x_3817_; 
v___x_3807_ = lean_io_promise_new();
v___f_3808_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_3809_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_3810_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_3811_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_3812_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_3812_, 0, v_chunk_3805_);
lean_closure_set(v___f_3812_, 1, v___f_3808_);
lean_closure_set(v___f_3812_, 2, v_stream_3804_);
lean_closure_set(v___f_3812_, 3, v___f_3811_);
lean_closure_set(v___f_3812_, 4, v___f_3810_);
lean_closure_set(v___f_3812_, 5, v___f_3809_);
v___x_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3807_);
v___x_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
v___x_3815_ = lean_unsigned_to_nat(0u);
v___x_3816_ = 0;
v___x_3817_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3815_, v___x_3816_, v___x_3814_, v___f_3812_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_3818_, lean_object* v_chunk_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3818_, v_chunk_3819_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_3822_, lean_object* v_x_3823_){
_start:
{
if (lean_obj_tag(v_x_3823_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_stream_3822_);
v_a_3825_ = lean_ctor_get(v_x_3823_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_x_3823_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3827_ = v_x_3823_;
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v_x_3823_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3831_; 
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
return v___x_3831_;
}
}
}
else
{
lean_object* v_a_3834_; 
v_a_3834_ = lean_ctor_get(v_x_3823_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v_x_3823_, 1);
if (lean_obj_tag(v_a_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3843_; 
lean_dec_ref(v_stream_3822_);
v_a_3835_ = lean_ctor_get(v_a_3834_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_a_3834_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3837_ = v_a_3834_;
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v_a_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
return v___x_3841_;
}
}
}
else
{
lean_object* v_a_3844_; 
v_a_3844_ = lean_ctor_get(v_a_3834_, 0);
lean_inc(v_a_3844_);
lean_dec_ref_known(v_a_3834_, 1);
if (lean_obj_tag(v_a_3844_) == 0)
{
lean_object* v___x_3845_; 
lean_dec_ref(v_stream_3822_);
v___x_3845_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
return v___x_3845_;
}
else
{
lean_object* v_val_3846_; lean_object* v_data_3847_; lean_object* v_extensions_3848_; uint8_t v___x_3849_; 
v_val_3846_ = lean_ctor_get(v_a_3844_, 0);
lean_inc(v_val_3846_);
lean_dec_ref_known(v_a_3844_, 1);
v_data_3847_ = lean_ctor_get(v_val_3846_, 0);
v_extensions_3848_ = lean_ctor_get(v_val_3846_, 1);
v___x_3849_ = l_ByteArray_isEmpty(v_data_3847_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; 
v___x_3850_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3822_, v_val_3846_);
return v___x_3850_;
}
else
{
lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; 
v___x_3851_ = lean_array_get_size(v_extensions_3848_);
v___x_3852_ = lean_unsigned_to_nat(0u);
v___x_3853_ = lean_nat_dec_eq(v___x_3851_, v___x_3852_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; 
v___x_3854_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3822_, v_val_3846_);
return v___x_3854_;
}
else
{
lean_object* v___x_3855_; 
lean_dec(v_val_3846_);
lean_dec_ref(v_stream_3822_);
v___x_3855_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
return v___x_3855_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object* v_stream_3856_, lean_object* v_x_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_3856_, v_x_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object* v_stream_3860_, lean_object* v_chunk_3861_, uint8_t v_incomplete_3862_){
_start:
{
lean_object* v___x_3864_; lean_object* v___f_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; lean_object* v___x_3870_; 
lean_inc_ref(v_stream_3860_);
v___x_3864_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3860_, v_chunk_3861_, v_incomplete_3862_);
v___f_3865_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3865_, 0, v_stream_3860_);
v___x_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3864_);
v___x_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
v___x_3868_ = lean_unsigned_to_nat(0u);
v___x_3869_ = 0;
v___x_3870_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3868_, v___x_3869_, v___x_3867_, v___f_3865_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object* v_stream_3871_, lean_object* v_chunk_3872_, lean_object* v_incomplete_3873_, lean_object* v_a_3874_){
_start:
{
uint8_t v_incomplete_boxed_3875_; lean_object* v_res_3876_; 
v_incomplete_boxed_3875_ = lean_unbox(v_incomplete_3873_);
v_res_3876_ = l_Std_Http_Body_Stream_send(v_stream_3871_, v_chunk_3872_, v_incomplete_boxed_3875_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object* v_x_3877_){
_start:
{
uint8_t v___y_3880_; 
if (lean_obj_tag(v_x_3877_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3892_; 
v_a_3884_ = lean_ctor_get(v_x_3877_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_x_3877_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3886_ = v_x_3877_;
v_isShared_3887_ = v_isSharedCheck_3892_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v_x_3877_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3892_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
return v___x_3890_;
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v_pendingConsumer_3894_; 
v_a_3893_ = lean_ctor_get(v_x_3877_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v_x_3877_, 1);
v_pendingConsumer_3894_ = lean_ctor_get(v_a_3893_, 1);
lean_inc(v_pendingConsumer_3894_);
lean_dec(v_a_3893_);
if (lean_obj_tag(v_pendingConsumer_3894_) == 0)
{
uint8_t v___x_3895_; 
v___x_3895_ = 0;
v___y_3880_ = v___x_3895_;
goto v___jp_3879_;
}
else
{
uint8_t v___x_3896_; 
lean_dec_ref_known(v_pendingConsumer_3894_, 1);
v___x_3896_ = 1;
v___y_3880_ = v___x_3896_;
goto v___jp_3879_;
}
}
v___jp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3881_ = lean_box(v___y_3880_);
v___x_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
return v___x_3883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object* v_x_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_3897_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object* v_a_3901_){
_start:
{
lean_object* v___x_3903_; lean_object* v___f_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; 
v___x_3903_ = lean_st_ref_get(v_a_3901_);
v___f_3904_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3903_);
v___x_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
v___x_3907_ = lean_unsigned_to_nat(0u);
v___x_3908_ = 0;
v___x_3909_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3907_, v___x_3908_, v___x_3906_, v___f_3904_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object* v_a_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_3910_);
lean_dec(v_a_3910_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object* v___y_3913_, lean_object* v_x_3914_){
_start:
{
if (lean_obj_tag(v_x_3914_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3924_; 
v_a_3916_ = lean_ctor_get(v_x_3914_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_x_3914_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3918_ = v_x_3914_;
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v_x_3914_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; 
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
}
}
else
{
lean_object* v___x_3925_; 
lean_dec_ref_known(v_x_3914_, 1);
v___x_3925_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_3913_);
return v___x_3925_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object* v___y_3926_, lean_object* v_x_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_3926_, v_x_3927_);
lean_dec(v___y_3926_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object* v___y_3930_){
_start:
{
lean_object* v___x_3932_; lean_object* v___f_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; lean_object* v___x_3936_; 
v___x_3932_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3930_);
lean_inc(v___y_3930_);
v___f_3933_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3933_, 0, v___y_3930_);
v___x_3934_ = lean_unsigned_to_nat(0u);
v___x_3935_ = 0;
v___x_3936_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3934_, v___x_3935_, v___x_3932_, v___f_3933_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_3937_);
lean_dec(v___y_3937_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object* v_stream_3941_){
_start:
{
lean_object* v___f_3943_; lean_object* v___x_3944_; 
v___f_3943_ = ((lean_object*)(l_Std_Http_Body_Stream_hasInterest___closed__0));
v___x_3944_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3941_, v___f_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object* v_stream_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Std_Http_Body_Stream_hasInterest(v_stream_3945_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object* v_lose_3948_, lean_object* v___y_3949_, uint8_t v___x_3950_, lean_object* v_promise_3951_, lean_object* v_x_3952_){
_start:
{
if (lean_obj_tag(v_x_3952_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3962_; 
lean_dec_ref(v_lose_3948_);
v_a_3954_ = lean_ctor_get(v_x_3952_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_x_3952_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3956_ = v_x_3952_;
v_isShared_3957_ = v_isSharedCheck_3962_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v_x_3952_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3962_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
lean_object* v___x_3960_; 
v___x_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
return v___x_3960_;
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3976_; 
v_a_3963_ = lean_ctor_get(v_x_3952_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v_x_3952_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3965_ = v_x_3952_;
v_isShared_3966_ = v_isSharedCheck_3976_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v_x_3952_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3976_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
uint8_t v___x_3967_; 
v___x_3967_ = lean_unbox(v_a_3963_);
lean_dec(v_a_3963_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
lean_del_object(v___x_3965_);
lean_inc(v___y_3949_);
v___x_3968_ = lean_apply_2(v_lose_3948_, v___y_3949_, lean_box(0));
return v___x_3968_;
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3971_; 
lean_dec_ref(v_lose_3948_);
v___x_3969_ = lean_box(v___x_3950_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 0, v___x_3969_);
v___x_3971_ = v___x_3965_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3969_);
v___x_3971_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3972_ = lean_io_promise_resolve(v___x_3971_, v_promise_3951_);
v___x_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object* v_lose_3977_, lean_object* v___y_3978_, lean_object* v___x_3979_, lean_object* v_promise_3980_, lean_object* v_x_3981_, lean_object* v___y_3982_){
_start:
{
uint8_t v___x_4642__boxed_3983_; lean_object* v_res_3984_; 
v___x_4642__boxed_3983_ = lean_unbox(v___x_3979_);
v_res_3984_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_3977_, v___y_3978_, v___x_4642__boxed_3983_, v_promise_3980_, v_x_3981_);
lean_dec(v_promise_3980_);
lean_dec(v___y_3978_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_3985_, lean_object* v_lose_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_finished_3989_; lean_object* v_promise_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___f_3994_; uint8_t v___y_3996_; uint8_t v___x_4005_; 
v_finished_3989_ = lean_ctor_get(v_w_3985_, 0);
lean_inc(v_finished_3989_);
v_promise_3990_ = lean_ctor_get(v_w_3985_, 1);
lean_inc(v_promise_3990_);
lean_dec_ref(v_w_3985_);
v___x_3991_ = lean_st_ref_take(v_finished_3989_);
v___x_3992_ = 0;
v___x_3993_ = lean_box(v___x_3992_);
lean_inc(v___y_3987_);
v___f_3994_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3994_, 0, v_lose_3986_);
lean_closure_set(v___f_3994_, 1, v___y_3987_);
lean_closure_set(v___f_3994_, 2, v___x_3993_);
lean_closure_set(v___f_3994_, 3, v_promise_3990_);
v___x_4005_ = lean_unbox(v___x_3991_);
lean_dec(v___x_3991_);
if (v___x_4005_ == 0)
{
uint8_t v___x_4006_; 
v___x_4006_ = 1;
v___y_3996_ = v___x_4006_;
goto v___jp_3995_;
}
else
{
v___y_3996_ = v___x_3992_;
goto v___jp_3995_;
}
v___jp_3995_:
{
uint8_t v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_3997_ = 1;
v___x_3998_ = lean_box(v___x_3997_);
v___x_3999_ = lean_st_ref_set(v_finished_3989_, v___x_3998_);
lean_dec(v_finished_3989_);
v___x_4000_ = lean_box(v___y_3996_);
v___x_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4003_, v___x_3992_, v___x_4002_, v___f_3994_);
return v___x_4004_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object* v_w_4007_, lean_object* v_lose_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_4007_, v_lose_4008_, v___y_4009_);
lean_dec(v___y_4009_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object* v_w_4012_, lean_object* v_lose_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_finished_4016_; lean_object* v_promise_4017_; lean_object* v___x_4018_; uint8_t v___x_4019_; lean_object* v___x_4020_; lean_object* v___f_4021_; uint8_t v___y_4023_; uint8_t v___x_4032_; 
v_finished_4016_ = lean_ctor_get(v_w_4012_, 0);
lean_inc(v_finished_4016_);
v_promise_4017_ = lean_ctor_get(v_w_4012_, 1);
lean_inc(v_promise_4017_);
lean_dec_ref(v_w_4012_);
v___x_4018_ = lean_st_ref_take(v_finished_4016_);
v___x_4019_ = 1;
v___x_4020_ = lean_box(v___x_4019_);
lean_inc(v___y_4014_);
v___f_4021_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4021_, 0, v_lose_4013_);
lean_closure_set(v___f_4021_, 1, v___y_4014_);
lean_closure_set(v___f_4021_, 2, v___x_4020_);
lean_closure_set(v___f_4021_, 3, v_promise_4017_);
v___x_4032_ = lean_unbox(v___x_4018_);
lean_dec(v___x_4018_);
if (v___x_4032_ == 0)
{
v___y_4023_ = v___x_4019_;
goto v___jp_4022_;
}
else
{
uint8_t v___x_4033_; 
v___x_4033_ = 0;
v___y_4023_ = v___x_4033_;
goto v___jp_4022_;
}
v___jp_4022_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; lean_object* v___x_4031_; 
v___x_4024_ = lean_box(v___x_4019_);
v___x_4025_ = lean_st_ref_set(v_finished_4016_, v___x_4024_);
lean_dec(v_finished_4016_);
v___x_4026_ = lean_box(v___y_4023_);
v___x_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
v___x_4029_ = lean_unsigned_to_nat(0u);
v___x_4030_ = 0;
v___x_4031_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4029_, v___x_4030_, v___x_4028_, v___f_4021_);
return v___x_4031_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_4034_, lean_object* v_lose_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_4034_, v_lose_4035_, v___y_4036_);
lean_dec(v___y_4036_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_4055_){
_start:
{
if (lean_obj_tag(v_x_4055_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4065_; 
v_a_4057_ = lean_ctor_get(v_x_4055_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_x_4055_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4059_ = v_x_4055_;
v_isShared_4060_ = v_isSharedCheck_4065_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v_x_4055_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4065_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; 
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
return v___x_4063_;
}
}
}
else
{
lean_object* v_a_4066_; lean_object* v_pendingConsumer_4067_; 
v_a_4066_ = lean_ctor_get(v_x_4055_, 0);
lean_inc(v_a_4066_);
lean_dec_ref_known(v_x_4055_, 1);
v_pendingConsumer_4067_ = lean_ctor_get(v_a_4066_, 1);
if (lean_obj_tag(v_pendingConsumer_4067_) == 0)
{
uint8_t v_closed_4068_; 
v_closed_4068_ = lean_ctor_get_uint8(v_a_4066_, sizeof(void*)*6);
lean_dec(v_a_4066_);
if (v_closed_4068_ == 0)
{
lean_object* v___x_4069_; 
v___x_4069_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_4069_;
}
else
{
lean_object* v___x_4070_; 
v___x_4070_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_4070_;
}
}
else
{
lean_object* v___x_4071_; 
lean_dec(v_a_4066_);
v___x_4071_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_4071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_4072_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_4082_, lean_object* v___y_4083_, lean_object* v_x_4084_){
_start:
{
if (lean_obj_tag(v_x_4084_) == 0)
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4094_; 
lean_dec_ref(v_waiter_4082_);
v_a_4086_ = lean_ctor_get(v_x_4084_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_x_4084_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4088_ = v_x_4084_;
v_isShared_4089_ = v_isSharedCheck_4094_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v_x_4084_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4094_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
lean_object* v___x_4092_; 
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
return v___x_4092_;
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4126_; 
v_a_4095_ = lean_ctor_get(v_x_4084_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_x_4084_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4097_ = v_x_4084_;
v_isShared_4098_ = v_isSharedCheck_4126_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v_x_4084_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4126_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v_pendingConsumer_4099_; 
v_pendingConsumer_4099_ = lean_ctor_get(v_a_4095_, 1);
lean_inc(v_pendingConsumer_4099_);
if (lean_obj_tag(v_pendingConsumer_4099_) == 0)
{
uint8_t v_closed_4100_; 
v_closed_4100_ = lean_ctor_get_uint8(v_a_4095_, sizeof(void*)*6);
if (v_closed_4100_ == 0)
{
lean_object* v_interestWaiter_4101_; 
v_interestWaiter_4101_ = lean_ctor_get(v_a_4095_, 2);
if (lean_obj_tag(v_interestWaiter_4101_) == 0)
{
lean_object* v_pendingProducer_4102_; lean_object* v_knownSize_4103_; lean_object* v_pendingIncompleteChunk_4104_; lean_object* v_closeError_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4118_; 
v_pendingProducer_4102_ = lean_ctor_get(v_a_4095_, 0);
v_knownSize_4103_ = lean_ctor_get(v_a_4095_, 3);
v_pendingIncompleteChunk_4104_ = lean_ctor_get(v_a_4095_, 4);
v_closeError_4105_ = lean_ctor_get(v_a_4095_, 5);
v_isSharedCheck_4118_ = !lean_is_exclusive(v_a_4095_);
if (v_isSharedCheck_4118_ == 0)
{
lean_object* v_unused_4119_; lean_object* v_unused_4120_; 
v_unused_4119_ = lean_ctor_get(v_a_4095_, 2);
lean_dec(v_unused_4119_);
v_unused_4120_ = lean_ctor_get(v_a_4095_, 1);
lean_dec(v_unused_4120_);
v___x_4107_ = v_a_4095_;
v_isShared_4108_ = v_isSharedCheck_4118_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_closeError_4105_);
lean_inc(v_pendingIncompleteChunk_4104_);
lean_inc(v_knownSize_4103_);
lean_inc(v_pendingProducer_4102_);
lean_dec(v_a_4095_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4118_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4109_; lean_object* v___x_4111_; 
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_waiter_4082_);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 2, v___x_4109_);
v___x_4111_ = v___x_4107_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_pendingProducer_4102_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v_pendingConsumer_4099_);
lean_ctor_set(v_reuseFailAlloc_4117_, 2, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4117_, 3, v_knownSize_4103_);
lean_ctor_set(v_reuseFailAlloc_4117_, 4, v_pendingIncompleteChunk_4104_);
lean_ctor_set(v_reuseFailAlloc_4117_, 5, v_closeError_4105_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, sizeof(void*)*6, v_closed_4100_);
v___x_4111_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4112_ = lean_st_ref_set(v___y_4083_, v___x_4111_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4112_);
v___x_4114_ = v___x_4097_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; 
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
return v___x_4115_;
}
}
}
}
else
{
lean_object* v___x_4121_; 
lean_del_object(v___x_4097_);
lean_dec(v_a_4095_);
lean_dec_ref(v_waiter_4082_);
v___x_4121_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_4121_;
}
}
else
{
lean_object* v___f_4122_; lean_object* v___x_4123_; 
lean_del_object(v___x_4097_);
lean_dec(v_a_4095_);
v___f_4122_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4123_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_4082_, v___f_4122_, v___y_4083_);
return v___x_4123_;
}
}
else
{
lean_object* v___f_4124_; lean_object* v___x_4125_; 
lean_dec_ref_known(v_pendingConsumer_4099_, 1);
lean_del_object(v___x_4097_);
lean_dec(v_a_4095_);
v___f_4124_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4125_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_4082_, v___f_4124_, v___y_4083_);
return v___x_4125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_4127_, lean_object* v___y_4128_, lean_object* v_x_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_4127_, v___y_4128_, v_x_4129_);
lean_dec(v___y_4128_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_4132_, lean_object* v___f_4133_, lean_object* v_x_4134_){
_start:
{
if (lean_obj_tag(v_x_4134_) == 0)
{
lean_object* v___x_4136_; 
lean_dec_ref(v___f_4133_);
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v_x_4134_);
return v___x_4136_;
}
else
{
lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4148_; 
v_isSharedCheck_4148_ = !lean_is_exclusive(v_x_4134_);
if (v_isSharedCheck_4148_ == 0)
{
lean_object* v_unused_4149_; 
v_unused_4149_ = lean_ctor_get(v_x_4134_, 0);
lean_dec(v_unused_4149_);
v___x_4138_ = v_x_4134_;
v_isShared_4139_ = v_isSharedCheck_4148_;
goto v_resetjp_4137_;
}
else
{
lean_dec(v_x_4134_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4148_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4140_; lean_object* v___x_4142_; 
v___x_4140_ = lean_st_ref_get(v___y_4132_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 0, v___x_4140_);
v___x_4142_ = v___x_4138_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4140_);
v___x_4142_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; uint8_t v___x_4145_; lean_object* v___x_4146_; 
v___x_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
v___x_4144_ = lean_unsigned_to_nat(0u);
v___x_4145_ = 0;
v___x_4146_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4144_, v___x_4145_, v___x_4143_, v___f_4133_);
return v___x_4146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_4150_, lean_object* v___f_4151_, lean_object* v_x_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_4150_, v___f_4151_, v_x_4152_);
lean_dec(v___y_4150_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4158_; lean_object* v___f_4159_; lean_object* v___f_4160_; lean_object* v___x_4161_; uint8_t v___x_4162_; lean_object* v___x_4163_; 
v___x_4158_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4156_);
lean_inc_n(v___y_4156_, 2);
v___f_4159_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_4159_, 0, v_waiter_4155_);
lean_closure_set(v___f_4159_, 1, v___y_4156_);
v___f_4160_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4160_, 0, v___y_4156_);
lean_closure_set(v___f_4160_, 1, v___f_4159_);
v___x_4161_ = lean_unsigned_to_nat(0u);
v___x_4162_ = 0;
v___x_4163_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4161_, v___x_4162_, v___x_4158_, v___f_4160_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_4164_, v___y_4165_);
lean_dec(v___y_4165_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_4168_, lean_object* v_waiter_4169_){
_start:
{
lean_object* v___f_4171_; lean_object* v___x_4172_; 
v___f_4171_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4171_, 0, v_waiter_4169_);
v___x_4172_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_4168_, v___f_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_4173_, lean_object* v_waiter_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_4173_, v_waiter_4174_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_4177_, lean_object* v___f_4178_, lean_object* v_x_4179_){
_start:
{
if (lean_obj_tag(v_x_4179_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4189_; 
lean_dec_ref(v___f_4178_);
v_a_4181_ = lean_ctor_get(v_x_4179_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_x_4179_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4183_ = v_x_4179_;
v_isShared_4184_ = v_isSharedCheck_4189_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v_x_4179_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4189_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
lean_object* v___x_4187_; 
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
return v___x_4187_;
}
}
}
else
{
lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4201_; 
v_isSharedCheck_4201_ = !lean_is_exclusive(v_x_4179_);
if (v_isSharedCheck_4201_ == 0)
{
lean_object* v_unused_4202_; 
v_unused_4202_ = lean_ctor_get(v_x_4179_, 0);
lean_dec(v_unused_4202_);
v___x_4191_ = v_x_4179_;
v_isShared_4192_ = v_isSharedCheck_4201_;
goto v_resetjp_4190_;
}
else
{
lean_dec(v_x_4179_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4201_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4193_; lean_object* v___x_4195_; 
v___x_4193_ = lean_st_ref_get(v___y_4177_);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 0, v___x_4193_);
v___x_4195_ = v___x_4191_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4193_);
v___x_4195_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; lean_object* v___x_4199_; 
v___x_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
v___x_4197_ = lean_unsigned_to_nat(0u);
v___x_4198_ = 0;
v___x_4199_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4197_, v___x_4198_, v___x_4196_, v___f_4178_);
return v___x_4199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_4203_, lean_object* v___f_4204_, lean_object* v_x_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_4203_, v___f_4204_, v_x_4205_);
lean_dec(v___y_4203_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; lean_object* v___f_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; lean_object* v___x_4215_; 
v___x_4211_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4209_);
lean_inc(v___y_4209_);
v___f_4212_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_4212_, 0, v___y_4209_);
lean_closure_set(v___f_4212_, 1, v___f_4208_);
v___x_4213_ = lean_unsigned_to_nat(0u);
v___x_4214_ = 0;
v___x_4215_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4213_, v___x_4214_, v___x_4211_, v___f_4212_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_4216_, v___y_4217_);
lean_dec(v___y_4217_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_4223_){
_start:
{
lean_object* v___f_4224_; lean_object* v___f_4225_; lean_object* v___f_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___f_4224_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_4223_, 2);
v___f_4225_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_4225_, 0, v_stream_4223_);
v___f_4226_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_4227_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4227_, 0, lean_box(0));
lean_closure_set(v___x_4227_, 1, lean_box(0));
lean_closure_set(v___x_4227_, 2, v_stream_4223_);
lean_closure_set(v___x_4227_, 3, v___f_4226_);
v___x_4228_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4228_, 0, lean_box(0));
lean_closure_set(v___x_4228_, 1, lean_box(0));
lean_closure_set(v___x_4228_, 2, v_stream_4223_);
lean_closure_set(v___x_4228_, 3, v___f_4224_);
v___x_4229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4227_);
lean_ctor_set(v___x_4229_, 1, v___f_4225_);
lean_ctor_set(v___x_4229_, 2, v___x_4228_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v___x_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v___x_4233_; lean_object* v_pendingProducer_4234_; lean_object* v_pendingConsumer_4235_; lean_object* v_interestWaiter_4236_; uint8_t v_closed_4237_; lean_object* v_pendingIncompleteChunk_4238_; lean_object* v_closeError_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4248_; 
v___x_4233_ = lean_st_ref_take(v___y_4231_);
v_pendingProducer_4234_ = lean_ctor_get(v___x_4233_, 0);
v_pendingConsumer_4235_ = lean_ctor_get(v___x_4233_, 1);
v_interestWaiter_4236_ = lean_ctor_get(v___x_4233_, 2);
v_closed_4237_ = lean_ctor_get_uint8(v___x_4233_, sizeof(void*)*6);
v_pendingIncompleteChunk_4238_ = lean_ctor_get(v___x_4233_, 4);
v_closeError_4239_ = lean_ctor_get(v___x_4233_, 5);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4248_ == 0)
{
lean_object* v_unused_4249_; 
v_unused_4249_ = lean_ctor_get(v___x_4233_, 3);
lean_dec(v_unused_4249_);
v___x_4241_ = v___x_4233_;
v_isShared_4242_ = v_isSharedCheck_4248_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_closeError_4239_);
lean_inc(v_pendingIncompleteChunk_4238_);
lean_inc(v_interestWaiter_4236_);
lean_inc(v_pendingConsumer_4235_);
lean_inc(v_pendingProducer_4234_);
lean_dec(v___x_4233_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4248_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 3, v___x_4230_);
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_pendingProducer_4234_);
lean_ctor_set(v_reuseFailAlloc_4247_, 1, v_pendingConsumer_4235_);
lean_ctor_set(v_reuseFailAlloc_4247_, 2, v_interestWaiter_4236_);
lean_ctor_set(v_reuseFailAlloc_4247_, 3, v___x_4230_);
lean_ctor_set(v_reuseFailAlloc_4247_, 4, v_pendingIncompleteChunk_4238_);
lean_ctor_set(v_reuseFailAlloc_4247_, 5, v_closeError_4239_);
lean_ctor_set_uint8(v_reuseFailAlloc_4247_, sizeof(void*)*6, v_closed_4237_);
v___x_4244_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = lean_st_ref_set(v___y_4231_, v___x_4244_);
v___x_4246_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
return v___x_4246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0___boxed(lean_object* v___x_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Std_Http_Body_stream___lam__0(v___x_4250_, v___y_4251_);
lean_dec(v___y_4251_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_x_4254_, lean_object* v_x_4255_){
_start:
{
if (lean_obj_tag(v_x_4255_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4265_; 
lean_dec_ref(v_x_4254_);
v_a_4257_ = lean_ctor_get(v_x_4255_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v_x_4255_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4259_ = v_x_4255_;
v_isShared_4260_ = v_isSharedCheck_4265_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v_x_4255_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4265_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4262_);
return v___x_4263_;
}
}
}
else
{
lean_object* v___x_4266_; 
lean_dec_ref_known(v_x_4255_, 1);
v___x_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4266_, 0, v_x_4254_);
return v___x_4266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_x_4267_, lean_object* v_x_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Std_Http_Body_stream___lam__1(v_x_4267_, v_x_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v_a_4271_, lean_object* v_x_4272_){
_start:
{
if (lean_obj_tag(v_x_4272_) == 0)
{
lean_object* v___x_4274_; 
lean_dec_ref(v_a_4271_);
v___x_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4274_, 0, v_x_4272_);
return v___x_4274_;
}
else
{
lean_object* v___x_4275_; 
lean_dec_ref_known(v_x_4272_, 1);
v___x_4275_ = l_Std_Http_Body_Stream_close(v_a_4271_);
return v___x_4275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v_a_4276_, lean_object* v_x_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Std_Http_Body_stream___lam__2(v_a_4276_, v_x_4277_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_a_4280_, lean_object* v_x_4281_){
_start:
{
if (lean_obj_tag(v_x_4281_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4284_; 
v_a_4283_ = lean_ctor_get(v_x_4281_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v_x_4281_, 1);
v___x_4284_ = l_Std_Http_Body_Stream_closeWithError(v_a_4280_, v_a_4283_);
return v___x_4284_;
}
else
{
lean_object* v___x_4285_; 
lean_dec_ref(v_a_4280_);
v___x_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4285_, 0, v_x_4281_);
return v___x_4285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_a_4286_, lean_object* v_x_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Std_Http_Body_stream___lam__3(v_a_4286_, v_x_4287_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_4290_, lean_object* v_a_4291_, lean_object* v___x_4292_, lean_object* v___f_4293_, lean_object* v___f_4294_){
_start:
{
lean_object* v___x_4296_; uint8_t v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4296_ = lean_apply_2(v_gen_4290_, v_a_4291_, lean_box(0));
v___x_4297_ = 0;
lean_inc(v___x_4292_);
v___x_4298_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4292_, v___x_4297_, v___x_4296_, v___f_4293_);
v___x_4299_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4292_, v___x_4297_, v___x_4298_, v___f_4294_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_4300_, lean_object* v_a_4301_, lean_object* v___x_4302_, lean_object* v___f_4303_, lean_object* v___f_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Std_Http_Body_stream___lam__4(v_gen_4300_, v_a_4301_, v___x_4302_, v___f_4303_, v___f_4304_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5(lean_object* v_gen_4307_, lean_object* v_a_4308_, lean_object* v___f_4309_, lean_object* v___f_4310_, lean_object* v___f_4311_, lean_object* v_x_4312_){
_start:
{
if (lean_obj_tag(v_x_4312_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4322_; 
lean_dec_ref(v___f_4311_);
lean_dec_ref(v___f_4310_);
lean_dec_ref(v___f_4309_);
lean_dec_ref(v_a_4308_);
lean_dec_ref(v_gen_4307_);
v_a_4314_ = lean_ctor_get(v_x_4312_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v_x_4312_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4316_ = v_x_4312_;
v_isShared_4317_ = v_isSharedCheck_4322_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v_x_4312_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4322_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; 
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
}
}
else
{
lean_object* v___x_4323_; lean_object* v___f_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; lean_object* v___x_4328_; 
lean_dec_ref_known(v_x_4312_, 1);
v___x_4323_ = lean_unsigned_to_nat(0u);
v___f_4324_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 6, 5);
lean_closure_set(v___f_4324_, 0, v_gen_4307_);
lean_closure_set(v___f_4324_, 1, v_a_4308_);
lean_closure_set(v___f_4324_, 2, v___x_4323_);
lean_closure_set(v___f_4324_, 3, v___f_4309_);
lean_closure_set(v___f_4324_, 4, v___f_4310_);
v___x_4325_ = lean_io_as_task(v___f_4324_, v___x_4323_);
lean_dec_ref(v___x_4325_);
v___x_4326_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
v___x_4327_ = 0;
v___x_4328_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4323_, v___x_4327_, v___x_4326_, v___f_4311_);
return v___x_4328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object* v_gen_4329_, lean_object* v_a_4330_, lean_object* v___f_4331_, lean_object* v___f_4332_, lean_object* v___f_4333_, lean_object* v_x_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Std_Http_Body_stream___lam__5(v_gen_4329_, v_a_4330_, v___f_4331_, v___f_4332_, v___f_4333_, v_x_4334_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6(lean_object* v_gen_4341_, lean_object* v_x_4342_){
_start:
{
if (lean_obj_tag(v_x_4342_) == 0)
{
lean_object* v___x_4344_; 
lean_dec_ref(v_gen_4341_);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v_x_4342_);
return v___x_4344_;
}
else
{
lean_object* v_a_4345_; lean_object* v___f_4346_; lean_object* v___x_4347_; lean_object* v___f_4348_; lean_object* v___f_4349_; lean_object* v___f_4350_; lean_object* v___f_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; lean_object* v___x_4354_; 
v_a_4345_ = lean_ctor_get(v_x_4342_, 0);
lean_inc_n(v_a_4345_, 4);
v___f_4346_ = ((lean_object*)(l_Std_Http_Body_stream___lam__6___closed__1));
v___x_4347_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4345_, v___f_4346_);
v___f_4348_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4348_, 0, v_x_4342_);
v___f_4349_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4349_, 0, v_a_4345_);
v___f_4350_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4350_, 0, v_a_4345_);
v___f_4351_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__5___boxed), 7, 5);
lean_closure_set(v___f_4351_, 0, v_gen_4341_);
lean_closure_set(v___f_4351_, 1, v_a_4345_);
lean_closure_set(v___f_4351_, 2, v___f_4349_);
lean_closure_set(v___f_4351_, 3, v___f_4350_);
lean_closure_set(v___f_4351_, 4, v___f_4348_);
v___x_4352_ = lean_unsigned_to_nat(0u);
v___x_4353_ = 0;
v___x_4354_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4352_, v___x_4353_, v___x_4347_, v___f_4351_);
return v___x_4354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object* v_gen_4355_, lean_object* v_x_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Std_Http_Body_stream___lam__6(v_gen_4355_, v_x_4356_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object* v_gen_4359_){
_start:
{
lean_object* v___x_4361_; lean_object* v___f_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; lean_object* v___x_4365_; 
v___x_4361_ = l_Std_Http_Body_mkStream();
v___f_4362_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4362_, 0, v_gen_4359_);
v___x_4363_ = lean_unsigned_to_nat(0u);
v___x_4364_ = 0;
v___x_4365_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4363_, v___x_4364_, v___x_4361_, v___f_4362_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l_Std_Http_Body_stream(v_gen_4366_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1(lean_object* v___x_4369_, lean_object* v_content_4370_, lean_object* v_s_4371_, lean_object* v_x_4372_){
_start:
{
if (lean_obj_tag(v_x_4372_) == 0)
{
lean_object* v___x_4374_; 
lean_dec_ref(v_s_4371_);
lean_dec_ref(v_content_4370_);
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v_x_4372_);
return v___x_4374_;
}
else
{
lean_object* v___x_4375_; uint8_t v___x_4376_; 
lean_dec_ref_known(v_x_4372_, 1);
v___x_4375_ = lean_unsigned_to_nat(0u);
v___x_4376_ = lean_nat_dec_lt(v___x_4375_, v___x_4369_);
if (v___x_4376_ == 0)
{
lean_object* v___x_4377_; 
lean_dec_ref(v_s_4371_);
lean_dec_ref(v_content_4370_);
v___x_4377_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___closed__1));
return v___x_4377_;
}
else
{
lean_object* v___x_4378_; uint8_t v___x_4379_; lean_object* v___x_4380_; 
v___x_4378_ = l_Std_Http_Chunk_ofByteArray(v_content_4370_);
v___x_4379_ = 0;
v___x_4380_ = l_Std_Http_Body_Stream_send(v_s_4371_, v___x_4378_, v___x_4379_);
return v___x_4380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1___boxed(lean_object* v___x_4381_, lean_object* v_content_4382_, lean_object* v_s_4383_, lean_object* v_x_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Std_Http_Body_fromBytes___lam__1(v___x_4381_, v_content_4382_, v_s_4383_, v_x_4384_);
lean_dec(v___x_4381_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v_content_4387_, lean_object* v_s_4388_){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___f_4393_; lean_object* v___x_4394_; lean_object* v___f_4395_; lean_object* v___x_4396_; uint8_t v___x_4397_; lean_object* v___x_4398_; 
v___x_4390_ = lean_byte_array_size(v_content_4387_);
v___x_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4391_);
v___f_4393_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4393_, 0, v___x_4392_);
lean_inc_ref(v_s_4388_);
v___x_4394_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_4388_, v___f_4393_);
v___f_4395_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4395_, 0, v___x_4390_);
lean_closure_set(v___f_4395_, 1, v_content_4387_);
lean_closure_set(v___f_4395_, 2, v_s_4388_);
v___x_4396_ = lean_unsigned_to_nat(0u);
v___x_4397_ = 0;
v___x_4398_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4396_, v___x_4397_, v___x_4394_, v___f_4395_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v_content_4399_, lean_object* v_s_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Std_Http_Body_fromBytes___lam__0(v_content_4399_, v_s_4400_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_4403_){
_start:
{
lean_object* v___f_4405_; lean_object* v___x_4406_; 
v___f_4405_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4405_, 0, v_content_4403_);
v___x_4406_ = l_Std_Http_Body_stream(v___f_4405_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Std_Http_Body_fromBytes(v_content_4407_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_a_4410_, lean_object* v___f_4411_, lean_object* v_x_4412_){
_start:
{
if (lean_obj_tag(v_x_4412_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4422_; 
lean_dec_ref(v___f_4411_);
lean_dec_ref(v_a_4410_);
v_a_4414_ = lean_ctor_get(v_x_4412_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v_x_4412_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4416_ = v_x_4412_;
v_isShared_4417_ = v_isSharedCheck_4422_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v_x_4412_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4422_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4414_);
v___x_4419_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
return v___x_4420_;
}
}
}
else
{
lean_object* v___x_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; lean_object* v___x_4426_; 
lean_dec_ref_known(v_x_4412_, 1);
v___x_4423_ = l_Std_Http_Body_Stream_close(v_a_4410_);
v___x_4424_ = lean_unsigned_to_nat(0u);
v___x_4425_ = 0;
v___x_4426_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4424_, v___x_4425_, v___x_4423_, v___f_4411_);
return v___x_4426_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_a_4427_, lean_object* v___f_4428_, lean_object* v_x_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Std_Http_Body_empty___lam__2(v_a_4427_, v___f_4428_, v_x_4429_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0(lean_object* v_x_4438_){
_start:
{
if (lean_obj_tag(v_x_4438_) == 0)
{
lean_object* v___x_4440_; 
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v_x_4438_);
return v___x_4440_;
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4442_; lean_object* v___f_4443_; lean_object* v___x_4444_; lean_object* v___f_4445_; lean_object* v___f_4446_; uint8_t v___x_4447_; lean_object* v___x_4448_; 
v_a_4441_ = lean_ctor_get(v_x_4438_, 0);
lean_inc_n(v_a_4441_, 2);
v___x_4442_ = lean_unsigned_to_nat(0u);
v___f_4443_ = ((lean_object*)(l_Std_Http_Body_empty___lam__0___closed__2));
v___x_4444_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4441_, v___f_4443_);
v___f_4445_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4445_, 0, v_x_4438_);
v___f_4446_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4446_, 0, v_a_4441_);
lean_closure_set(v___f_4446_, 1, v___f_4445_);
v___x_4447_ = 0;
v___x_4448_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4442_, v___x_4447_, v___x_4444_, v___f_4446_);
return v___x_4448_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0___boxed(lean_object* v_x_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Std_Http_Body_empty___lam__0(v_x_4449_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___x_4454_; lean_object* v___f_4455_; lean_object* v___x_4456_; uint8_t v___x_4457_; lean_object* v___x_4458_; 
v___x_4454_ = l_Std_Http_Body_mkStream();
v___f_4455_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_4456_ = lean_unsigned_to_nat(0u);
v___x_4457_ = 0;
v___x_4458_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4456_, v___x_4457_, v___x_4454_, v___f_4455_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Std_Http_Body_empty();
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_4483_, lean_object* v_f_4484_){
_start:
{
lean_object* v_line_4485_; lean_object* v_body_4486_; lean_object* v_extensions_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4495_; 
v_line_4485_ = lean_ctor_get(v_f_4484_, 0);
v_body_4486_ = lean_ctor_get(v_f_4484_, 1);
v_extensions_4487_ = lean_ctor_get(v_f_4484_, 2);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_f_4484_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4489_ = v_f_4484_;
v_isShared_4490_ = v_isSharedCheck_4495_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_extensions_4487_);
lean_inc(v_body_4486_);
lean_inc(v_line_4485_);
lean_dec(v_f_4484_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4495_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4491_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4483_, v_body_4486_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 1, v___x_4491_);
v___x_4493_ = v___x_4489_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_line_4485_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v___x_4491_);
lean_ctor_set(v_reuseFailAlloc_4494_, 2, v_extensions_4487_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_4499_, lean_object* v_x_4500_){
_start:
{
if (lean_obj_tag(v_x_4500_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4510_; 
lean_dec_ref(v___x_4499_);
v_a_4502_ = lean_ctor_get(v_x_4500_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v_x_4500_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4504_ = v_x_4500_;
v_isShared_4505_ = v_isSharedCheck_4510_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v_x_4500_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4510_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4508_; 
v___x_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4507_);
return v___x_4508_;
}
}
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4530_; 
v_a_4511_ = lean_ctor_get(v_x_4500_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v_x_4500_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4513_ = v_x_4500_;
v_isShared_4514_ = v_isSharedCheck_4530_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v_x_4500_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4530_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v_line_4515_; lean_object* v_body_4516_; lean_object* v_extensions_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4529_; 
v_line_4515_ = lean_ctor_get(v_a_4511_, 0);
v_body_4516_ = lean_ctor_get(v_a_4511_, 1);
v_extensions_4517_ = lean_ctor_get(v_a_4511_, 2);
v_isSharedCheck_4529_ = !lean_is_exclusive(v_a_4511_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4519_ = v_a_4511_;
v_isShared_4520_ = v_isSharedCheck_4529_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_extensions_4517_);
lean_inc(v_body_4516_);
lean_inc(v_line_4515_);
lean_dec(v_a_4511_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4529_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4521_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4499_, v_body_4516_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 1, v___x_4521_);
v___x_4523_ = v___x_4519_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_line_4515_);
lean_ctor_set(v_reuseFailAlloc_4528_, 1, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4528_, 2, v_extensions_4517_);
v___x_4523_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4525_; 
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v___x_4523_);
v___x_4525_ = v___x_4513_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4523_);
v___x_4525_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
lean_object* v___x_4526_; 
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
return v___x_4526_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_4531_, lean_object* v_x_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_4531_, v_x_4532_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_4535_, lean_object* v_action_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; lean_object* v___x_4542_; 
lean_inc_ref(v___y_4537_);
v___x_4539_ = lean_apply_2(v_action_4536_, v___y_4537_, lean_box(0));
v___x_4540_ = lean_unsigned_to_nat(0u);
v___x_4541_ = 0;
v___x_4542_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4540_, v___x_4541_, v___x_4539_, v___f_4535_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_4543_, lean_object* v_action_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_4543_, v_action_4544_, v___y_4545_);
lean_dec_ref(v___y_4545_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_4553_, lean_object* v_action_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; uint8_t v___x_4559_; lean_object* v___x_4560_; 
v___x_4557_ = lean_apply_1(v_action_4554_, lean_box(0));
v___x_4558_ = lean_unsigned_to_nat(0u);
v___x_4559_ = 0;
v___x_4560_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4558_, v___x_4559_, v___x_4557_, v___f_4553_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_4561_, lean_object* v_action_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_4561_, v_action_4562_, v___y_4563_);
lean_dec_ref(v___y_4563_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_4569_, lean_object* v_x_4570_){
_start:
{
if (lean_obj_tag(v_x_4570_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4580_; 
v_a_4572_ = lean_ctor_get(v_x_4570_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v_x_4570_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4574_ = v_x_4570_;
v_isShared_4575_ = v_isSharedCheck_4580_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v_x_4570_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4580_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
lean_object* v___x_4578_; 
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
return v___x_4578_;
}
}
}
else
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4590_; 
v_a_4581_ = lean_ctor_get(v_x_4570_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v_x_4570_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4583_ = v_x_4570_;
v_isShared_4584_ = v_isSharedCheck_4590_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v_x_4570_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4590_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4585_; lean_object* v___x_4587_; 
v___x_4585_ = l_Std_Http_Request_Builder_body___redArg(v_builder_4569_, v_a_4581_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4585_);
v___x_4587_ = v___x_4583_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4585_);
v___x_4587_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4588_; 
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
return v___x_4588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_4591_, lean_object* v_x_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_4591_, v_x_4592_);
lean_dec_ref(v_builder_4591_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_4595_, lean_object* v_gen_4596_){
_start:
{
lean_object* v___x_4598_; lean_object* v___f_4599_; lean_object* v___x_4600_; uint8_t v___x_4601_; lean_object* v___x_4602_; 
v___x_4598_ = l_Std_Http_Body_stream(v_gen_4596_);
v___f_4599_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4599_, 0, v_builder_4595_);
v___x_4600_ = lean_unsigned_to_nat(0u);
v___x_4601_ = 0;
v___x_4602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4600_, v___x_4601_, v___x_4598_, v___f_4599_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_4603_, lean_object* v_gen_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Std_Http_Request_Builder_stream(v_builder_4603_, v_gen_4604_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_4607_, lean_object* v_x_4608_){
_start:
{
if (lean_obj_tag(v_x_4608_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4618_; 
v_a_4610_ = lean_ctor_get(v_x_4608_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v_x_4608_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4612_ = v_x_4608_;
v_isShared_4613_ = v_isSharedCheck_4618_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v_x_4608_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4618_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4616_; 
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
return v___x_4616_;
}
}
}
else
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4628_; 
v_a_4619_ = lean_ctor_get(v_x_4608_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_x_4608_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4621_ = v_x_4608_;
v_isShared_4622_ = v_isSharedCheck_4628_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v_x_4608_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4628_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4623_; lean_object* v___x_4625_; 
v___x_4623_ = l_Std_Http_Response_Builder_body___redArg(v_builder_4607_, v_a_4619_);
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 0, v___x_4623_);
v___x_4625_ = v___x_4621_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_object* v___x_4626_; 
v___x_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
return v___x_4626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_4629_, lean_object* v_x_4630_, lean_object* v___y_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_4629_, v_x_4630_);
lean_dec_ref(v_builder_4629_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_4633_, lean_object* v_gen_4634_){
_start:
{
lean_object* v___x_4636_; lean_object* v___f_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; lean_object* v___x_4640_; 
v___x_4636_ = l_Std_Http_Body_stream(v_gen_4634_);
v___f_4637_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4637_, 0, v_builder_4633_);
v___x_4638_ = lean_unsigned_to_nat(0u);
v___x_4639_ = 0;
v___x_4640_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4638_, v___x_4639_, v___x_4636_, v___f_4637_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_4641_, lean_object* v_gen_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Std_Http_Response_Builder_stream(v_builder_4641_, v_gen_4642_);
return v_res_4644_;
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

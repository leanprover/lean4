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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Body_mkStream___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_mkStream___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_mkStream___closed__0 = (const lean_object*)&l_Std_Http_Body_mkStream___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_mkStream___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 8, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__4 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__4_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__4_value),((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__3_value)} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__5 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__5_value;
static lean_once_cell_t l_Std_Http_Body_Stream_isClosed___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_isClosed___closed__6;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_stream___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_stream___lam__6___closed__0 = (const lean_object*)&l_Std_Http_Body_stream___lam__6___closed__0_value;
static const lean_closure_object l_Std_Http_Body_stream___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_stream___lam__5___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_stream___lam__6___closed__0_value)} };
static const lean_object* l_Std_Http_Body_stream___lam__6___closed__1 = (const lean_object*)&l_Std_Http_Body_stream___lam__6___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_empty___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_empty___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Body_empty___lam__2___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_empty___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_empty___lam__2___closed__0_value)}};
static const lean_object* l_Std_Http_Body_empty___lam__2___closed__1 = (const lean_object*)&l_Std_Http_Body_empty___lam__2___closed__1_value;
static const lean_closure_object l_Std_Http_Body_empty___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_stream___lam__5___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_empty___lam__2___closed__1_value)} };
static const lean_object* l_Std_Http_Body_empty___lam__2___closed__2 = (const lean_object*)&l_Std_Http_Body_empty___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_empty___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
uint8_t v___x_386__boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v___x_386__boxed_68_ = lean_unbox(v___x_66_);
v_res_69_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(v___x_386__boxed_68_);
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
lean_object* v___f_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___f_165_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__0));
v___x_166_ = 0;
v___x_167_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__1));
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = l_Std_Mutex_new___redArg(v___x_167_);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
v___x_172_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_168_, v___x_166_, v___x_171_, v___f_165_);
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
uint8_t v___x_635__boxed_710_; lean_object* v_res_711_; 
v___x_635__boxed_710_ = lean_unbox(v___x_704_);
v_res_711_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(v___x_635__boxed_710_, v_knownSize_705_, v_closeError_706_, v_inst_707_, v_____r_708_, v___y_709_);
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
lean_object* v___x_937_; lean_object* v___x_939_; 
lean_dec_ref(v___f_920_);
v___x_937_ = lean_unsigned_to_nat(0u);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v_interestWaiter_918_);
v___x_939_ = v___x_934_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_interestWaiter_918_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; uint8_t v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
v___x_941_ = lean_unbox(v_a_932_);
lean_dec(v_a_932_);
v___x_942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_937_, v___x_941_, v___x_940_, v___f_919_);
return v___x_942_;
}
}
else
{
lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_del_object(v___x_934_);
lean_dec(v_a_932_);
lean_dec_ref(v___f_919_);
lean_dec(v_interestWaiter_918_);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = 0;
v___x_946_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1));
v___x_947_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_944_, v___x_945_, v___x_946_, v___f_920_);
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
lean_object* v___f_966_; lean_object* v___x_967_; uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_inc(v___y_962_);
v___f_966_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_966_, 0, v___f_965_);
lean_closure_set(v___f_966_, 1, v___y_962_);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = 0;
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v_interestWaiter_960_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___x_971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_967_, v___x_968_, v___x_970_, v___f_966_);
return v___x_971_;
}
else
{
lean_object* v_val_972_; lean_object* v_finished_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_val_972_ = lean_ctor_get(v_interestWaiter_960_, 0);
v_finished_973_ = lean_ctor_get(v_val_972_, 0);
lean_inc(v_finished_973_);
lean_inc(v___y_962_);
v___f_974_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_974_, 0, v___f_965_);
lean_closure_set(v___f_974_, 1, v___y_962_);
lean_inc_ref(v___f_974_);
v___f_975_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed), 5, 3);
lean_closure_set(v___f_975_, 0, v_interestWaiter_960_);
lean_closure_set(v___f_975_, 1, v___f_974_);
lean_closure_set(v___f_975_, 2, v___f_974_);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = 0;
v___x_978_ = lean_st_ref_get(v_finished_973_);
lean_dec(v_finished_973_);
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
v___x_981_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_976_, v___x_977_, v___x_980_, v___f_975_);
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
lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_dec_ref(v___f_1039_);
v___x_1056_ = lean_unsigned_to_nat(0u);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v_pendingConsumer_1037_);
v___x_1058_ = v___x_1053_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_pendingConsumer_1037_);
v___x_1058_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
v___x_1060_ = lean_unbox(v_a_1051_);
lean_dec(v_a_1051_);
v___x_1061_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1056_, v___x_1060_, v___x_1059_, v___f_1038_);
return v___x_1061_;
}
}
else
{
lean_object* v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_del_object(v___x_1053_);
lean_dec(v_a_1051_);
lean_dec_ref(v___f_1038_);
lean_dec(v_pendingConsumer_1037_);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = 0;
v___x_1065_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1));
v___x_1066_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1063_, v___x_1064_, v___x_1065_, v___f_1039_);
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
lean_object* v_finished_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v_finished_1114_ = lean_ctor_get(v_finished_1110_, 0);
lean_inc(v_finished_1114_);
lean_dec_ref(v_finished_1110_);
lean_inc(v_a_1074_);
v___f_1115_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1115_, 0, v___f_1098_);
lean_closure_set(v___f_1115_, 1, v_a_1074_);
lean_inc_ref(v___f_1115_);
v___f_1116_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1116_, 0, v_pendingConsumer_1091_);
lean_closure_set(v___f_1116_, 1, v___f_1115_);
lean_closure_set(v___f_1116_, 2, v___f_1115_);
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = 0;
v___x_1119_ = lean_st_ref_get(v_finished_1114_);
lean_dec(v_finished_1114_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1119_);
v___x_1121_ = v___x_1112_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
v___x_1123_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1117_, v___x_1118_, v___x_1122_, v___f_1116_);
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
lean_object* v___f_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1105_; 
lean_inc(v___y_1100_);
v___f_1101_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1101_, 0, v___f_1098_);
lean_closure_set(v___f_1101_, 1, v___y_1100_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = 0;
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v_pendingConsumer_1091_);
v___x_1105_ = v___x_1088_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_pendingConsumer_1091_);
v___x_1105_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
v___x_1107_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1102_, v___x_1103_, v___x_1106_, v___f_1101_);
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
lean_object* v___f_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc(v_a_1131_);
v___f_1133_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1133_, 0, v_a_1131_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = 0;
v___x_1136_ = lean_st_ref_get(v_a_1131_);
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
v___x_1139_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1134_, v___x_1135_, v___x_1138_, v___f_1133_);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object* v___y_1143_){
_start:
{
if (lean_obj_tag(v___y_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
v_a_1144_ = lean_ctor_get(v___y_1143_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___y_1143_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___y_1143_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___y_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v_a_1152_ = lean_ctor_get(v___y_1143_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___y_1143_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1154_ = v___y_1143_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___y_1143_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_fst_1156_; lean_object* v___x_1158_; 
v_fst_1156_ = lean_ctor_get(v_a_1152_, 0);
lean_inc(v_fst_1156_);
lean_dec(v_a_1152_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v_fst_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_fst_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object* v_mutex_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_io_basemutex_unlock(v_mutex_1161_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(v_mutex_1167_, v_x_1168_);
lean_dec(v_x_1168_);
lean_dec(v_mutex_1167_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object* v_k_1171_, lean_object* v_ref_1172_, lean_object* v_x_1173_){
_start:
{
if (lean_obj_tag(v_x_1173_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_ref_1172_);
lean_dec_ref(v_k_1171_);
v_a_1175_ = lean_ctor_get(v_x_1173_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_x_1173_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v_x_1173_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v_x_1173_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
}
else
{
lean_object* v___x_1184_; 
lean_dec_ref_known(v_x_1173_, 1);
v___x_1184_ = lean_apply_2(v_k_1171_, v_ref_1172_, lean_box(0));
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object* v_k_1185_, lean_object* v_ref_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(v_k_1185_, v_ref_1186_, v_x_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object* v_mutex_1190_, lean_object* v___f_1191_){
_start:
{
lean_object* v___x_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = 0;
v___x_1195_ = lean_io_basemutex_lock(v_mutex_1190_);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
v___x_1198_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1193_, v___x_1194_, v___x_1197_, v___f_1191_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_1199_, lean_object* v___f_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(v_mutex_1199_, v___f_1200_);
lean_dec(v_mutex_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(lean_object* v_mutex_1204_, lean_object* v_k_1205_){
_start:
{
lean_object* v_ref_1207_; lean_object* v_mutex_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___y_1217_; 
v_ref_1207_ = lean_ctor_get(v_mutex_1204_, 0);
lean_inc(v_ref_1207_);
v_mutex_1208_ = lean_ctor_get(v_mutex_1204_, 1);
lean_inc_n(v_mutex_1208_, 2);
lean_dec_ref(v_mutex_1204_);
v___f_1209_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0));
v___f_1210_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1210_, 0, v_mutex_1208_);
v___f_1211_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1211_, 0, v_k_1205_);
lean_closure_set(v___f_1211_, 1, v_ref_1207_);
v___f_1212_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1212_, 0, v_mutex_1208_);
lean_closure_set(v___f_1212_, 1, v___f_1211_);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = 0;
v___x_1215_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1212_, v___f_1210_, v___x_1213_, v___x_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1219_; 
v_a_1219_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1215_, 1);
if (lean_obj_tag(v_a_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_a_1220_ = lean_ctor_get(v_a_1219_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_a_1219_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v_a_1219_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v_a_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v___y_1217_ = v___x_1225_;
goto v___jp_1216_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1236_; 
v_a_1228_ = lean_ctor_get(v_a_1219_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_a_1219_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1230_ = v_a_1219_;
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v_a_1219_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_fst_1232_; lean_object* v___x_1234_; 
v_fst_1232_ = lean_ctor_get(v_a_1228_, 0);
lean_inc(v_fst_1232_);
lean_dec(v_a_1228_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v_fst_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_fst_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
v___y_1217_ = v___x_1234_;
goto v___jp_1216_;
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
v_a_1237_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1239_ = v___x_1215_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1215_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = lean_task_map(v___f_1209_, v_a_1237_, v___x_1213_, v___x_1214_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1243_ = v___x_1239_;
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
v___jp_1216_:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___y_1217_);
return v___x_1218_;
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
lean_object* v___x_1304_; uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = 0;
v___x_1306_ = lean_st_ref_get(v_a_1278_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1306_);
v___x_1308_ = v___x_1302_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
v___x_1310_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1304_, v___x_1305_, v___x_1309_, v___f_1279_);
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
uint8_t v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref_known(v_x_1358_, 1);
v___x_1369_ = 1;
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = 0;
v___x_1372_ = lean_box(v___x_1369_);
v___x_1373_ = lean_io_promise_resolve(v___x_1372_, v_done_1356_);
v___x_1374_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1375_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1370_, v___x_1371_, v___x_1374_, v___f_1357_);
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
lean_object* v_chunk_1433_; lean_object* v_done_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v_chunk_1433_ = lean_ctor_get(v_val_1423_, 0);
lean_inc_ref_n(v_chunk_1433_, 2);
v_done_1434_ = lean_ctor_get(v_val_1423_, 1);
lean_inc(v_done_1434_);
lean_dec(v_val_1423_);
v___x_1435_ = lean_box(0);
v___f_1436_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1436_, 0, v_chunk_1433_);
v___f_1437_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1437_, 0, v_done_1434_);
lean_closure_set(v___f_1437_, 1, v___f_1436_);
v___x_1438_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1427_, v_chunk_1433_);
lean_dec_ref(v_chunk_1433_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 3, v___x_1438_);
lean_ctor_set(v___x_1431_, 0, v___x_1435_);
v___x_1440_ = v___x_1431_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_pendingConsumer_1424_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_interestWaiter_1425_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_pendingIncompleteChunk_1428_);
lean_ctor_set(v_reuseFailAlloc_1446_, 5, v_closeError_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, sizeof(void*)*6, v_closed_1426_);
v___x_1440_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = 0;
v___x_1443_ = lean_st_ref_swap(v_a_1409_, v___x_1440_);
lean_dec(v___x_1443_);
v___x_1444_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1441_, v___x_1442_, v___x_1444_, v___f_1437_);
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
lean_object* v___f_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_inc(v_a_1454_);
v___f_1456_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1456_, 0, v_a_1454_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = 0;
v___x_1459_ = lean_st_ref_get(v_a_1454_);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
v___x_1462_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1457_, v___x_1458_, v___x_1461_, v___f_1456_);
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
lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___f_1469_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0));
lean_inc(v_a_1467_);
v___f_1470_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1470_, 0, v_a_1467_);
lean_closure_set(v___f_1470_, 1, v___f_1469_);
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = 0;
v___x_1473_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1467_);
v___x_1474_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1471_, v___x_1472_, v___x_1473_, v___f_1470_);
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
lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec_ref_known(v_x_1480_, 1);
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = 0;
v___x_1493_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1478_);
v___x_1494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1491_, v___x_1492_, v___x_1493_, v___f_1479_);
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
lean_object* v___f_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_inc(v___y_1501_);
v___f_1503_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecv___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1503_, 0, v___y_1501_);
lean_closure_set(v___f_1503_, 1, v___f_1500_);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = 0;
v___x_1506_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1501_);
v___x_1507_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1504_, v___x_1505_, v___x_1506_, v___f_1503_);
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
lean_object* v___f_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___f_1548_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0));
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = 0;
v___x_1551_ = lean_st_ref_get(v_a_1546_);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
v___x_1554_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1549_, v___x_1550_, v___x_1553_, v___f_1548_);
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
lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = 0;
v___x_1614_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1596_);
v___x_1615_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1612_, v___x_1613_, v___x_1614_, v___f_1597_);
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
lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref_known(v_x_1623_, 1);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = 0;
v___x_1636_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_1621_);
v___x_1637_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1634_, v___x_1635_, v___x_1636_, v___f_1622_);
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
lean_object* v___f_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_inc_n(v___y_1644_, 2);
v___f_1646_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1646_, 0, v___y_1644_);
lean_closure_set(v___f_1646_, 1, v___f_1643_);
v___f_1647_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1647_, 0, v___y_1644_);
lean_closure_set(v___f_1647_, 1, v___f_1646_);
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = 0;
v___x_1650_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1644_);
v___x_1651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1648_, v___x_1649_, v___x_1650_, v___f_1647_);
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
v___x_1685_ = lean_box(0);
v___x_1686_ = lean_st_ref_swap(v___y_1682_, v___x_1684_);
lean_dec(v___x_1686_);
return v___x_1685_;
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
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_st_ref_swap(v_a_1744_, v___x_1762_);
lean_dec(v___x_1764_);
return v___x_1763_;
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
uint8_t v___x_1821_; lean_object* v___x_1822_; 
lean_dec(v___x_1819_);
v___x_1821_ = 1;
v___x_1822_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_1816_);
if (lean_obj_tag(v___x_1822_) == 1)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref(v___f_1815_);
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
v___x_1824_ = lean_task_pure(v___x_1823_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; lean_object* v_pendingConsumer_1826_; 
lean_dec(v___x_1822_);
v___x_1825_ = lean_st_ref_get(v___y_1816_);
v_pendingConsumer_1826_ = lean_ctor_get(v___x_1825_, 1);
lean_inc(v_pendingConsumer_1826_);
if (lean_obj_tag(v_pendingConsumer_1826_) == 0)
{
lean_object* v_pendingProducer_1827_; lean_object* v_interestWaiter_1828_; uint8_t v_closed_1829_; lean_object* v_knownSize_1830_; lean_object* v_pendingIncompleteChunk_1831_; lean_object* v_closeError_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1847_; 
v_pendingProducer_1827_ = lean_ctor_get(v___x_1825_, 0);
v_interestWaiter_1828_ = lean_ctor_get(v___x_1825_, 2);
v_closed_1829_ = lean_ctor_get_uint8(v___x_1825_, sizeof(void*)*6);
v_knownSize_1830_ = lean_ctor_get(v___x_1825_, 3);
v_pendingIncompleteChunk_1831_ = lean_ctor_get(v___x_1825_, 4);
v_closeError_1832_ = lean_ctor_get(v___x_1825_, 5);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v___x_1825_, 1);
lean_dec(v_unused_1848_);
v___x_1834_ = v___x_1825_;
v_isShared_1835_ = v_isSharedCheck_1847_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_closeError_1832_);
lean_inc(v_pendingIncompleteChunk_1831_);
lean_inc(v_knownSize_1830_);
lean_inc(v_interestWaiter_1828_);
lean_inc(v_pendingProducer_1827_);
lean_dec(v___x_1825_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1847_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1836_ = lean_io_promise_new();
lean_inc(v___x_1836_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1838_);
v___x_1840_ = v___x_1834_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_pendingProducer_1827_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_interestWaiter_1828_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_knownSize_1830_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_pendingIncompleteChunk_1831_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v_closeError_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1846_, sizeof(void*)*6, v_closed_1829_);
v___x_1840_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1841_ = lean_st_ref_swap(v___y_1816_, v___x_1840_);
lean_dec(v___x_1841_);
v___x_1842_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_1816_);
v___x_1843_ = lean_io_promise_result_opt(v___x_1836_);
lean_dec(v___x_1836_);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_task_map(v___f_1815_, v___x_1843_, v___x_1844_, v___x_1821_);
return v___x_1845_;
}
}
}
else
{
lean_object* v___x_1849_; 
lean_dec_ref_known(v_pendingConsumer_1826_, 1);
lean_dec(v___x_1825_);
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
lean_object* v___f_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___f_1894_ = ((lean_object*)(l_Std_Http_Body_Stream_recv___closed__0));
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = 0;
v___x_1897_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1892_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
v___x_1900_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1895_, v___x_1896_, v___x_1899_, v___f_1894_);
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
uint8_t v___x_2195__boxed_1920_; lean_object* v_res_1921_; 
v___x_2195__boxed_1920_ = lean_unbox(v___x_1914_);
v_res_1921_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(v___x_2195__boxed_1920_, v_knownSize_1915_, v_closeError_1916_, v_____r_1917_, v___y_1918_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object* v_pendingProducer_1934_, lean_object* v___f_1935_, uint8_t v_closed_1936_, lean_object* v_____r_1937_, lean_object* v___y_1938_){
_start:
{
if (lean_obj_tag(v_pendingProducer_1934_) == 1)
{
lean_object* v_val_1940_; lean_object* v_done_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_val_1940_ = lean_ctor_get(v_pendingProducer_1934_, 0);
v_done_1941_ = lean_ctor_get(v_val_1940_, 1);
lean_inc(v___y_1938_);
v___f_1942_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1942_, 0, v___f_1935_);
lean_closure_set(v___f_1942_, 1, v___y_1938_);
v___x_1943_ = lean_unsigned_to_nat(0u);
v___x_1944_ = lean_box(v_closed_1936_);
v___x_1945_ = lean_io_promise_resolve(v___x_1944_, v_done_1941_);
v___x_1946_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1947_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1943_, v_closed_1936_, v___x_1946_, v___f_1942_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_box(0);
lean_inc(v___y_1938_);
v___x_1949_ = lean_apply_3(v___f_1935_, v___x_1948_, v___y_1938_, lean_box(0));
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object* v_pendingProducer_1950_, lean_object* v___f_1951_, lean_object* v_closed_1952_, lean_object* v_____r_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
uint8_t v_closed_boxed_1956_; lean_object* v_res_1957_; 
v_closed_boxed_1956_ = lean_unbox(v_closed_1952_);
v_res_1957_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(v_pendingProducer_1950_, v___f_1951_, v_closed_boxed_1956_, v_____r_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec(v_pendingProducer_1950_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object* v_interestWaiter_1958_, lean_object* v___f_1959_, uint8_t v_closed_1960_, lean_object* v_____r_1961_, lean_object* v___y_1962_){
_start:
{
if (lean_obj_tag(v_interestWaiter_1958_) == 1)
{
lean_object* v_val_1964_; lean_object* v___f_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_val_1964_ = lean_ctor_get(v_interestWaiter_1958_, 0);
lean_inc(v___y_1962_);
v___f_1965_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1965_, 0, v___f_1959_);
lean_closure_set(v___f_1965_, 1, v___y_1962_);
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1964_, v_closed_1960_);
v___x_1968_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1969_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1966_, v_closed_1960_, v___x_1968_, v___f_1965_);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_box(0);
lean_inc(v___y_1962_);
v___x_1971_ = lean_apply_3(v___f_1959_, v___x_1970_, v___y_1962_, lean_box(0));
return v___x_1971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(lean_object* v_interestWaiter_1972_, lean_object* v___f_1973_, lean_object* v_closed_1974_, lean_object* v_____r_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v_closed_boxed_1978_; lean_object* v_res_1979_; 
v_closed_boxed_1978_ = lean_unbox(v_closed_1974_);
v_res_1979_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_1972_, v___f_1973_, v_closed_boxed_1978_, v_____r_1975_, v___y_1976_);
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
lean_closure_set(v___f_2018_, 1, v___f_2016_);
lean_closure_set(v___f_2018_, 2, v___x_2017_);
v___x_2019_ = lean_box(v_closed_2008_);
lean_inc_ref(v___f_2018_);
v___f_2020_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2020_, 0, v_interestWaiter_2011_);
lean_closure_set(v___f_2020_, 1, v___f_2018_);
lean_closure_set(v___f_2020_, 2, v___x_2019_);
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
lean_object* v___x_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_2021_, v___y_2024_);
lean_dec(v_val_2021_);
v___x_2027_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2028_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2025_, v_closed_2008_, v___x_2027_, v___f_2022_);
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
v___x_2035_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_2011_, v___f_2018_, v_closed_2008_, v___x_2034_, v_a_1992_);
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
lean_object* v___f_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_inc(v_a_2042_);
v___f_2044_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed), 3, 1);
lean_closure_set(v___f_2044_, 0, v_a_2042_);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = 0;
v___x_2047_ = lean_st_ref_get(v_a_2042_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
v___x_2050_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2045_, v___x_2046_, v___x_2049_, v___f_2044_);
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
uint8_t v___x_1415__boxed_2087_; lean_object* v_res_2088_; 
v___x_1415__boxed_2087_ = lean_unbox(v___x_2084_);
v_res_2088_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(v___x_1415__boxed_2087_, v_x_2085_);
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
lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___f_2112_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0));
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v___y_2092_);
v___x_2115_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2113_, v_closed_2110_, v___x_2114_, v___f_2112_);
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
lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = 0;
v___x_2139_ = lean_st_ref_get(v___y_2121_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2139_);
v___x_2141_ = v___x_2135_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
v___x_2143_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2137_, v___x_2138_, v___x_2142_, v___f_2122_);
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
lean_object* v___f_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_inc_n(v___y_2152_, 2);
v___f_2154_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2154_, 0, v___y_2152_);
v___f_2155_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2155_, 0, v___y_2152_);
lean_closure_set(v___f_2155_, 1, v___f_2154_);
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = 0;
v___x_2158_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2152_);
v___x_2159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2156_, v___x_2157_, v___x_2158_, v___f_2155_);
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
lean_object* v___f_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; lean_object* v_fst_2188_; lean_object* v_snd_2189_; lean_object* v_pendingProducer_2194_; lean_object* v_pendingConsumer_2195_; lean_object* v_interestWaiter_2196_; uint8_t v_closed_2197_; lean_object* v_knownSize_2198_; lean_object* v_pendingIncompleteChunk_2199_; lean_object* v_closeError_2200_; lean_object* v___x_2201_; 
lean_inc(v___y_2181_);
v___f_2183_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2183_, 0, v___y_2181_);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = 0;
v___x_2186_ = lean_st_ref_take(v___y_2181_);
v_pendingProducer_2194_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_pendingProducer_2194_);
v_pendingConsumer_2195_ = lean_ctor_get(v___x_2186_, 1);
lean_inc(v_pendingConsumer_2195_);
v_interestWaiter_2196_ = lean_ctor_get(v___x_2186_, 2);
lean_inc(v_interestWaiter_2196_);
v_closed_2197_ = lean_ctor_get_uint8(v___x_2186_, sizeof(void*)*6);
v_knownSize_2198_ = lean_ctor_get(v___x_2186_, 3);
lean_inc(v_knownSize_2198_);
v_pendingIncompleteChunk_2199_ = lean_ctor_get(v___x_2186_, 4);
lean_inc(v_pendingIncompleteChunk_2199_);
v_closeError_2200_ = lean_ctor_get(v___x_2186_, 5);
lean_inc(v_closeError_2200_);
v___x_2201_ = lean_box(0);
if (lean_obj_tag(v_closeError_2200_) == 0)
{
lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2210_ = lean_ctor_get(v___x_2186_, 5);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v___x_2186_, 4);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v___x_2186_, 3);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v___x_2186_, 2);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v___x_2186_, 1);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v___x_2186_, 0);
lean_dec(v_unused_2215_);
v___x_2203_ = v___x_2186_;
v_isShared_2204_ = v_isSharedCheck_2209_;
goto v_resetjp_2202_;
}
else
{
lean_dec(v___x_2186_);
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
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_pendingProducer_2194_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_pendingConsumer_2195_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_interestWaiter_2196_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_knownSize_2198_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_pendingIncompleteChunk_2199_);
lean_ctor_set(v_reuseFailAlloc_2208_, 5, v___x_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2208_, sizeof(void*)*6, v_closed_2197_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
v_fst_2188_ = v___x_2201_;
v_snd_2189_ = v___x_2207_;
goto v___jp_2187_;
}
}
}
else
{
lean_dec_ref_known(v_closeError_2200_, 1);
lean_dec(v_pendingIncompleteChunk_2199_);
lean_dec(v_knownSize_2198_);
lean_dec(v_interestWaiter_2196_);
lean_dec(v_pendingConsumer_2195_);
lean_dec(v_pendingProducer_2194_);
lean_dec(v_err_2180_);
v_fst_2188_ = v___x_2201_;
v_snd_2189_ = v___x_2186_;
goto v___jp_2187_;
}
v___jp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2190_ = lean_st_ref_put(v___y_2181_, v_snd_2189_);
v___x_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_fst_2188_);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
v___x_2193_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2184_, v___x_2185_, v___x_2192_, v___f_2183_);
return v___x_2193_;
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
v___x_2241_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_2241_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__2(void){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
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
lean_object* v___x_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v___x_214__overap_2274_; lean_object* v___x_2275_; 
v___x_2270_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2271_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2272_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2273_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__13, &l_Std_Http_Body_Stream_isClosed___closed__13_once, _init_l_Std_Http_Body_Stream_isClosed___closed__13);
v___x_214__overap_2274_ = l_Std_Mutex_atomically___redArg(v___x_2270_, v___f_2271_, v___f_2272_, v_stream_2268_, v___x_2273_);
v___x_2275_ = lean_apply_1(v___x_214__overap_2274_, lean_box(0));
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
lean_object* v___x_2296_; lean_object* v___f_2297_; lean_object* v___f_2298_; lean_object* v___x_2299_; lean_object* v___x_214__overap_2300_; lean_object* v___x_2301_; 
v___x_2296_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2297_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2298_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2299_ = lean_obj_once(&l_Std_Http_Body_Stream_getKnownSize___closed__1, &l_Std_Http_Body_Stream_getKnownSize___closed__1_once, _init_l_Std_Http_Body_Stream_getKnownSize___closed__1);
v___x_214__overap_2300_ = l_Std_Mutex_atomically___redArg(v___x_2296_, v___f_2297_, v___f_2298_, v_stream_2294_, v___x_2299_);
v___x_2301_ = lean_apply_1(v___x_214__overap_2300_, lean_box(0));
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
lean_object* v___f_2332_; lean_object* v___x_2333_; lean_object* v___f_2334_; lean_object* v___f_2335_; lean_object* v___x_207__overap_2336_; lean_object* v___x_2337_; 
v___f_2332_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2332_, 0, v_size_2330_);
v___x_2333_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2334_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2335_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_207__overap_2336_ = l_Std_Mutex_atomically___redArg(v___x_2333_, v___f_2334_, v___f_2335_, v_stream_2329_, v___f_2332_);
v___x_2337_ = lean_apply_1(v___x_207__overap_2336_, lean_box(0));
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
lean_object* v_pendingProducer_2391_; lean_object* v_pendingConsumer_2392_; uint8_t v_closed_2393_; lean_object* v_knownSize_2394_; lean_object* v_pendingIncompleteChunk_2395_; lean_object* v_closeError_2396_; lean_object* v_val_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; uint8_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
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
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_box(v_closed_2393_);
lean_inc(v_a_2377_);
v___f_2401_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed), 10, 8);
lean_closure_set(v___f_2401_, 0, v_pendingProducer_2391_);
lean_closure_set(v___f_2401_, 1, v_pendingConsumer_2392_);
lean_closure_set(v___f_2401_, 2, v___x_2400_);
lean_closure_set(v___f_2401_, 3, v_knownSize_2394_);
lean_closure_set(v___f_2401_, 4, v_pendingIncompleteChunk_2395_);
lean_closure_set(v___f_2401_, 5, v_closeError_2396_);
lean_closure_set(v___f_2401_, 6, v_a_2377_);
lean_closure_set(v___f_2401_, 7, v___x_2399_);
v___x_2402_ = lean_unsigned_to_nat(0u);
v___x_2403_ = 0;
v___x_2404_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2397_, v___x_2398_);
lean_dec(v_val_2397_);
v___x_2405_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2406_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2402_, v___x_2403_, v___x_2405_, v___f_2401_);
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
lean_object* v___f_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
lean_inc(v_a_2412_);
v___f_2414_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2414_, 0, v_a_2412_);
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = 0;
v___x_2417_ = lean_st_ref_get(v_a_2412_);
v___x_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
v___x_2420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2415_, v___x_2416_, v___x_2419_, v___f_2414_);
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
lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec_ref(v_lose_2450_);
v___x_2467_ = lean_unsigned_to_nat(0u);
v___x_2468_ = 0;
v___x_2469_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2451_);
v___x_2470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2467_, v___x_2468_, v___x_2469_, v___f_2452_);
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
lean_object* v_finished_2481_; lean_object* v_promise_2482_; lean_object* v___f_2483_; lean_object* v___f_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; uint8_t v___y_2489_; uint8_t v___x_2497_; 
v_finished_2481_ = lean_ctor_get(v_w_2477_, 0);
lean_inc(v_finished_2481_);
v_promise_2482_ = lean_ctor_get(v_w_2477_, 1);
lean_inc(v_promise_2482_);
lean_dec_ref(v_w_2477_);
v___f_2483_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2483_, 0, v_promise_2482_);
lean_inc(v___y_2479_);
v___f_2484_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2484_, 0, v_lose_2478_);
lean_closure_set(v___f_2484_, 1, v___y_2479_);
lean_closure_set(v___f_2484_, 2, v___f_2483_);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = 0;
v___x_2487_ = lean_st_ref_take(v_finished_2481_);
v___x_2497_ = lean_unbox(v___x_2487_);
lean_dec(v___x_2487_);
if (v___x_2497_ == 0)
{
uint8_t v___x_2498_; 
v___x_2498_ = 1;
v___y_2489_ = v___x_2498_;
goto v___jp_2488_;
}
else
{
v___y_2489_ = v___x_2486_;
goto v___jp_2488_;
}
v___jp_2488_:
{
uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2490_ = 1;
v___x_2491_ = lean_box(v___x_2490_);
v___x_2492_ = lean_st_ref_put(v_finished_2481_, v___x_2491_);
lean_dec(v_finished_2481_);
v___x_2493_ = lean_box(v___y_2489_);
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
v___x_2496_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2485_, v___x_2486_, v___x_2495_, v___f_2484_);
return v___x_2496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object* v_w_2499_, lean_object* v_lose_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_2499_, v_lose_2500_, v___y_2501_);
lean_dec(v___y_2501_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object* v___y_2504_, lean_object* v_x_2505_){
_start:
{
if (lean_obj_tag(v_x_2505_) == 0)
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_x_2505_);
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; 
lean_dec_ref_known(v_x_2505_, 1);
v___x_2508_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_2504_);
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object* v___y_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_2509_, v_x_2510_);
lean_dec(v___y_2509_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object* v_waiter_2513_, lean_object* v_pendingProducer_2514_, lean_object* v_interestWaiter_2515_, uint8_t v_closed_2516_, lean_object* v_knownSize_2517_, lean_object* v_pendingIncompleteChunk_2518_, lean_object* v_closeError_2519_, uint8_t v_a_2520_, lean_object* v_____r_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___f_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_inc(v___y_2522_);
v___f_2524_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2524_, 0, v___y_2522_);
v___x_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_waiter_2513_);
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2527_, 0, v_pendingProducer_2514_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
lean_ctor_set(v___x_2527_, 2, v_interestWaiter_2515_);
lean_ctor_set(v___x_2527_, 3, v_knownSize_2517_);
lean_ctor_set(v___x_2527_, 4, v_pendingIncompleteChunk_2518_);
lean_ctor_set(v___x_2527_, 5, v_closeError_2519_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*6, v_closed_2516_);
v___x_2528_ = lean_unsigned_to_nat(0u);
v___x_2529_ = lean_st_ref_swap(v___y_2522_, v___x_2527_);
lean_dec(v___x_2529_);
v___x_2530_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2531_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2528_, v_a_2520_, v___x_2530_, v___f_2524_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object* v_waiter_2532_, lean_object* v_pendingProducer_2533_, lean_object* v_interestWaiter_2534_, lean_object* v_closed_2535_, lean_object* v_knownSize_2536_, lean_object* v_pendingIncompleteChunk_2537_, lean_object* v_closeError_2538_, lean_object* v_a_2539_, lean_object* v_____r_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
uint8_t v_closed_boxed_2543_; uint8_t v_a_5670__boxed_2544_; lean_object* v_res_2545_; 
v_closed_boxed_2543_ = lean_unbox(v_closed_2535_);
v_a_5670__boxed_2544_ = lean_unbox(v_a_2539_);
v_res_2545_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2532_, v_pendingProducer_2533_, v_interestWaiter_2534_, v_closed_boxed_2543_, v_knownSize_2536_, v_pendingIncompleteChunk_2537_, v_closeError_2538_, v_a_5670__boxed_2544_, v_____r_2540_, v___y_2541_);
lean_dec(v___y_2541_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object* v_waiter_2550_, uint8_t v_a_2551_, lean_object* v___y_2552_, lean_object* v_x_2553_){
_start:
{
if (lean_obj_tag(v_x_2553_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v_waiter_2550_);
v_a_2555_ = lean_ctor_get(v_x_2553_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_x_2553_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2557_ = v_x_2553_;
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v_x_2553_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v_pendingProducer_2565_; lean_object* v_pendingConsumer_2566_; lean_object* v_interestWaiter_2567_; uint8_t v_closed_2568_; lean_object* v_knownSize_2569_; lean_object* v_pendingIncompleteChunk_2570_; lean_object* v_closeError_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___f_2574_; 
v_a_2564_ = lean_ctor_get(v_x_2553_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v_x_2553_, 1);
v_pendingProducer_2565_ = lean_ctor_get(v_a_2564_, 0);
lean_inc_n(v_pendingProducer_2565_, 2);
v_pendingConsumer_2566_ = lean_ctor_get(v_a_2564_, 1);
lean_inc(v_pendingConsumer_2566_);
v_interestWaiter_2567_ = lean_ctor_get(v_a_2564_, 2);
lean_inc_n(v_interestWaiter_2567_, 2);
v_closed_2568_ = lean_ctor_get_uint8(v_a_2564_, sizeof(void*)*6);
v_knownSize_2569_ = lean_ctor_get(v_a_2564_, 3);
lean_inc_n(v_knownSize_2569_, 2);
v_pendingIncompleteChunk_2570_ = lean_ctor_get(v_a_2564_, 4);
lean_inc_n(v_pendingIncompleteChunk_2570_, 2);
v_closeError_2571_ = lean_ctor_get(v_a_2564_, 5);
lean_inc_n(v_closeError_2571_, 2);
lean_dec(v_a_2564_);
v___x_2572_ = lean_box(v_closed_2568_);
v___x_2573_ = lean_box(v_a_2551_);
lean_inc_ref(v_waiter_2550_);
v___f_2574_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__0___boxed), 11, 8);
lean_closure_set(v___f_2574_, 0, v_waiter_2550_);
lean_closure_set(v___f_2574_, 1, v_pendingProducer_2565_);
lean_closure_set(v___f_2574_, 2, v_interestWaiter_2567_);
lean_closure_set(v___f_2574_, 3, v___x_2572_);
lean_closure_set(v___f_2574_, 4, v_knownSize_2569_);
lean_closure_set(v___f_2574_, 5, v_pendingIncompleteChunk_2570_);
lean_closure_set(v___f_2574_, 6, v_closeError_2571_);
lean_closure_set(v___f_2574_, 7, v___x_2573_);
if (lean_obj_tag(v_pendingConsumer_2566_) == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec_ref(v___f_2574_);
v___x_2575_ = lean_box(0);
v___x_2576_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2550_, v_pendingProducer_2565_, v_interestWaiter_2567_, v_closed_2568_, v_knownSize_2569_, v_pendingIncompleteChunk_2570_, v_closeError_2571_, v_a_2551_, v___x_2575_, v___y_2552_);
return v___x_2576_;
}
else
{
lean_object* v___f_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec_ref_known(v_pendingConsumer_2566_, 1);
lean_dec(v_closeError_2571_);
lean_dec(v_pendingIncompleteChunk_2570_);
lean_dec(v_knownSize_2569_);
lean_dec(v_interestWaiter_2567_);
lean_dec(v_pendingProducer_2565_);
lean_dec_ref(v_waiter_2550_);
lean_inc(v___y_2552_);
v___f_2577_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2577_, 0, v___f_2574_);
lean_closure_set(v___f_2577_, 1, v___y_2552_);
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1));
v___x_2580_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2578_, v_a_2551_, v___x_2579_, v___f_2577_);
return v___x_2580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object* v_waiter_2581_, lean_object* v_a_2582_, lean_object* v___y_2583_, lean_object* v_x_2584_, lean_object* v___y_2585_){
_start:
{
uint8_t v_a_5711__boxed_2586_; lean_object* v_res_2587_; 
v_a_5711__boxed_2586_ = lean_unbox(v_a_2582_);
v_res_2587_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v_waiter_2581_, v_a_5711__boxed_2586_, v___y_2583_, v_x_2584_);
lean_dec(v___y_2583_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object* v___x_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2588_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object* v___x_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_2593_, v___y_2594_);
lean_dec(v___y_2594_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object* v_waiter_2599_, lean_object* v___y_2600_, lean_object* v_x_2601_){
_start:
{
if (lean_obj_tag(v_x_2601_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v_waiter_2599_);
v_a_2603_ = lean_ctor_get(v_x_2601_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_x_2601_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2605_ = v_x_2601_;
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v_x_2601_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
return v___x_2609_;
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2628_; 
v_a_2612_ = lean_ctor_get(v_x_2601_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_x_2601_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2614_ = v_x_2601_;
v_isShared_2615_ = v_isSharedCheck_2628_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v_x_2601_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2628_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_unbox(v_a_2612_);
if (v___x_2616_ == 0)
{
lean_object* v___f_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_inc(v___y_2600_);
lean_inc(v_a_2612_);
v___f_2617_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2617_, 0, v_waiter_2599_);
lean_closure_set(v___f_2617_, 1, v_a_2612_);
lean_closure_set(v___f_2617_, 2, v___y_2600_);
v___x_2618_ = lean_unsigned_to_nat(0u);
v___x_2619_ = lean_st_ref_get(v___y_2600_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2619_);
v___x_2621_ = v___x_2614_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
v___x_2623_ = lean_unbox(v_a_2612_);
lean_dec(v_a_2612_);
v___x_2624_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2618_, v___x_2623_, v___x_2622_, v___f_2617_);
return v___x_2624_;
}
}
else
{
lean_object* v___f_2626_; lean_object* v___x_2627_; 
lean_del_object(v___x_2614_);
lean_dec(v_a_2612_);
v___f_2626_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_2627_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_waiter_2599_, v___f_2626_, v___y_2600_);
return v___x_2627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object* v_waiter_2629_, lean_object* v___y_2630_, lean_object* v_x_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v_waiter_2629_, v___y_2630_, v_x_2631_);
lean_dec(v___y_2630_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object* v___y_2634_, lean_object* v___f_2635_, lean_object* v_x_2636_){
_start:
{
if (lean_obj_tag(v_x_2636_) == 0)
{
lean_object* v___x_2638_; 
lean_dec_ref(v___f_2635_);
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_x_2636_);
return v___x_2638_;
}
else
{
lean_object* v___x_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec_ref_known(v_x_2636_, 1);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = 0;
v___x_2641_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_2634_);
v___x_2642_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2639_, v___x_2640_, v___x_2641_, v___f_2635_);
return v___x_2642_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object* v___y_2643_, lean_object* v___f_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_2643_, v___f_2644_, v_x_2645_);
lean_dec(v___y_2643_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object* v_waiter_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___f_2651_; lean_object* v___f_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_inc_n(v___y_2649_, 2);
v___f_2651_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__4___boxed), 4, 2);
lean_closure_set(v___f_2651_, 0, v_waiter_2648_);
lean_closure_set(v___f_2651_, 1, v___y_2649_);
v___f_2652_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2652_, 0, v___y_2649_);
lean_closure_set(v___f_2652_, 1, v___f_2651_);
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = 0;
v___x_2655_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2649_);
v___x_2656_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2653_, v___x_2654_, v___x_2655_, v___f_2652_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object* v_waiter_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_2657_, v___y_2658_);
lean_dec(v___y_2658_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object* v_stream_2661_, lean_object* v_waiter_2662_){
_start:
{
lean_object* v___f_2664_; lean_object* v___x_2665_; 
v___f_2664_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2664_, 0, v_waiter_2662_);
v___x_2665_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2661_, v___f_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object* v_stream_2666_, lean_object* v_waiter_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_2666_, v_waiter_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object* v_stream_2671_){
_start:
{
lean_object* v___f_2672_; lean_object* v___f_2673_; lean_object* v___f_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___f_2672_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_2671_, 2);
v___f_2673_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2673_, 0, v_stream_2671_);
v___f_2674_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_2675_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2675_, 0, lean_box(0));
lean_closure_set(v___x_2675_, 1, lean_box(0));
lean_closure_set(v___x_2675_, 2, v_stream_2671_);
lean_closure_set(v___x_2675_, 3, v___f_2674_);
v___x_2676_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2676_, 0, lean_box(0));
lean_closure_set(v___x_2676_, 1, lean_box(0));
lean_closure_set(v___x_2676_, 2, v_stream_2671_);
lean_closure_set(v___x_2676_, 3, v___f_2672_);
v___x_2677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2675_);
lean_ctor_set(v___x_2677_, 1, v___f_2673_);
lean_ctor_set(v___x_2677_, 2, v___x_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(lean_object* v_step_2678_, lean_object* v_acc_2679_, lean_object* v___f_2680_, lean_object* v_x_2681_){
_start:
{
if (lean_obj_tag(v_x_2681_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v___f_2680_);
lean_dec(v_acc_2679_);
lean_dec_ref(v_step_2678_);
v_a_2683_ = lean_ctor_get(v_x_2681_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_x_2681_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2685_ = v_x_2681_;
v_isShared_2686_ = v_isSharedCheck_2691_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v_x_2681_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2691_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
return v___x_2689_;
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2705_; 
v_a_2692_ = lean_ctor_get(v_x_2681_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_x_2681_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2694_ = v_x_2681_;
v_isShared_2695_ = v_isSharedCheck_2705_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v_x_2681_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2705_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
if (lean_obj_tag(v_a_2692_) == 1)
{
lean_object* v_val_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_del_object(v___x_2694_);
v_val_2696_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_val_2696_);
lean_dec_ref_known(v_a_2692_, 1);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = 0;
v___x_2699_ = lean_apply_3(v_step_2678_, v_val_2696_, v_acc_2679_, lean_box(0));
v___x_2700_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2697_, v___x_2698_, v___x_2699_, v___f_2680_);
return v___x_2700_;
}
else
{
lean_object* v___x_2702_; 
lean_dec(v_a_2692_);
lean_dec_ref(v___f_2680_);
lean_dec_ref(v_step_2678_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v_acc_2679_);
v___x_2702_ = v___x_2694_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_acc_2679_);
v___x_2702_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed(lean_object* v_step_2706_, lean_object* v_acc_2707_, lean_object* v___f_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(v_step_2706_, v_acc_2707_, v___f_2708_, v_x_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(lean_object* v_step_2712_, lean_object* v_stream_2713_, lean_object* v_x_2714_){
_start:
{
if (lean_obj_tag(v_x_2714_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref(v_stream_2713_);
lean_dec_ref(v_step_2712_);
v_a_2716_ = lean_ctor_get(v_x_2714_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_x_2714_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v_x_2714_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v_x_2714_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2742_; 
v_a_2725_ = lean_ctor_get(v_x_2714_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_x_2714_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2727_ = v_x_2714_;
v_isShared_2728_ = v_isSharedCheck_2742_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v_x_2714_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2742_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
if (lean_obj_tag(v_a_2725_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2739_; 
lean_dec_ref(v_stream_2713_);
lean_dec_ref(v_step_2712_);
v_a_2729_ = lean_ctor_get(v_a_2725_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_a_2725_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2731_ = v_a_2725_;
v_isShared_2732_ = v_isSharedCheck_2739_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v_a_2725_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2739_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v_a_2729_);
v___x_2734_ = v___x_2727_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2736_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v___x_2734_);
v___x_2736_ = v___x_2731_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2741_; 
lean_del_object(v___x_2727_);
v_a_2740_ = lean_ctor_get(v_a_2725_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v_a_2725_, 1);
v___x_2741_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2712_, v_stream_2713_, v_a_2740_);
return v___x_2741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed(lean_object* v_step_2743_, lean_object* v_stream_2744_, lean_object* v_x_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(v_step_2743_, v_stream_2744_, v_x_2745_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(lean_object* v_step_2748_, lean_object* v_stream_2749_, lean_object* v_acc_2750_){
_start:
{
lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_inc_ref(v_stream_2749_);
lean_inc_ref(v_step_2748_);
v___f_2752_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2752_, 0, v_step_2748_);
lean_closure_set(v___f_2752_, 1, v_stream_2749_);
v___f_2753_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2753_, 0, v_step_2748_);
lean_closure_set(v___f_2753_, 1, v_acc_2750_);
lean_closure_set(v___f_2753_, 2, v___f_2752_);
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = 0;
v___x_2756_ = l_Std_Http_Body_Stream_recv(v_stream_2749_);
v___x_2757_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2754_, v___x_2755_, v___x_2756_, v___f_2753_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___boxed(lean_object* v_step_2758_, lean_object* v_stream_2759_, lean_object* v_acc_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2758_, v_stream_2759_, v_acc_2760_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(lean_object* v_00_u03b2_2763_, lean_object* v_step_2764_, lean_object* v_stream_2765_, lean_object* v_acc_2766_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2764_, v_stream_2765_, v_acc_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___boxed(lean_object* v_00_u03b2_2769_, lean_object* v_step_2770_, lean_object* v_stream_2771_, lean_object* v_acc_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(v_00_u03b2_2769_, v_step_2770_, v_stream_2771_, v_acc_2772_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_2775_, lean_object* v_acc_2776_, lean_object* v_step_2777_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2777_, v_stream_2775_, v_acc_2776_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_2780_, lean_object* v_acc_2781_, lean_object* v_step_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_2780_, v_acc_2781_, v_step_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_2785_, lean_object* v_stream_2786_, lean_object* v_acc_2787_, lean_object* v_step_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2788_, v_stream_2786_, v_acc_2787_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_2791_, lean_object* v_stream_2792_, lean_object* v_acc_2793_, lean_object* v_step_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_2791_, v_stream_2792_, v_acc_2793_, v_step_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(lean_object* v___y_2797_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___y_2797_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(v___y_2801_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(lean_object* v_x_2804_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed(lean_object* v_x_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(v_x_2807_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(lean_object* v_step_2810_, lean_object* v_acc_2811_, lean_object* v_a_2812_, lean_object* v___f_2813_, lean_object* v_x_2814_){
_start:
{
if (lean_obj_tag(v_x_2814_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2824_; 
lean_dec_ref(v___f_2813_);
lean_dec(v_acc_2811_);
lean_dec_ref(v_step_2810_);
v_a_2816_ = lean_ctor_get(v_x_2814_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_x_2814_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2818_ = v_x_2814_;
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v_x_2814_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
return v___x_2822_;
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2838_; 
v_a_2825_ = lean_ctor_get(v_x_2814_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_x_2814_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2827_ = v_x_2814_;
v_isShared_2828_ = v_isSharedCheck_2838_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v_x_2814_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2838_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
if (lean_obj_tag(v_a_2825_) == 1)
{
lean_object* v_val_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_del_object(v___x_2827_);
v_val_2829_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_val_2829_);
lean_dec_ref_known(v_a_2825_, 1);
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = 0;
lean_inc_ref(v_a_2812_);
v___x_2832_ = lean_apply_4(v_step_2810_, v_val_2829_, v_acc_2811_, v_a_2812_, lean_box(0));
v___x_2833_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2830_, v___x_2831_, v___x_2832_, v___f_2813_);
return v___x_2833_;
}
else
{
lean_object* v___x_2835_; 
lean_dec(v_a_2825_);
lean_dec_ref(v___f_2813_);
lean_dec_ref(v_step_2810_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v_acc_2811_);
v___x_2835_ = v___x_2827_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_acc_2811_);
v___x_2835_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
return v___x_2836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed(lean_object* v_step_2839_, lean_object* v_acc_2840_, lean_object* v_a_2841_, lean_object* v___f_2842_, lean_object* v_x_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(v_step_2839_, v_acc_2840_, v_a_2841_, v___f_2842_, v_x_2843_);
lean_dec_ref(v_a_2841_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(lean_object* v_x_2846_){
_start:
{
if (lean_obj_tag(v_x_2846_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2856_; 
v_a_2848_ = lean_ctor_get(v_x_2846_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_x_2846_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2850_ = v_x_2846_;
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v_x_2846_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
return v___x_2854_;
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2867_; 
v_a_2857_ = lean_ctor_get(v_x_2846_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_x_2846_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2859_ = v_x_2846_;
v_isShared_2860_ = v_isSharedCheck_2867_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v_x_2846_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2867_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_token_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v_token_2861_ = lean_ctor_get(v_a_2857_, 1);
lean_inc_ref(v_token_2861_);
lean_dec(v_a_2857_);
v___x_2862_ = l_Std_CancellationToken_selector(v_token_2861_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2862_);
v___x_2864_ = v___x_2859_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; 
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
return v___x_2865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed(lean_object* v_x_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(v_x_2868_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(lean_object* v_stream_2871_, lean_object* v___f_2872_, lean_object* v___f_2873_, lean_object* v___f_2874_, lean_object* v_x_2875_){
_start:
{
if (lean_obj_tag(v_x_2875_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2885_; 
lean_dec_ref(v___f_2874_);
lean_dec_ref(v___f_2873_);
lean_dec_ref(v___f_2872_);
lean_dec_ref(v_stream_2871_);
v_a_2877_ = lean_ctor_get(v_x_2875_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_x_2875_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2879_ = v_x_2875_;
v_isShared_2880_ = v_isSharedCheck_2885_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v_x_2875_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2885_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
return v___x_2883_;
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_a_2886_ = lean_ctor_get(v_x_2875_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v_x_2875_, 1);
v___x_2887_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2871_);
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
lean_ctor_set(v___x_2888_, 1, v___f_2872_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_a_2886_);
lean_ctor_set(v___x_2889_, 1, v___f_2873_);
v___x_2890_ = lean_unsigned_to_nat(2u);
v___x_2891_ = lean_mk_empty_array_with_capacity(v___x_2890_);
v___x_2892_ = lean_array_push(v___x_2891_, v___x_2888_);
v___x_2893_ = lean_array_push(v___x_2892_, v___x_2889_);
v___x_2894_ = lean_unsigned_to_nat(0u);
v___x_2895_ = 0;
v___x_2896_ = l_Std_Async_Selectable_one___redArg(v___x_2893_);
v___x_2897_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2894_, v___x_2895_, v___x_2896_, v___f_2874_);
return v___x_2897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed(lean_object* v_stream_2898_, lean_object* v___f_2899_, lean_object* v___f_2900_, lean_object* v___f_2901_, lean_object* v_x_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(v_stream_2898_, v___f_2899_, v___f_2900_, v___f_2901_, v_x_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed(lean_object* v_step_2907_, lean_object* v_stream_2908_, lean_object* v_a_2909_, lean_object* v_x_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(v_step_2907_, v_stream_2908_, v_a_2909_, v_x_2910_);
lean_dec_ref(v_a_2909_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(lean_object* v_step_2914_, lean_object* v_stream_2915_, lean_object* v_acc_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___f_2919_; lean_object* v___f_2920_; lean_object* v___f_2921_; lean_object* v___f_2922_; lean_object* v___f_2923_; lean_object* v___f_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___f_2919_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0));
v___f_2920_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1));
lean_inc_ref_n(v_a_2917_, 3);
lean_inc_ref(v_stream_2915_);
lean_inc_ref(v_step_2914_);
v___f_2921_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_2921_, 0, v_step_2914_);
lean_closure_set(v___f_2921_, 1, v_stream_2915_);
lean_closure_set(v___f_2921_, 2, v_a_2917_);
v___f_2922_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_2922_, 0, v_step_2914_);
lean_closure_set(v___f_2922_, 1, v_acc_2916_);
lean_closure_set(v___f_2922_, 2, v_a_2917_);
lean_closure_set(v___f_2922_, 3, v___f_2921_);
v___f_2923_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_2923_, 0, v_stream_2915_);
lean_closure_set(v___f_2923_, 1, v___f_2919_);
lean_closure_set(v___f_2923_, 2, v___f_2920_);
lean_closure_set(v___f_2923_, 3, v___f_2922_);
v___f_2924_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2));
v___x_2925_ = lean_unsigned_to_nat(0u);
v___x_2926_ = 0;
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v_a_2917_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
v___x_2929_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2925_, v___x_2926_, v___x_2928_, v___f_2924_);
v___x_2930_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2925_, v___x_2926_, v___x_2929_, v___f_2923_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(lean_object* v_step_2931_, lean_object* v_stream_2932_, lean_object* v_a_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2934_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v_stream_2932_);
lean_dec_ref(v_step_2931_);
v_a_2936_ = lean_ctor_get(v_x_2934_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_x_2934_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2938_ = v_x_2934_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v_x_2934_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2962_; 
v_a_2945_ = lean_ctor_get(v_x_2934_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_x_2934_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2947_ = v_x_2934_;
v_isShared_2948_ = v_isSharedCheck_2962_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v_x_2934_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2962_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
if (lean_obj_tag(v_a_2945_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref(v_stream_2932_);
lean_dec_ref(v_step_2931_);
v_a_2949_ = lean_ctor_get(v_a_2945_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_a_2945_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2951_ = v_a_2945_;
v_isShared_2952_ = v_isSharedCheck_2959_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v_a_2945_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2959_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v_a_2949_);
v___x_2954_ = v___x_2947_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2956_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2954_);
v___x_2956_ = v___x_2951_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2961_; 
lean_del_object(v___x_2947_);
v_a_2960_ = lean_ctor_get(v_a_2945_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v_a_2945_, 1);
v___x_2961_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2931_, v_stream_2932_, v_a_2960_, v_a_2933_);
return v___x_2961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___boxed(lean_object* v_step_2963_, lean_object* v_stream_2964_, lean_object* v_acc_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2963_, v_stream_2964_, v_acc_2965_, v_a_2966_);
lean_dec_ref(v_a_2966_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(lean_object* v_00_u03b2_2969_, lean_object* v_step_2970_, lean_object* v_stream_2971_, lean_object* v_acc_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2970_, v_stream_2971_, v_acc_2972_, v_a_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___boxed(lean_object* v_00_u03b2_2976_, lean_object* v_step_2977_, lean_object* v_stream_2978_, lean_object* v_acc_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(v_00_u03b2_2976_, v_step_2977_, v_stream_2978_, v_acc_2979_, v_a_2980_);
lean_dec_ref(v_a_2980_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_2983_, lean_object* v_acc_2984_, lean_object* v_step_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2985_, v_stream_2983_, v_acc_2984_, v_a_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_2989_, lean_object* v_acc_2990_, lean_object* v_step_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_2989_, v_acc_2990_, v_step_2991_, v_a_2992_);
lean_dec_ref(v_a_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_2995_, lean_object* v_stream_2996_, lean_object* v_acc_2997_, lean_object* v_step_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2998_, v_stream_2996_, v_acc_2997_, v_a_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_3002_, lean_object* v_stream_3003_, lean_object* v_acc_3004_, lean_object* v_step_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_3002_, v_stream_3003_, v_acc_3004_, v_step_3005_, v_a_3006_);
lean_dec_ref(v_a_3006_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v_x_3011_){
_start:
{
if (lean_obj_tag(v_x_3011_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3021_; 
v_a_3013_ = lean_ctor_get(v_x_3011_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_x_3011_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3015_ = v_x_3011_;
v_isShared_3016_ = v_isSharedCheck_3021_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v_x_3011_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3021_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
return v___x_3019_;
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3032_; 
v_a_3022_ = lean_ctor_get(v_x_3011_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_x_3011_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3024_ = v_x_3011_;
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v_x_3011_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_token_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
v_token_3026_ = lean_ctor_get(v_a_3022_, 1);
lean_inc_ref(v_token_3026_);
lean_dec(v_a_3022_);
v___x_3027_ = l_Std_CancellationToken_selector(v_token_3026_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3027_);
v___x_3029_ = v___x_3024_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
return v___x_3030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v_x_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v_x_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(lean_object* v_x_3036_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed(lean_object* v_x_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(v_x_3039_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___y_3042_);
v___x_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed(lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(v___y_3046_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v_stream_3049_, lean_object* v___f_3050_, lean_object* v___f_3051_, lean_object* v_x_3052_){
_start:
{
if (lean_obj_tag(v_x_3052_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3062_; 
lean_dec_ref(v___f_3051_);
lean_dec_ref(v___f_3050_);
lean_dec_ref(v_stream_3049_);
v_a_3054_ = lean_ctor_get(v_x_3052_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_x_3052_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3056_ = v_x_3052_;
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v_x_3052_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
return v___x_3060_;
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_a_3063_ = lean_ctor_get(v_x_3052_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v_x_3052_, 1);
v___x_3064_ = l_Std_Http_Body_Stream_recvSelector(v_stream_3049_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v___f_3050_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v_a_3063_);
lean_ctor_set(v___x_3066_, 1, v___f_3051_);
v___x_3067_ = lean_unsigned_to_nat(2u);
v___x_3068_ = lean_mk_empty_array_with_capacity(v___x_3067_);
v___x_3069_ = lean_array_push(v___x_3068_, v___x_3065_);
v___x_3070_ = lean_array_push(v___x_3069_, v___x_3066_);
v___x_3071_ = l_Std_Async_Selectable_one___redArg(v___x_3070_);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v_stream_3072_, lean_object* v___f_3073_, lean_object* v___f_3074_, lean_object* v_x_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_3072_, v___f_3073_, v___f_3074_, v_x_3075_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(lean_object* v___f_3078_, lean_object* v___f_3079_, lean_object* v___f_3080_, lean_object* v_stream_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___f_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___f_3084_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3084_, 0, v_stream_3081_);
lean_closure_set(v___f_3084_, 1, v___f_3078_);
lean_closure_set(v___f_3084_, 2, v___f_3079_);
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = 0;
lean_inc_ref(v___y_3082_);
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___y_3082_);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
v___x_3089_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3085_, v___x_3086_, v___x_3088_, v___f_3080_);
v___x_3090_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3085_, v___x_3086_, v___x_3089_, v___f_3084_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4___boxed(lean_object* v___f_3091_, lean_object* v___f_3092_, lean_object* v___f_3093_, lean_object* v_stream_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(v___f_3091_, v___f_3092_, v___f_3093_, v_stream_3094_, v___y_3095_);
lean_dec_ref(v___y_3095_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v_toPure_3108_, lean_object* v_result_3109_, lean_object* v_maximumSize_3110_, lean_object* v_inst_3111_, lean_object* v_inst_3112_, lean_object* v_inst_3113_, lean_object* v_stream_3114_, lean_object* v_toBind_3115_, lean_object* v_____do__lift_3116_){
_start:
{
if (lean_obj_tag(v_____do__lift_3116_) == 0)
{
lean_object* v___x_3117_; 
lean_dec(v_toBind_3115_);
lean_dec_ref(v_stream_3114_);
lean_dec(v_inst_3113_);
lean_dec_ref(v_inst_3112_);
lean_dec_ref(v_inst_3111_);
lean_dec(v_maximumSize_3110_);
v___x_3117_ = lean_apply_2(v_toPure_3108_, lean_box(0), v_result_3109_);
return v___x_3117_;
}
else
{
lean_object* v_val_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_toPure_3108_);
v_val_3118_ = lean_ctor_get(v_____do__lift_3116_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_____do__lift_3116_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3120_ = v_____do__lift_3116_;
v_isShared_3121_ = v_isSharedCheck_3149_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_val_3118_);
lean_dec(v_____do__lift_3116_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3149_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v_data_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; lean_object* v_result_3127_; 
v_data_3122_ = lean_ctor_get(v_val_3118_, 0);
lean_inc_ref(v_data_3122_);
lean_dec(v_val_3118_);
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = lean_byte_array_size(v_result_3109_);
v___x_3125_ = lean_byte_array_size(v_data_3122_);
v___x_3126_ = 0;
v_result_3127_ = lean_byte_array_copy_slice(v_data_3122_, v___x_3123_, v_result_3109_, v___x_3124_, v___x_3125_, v___x_3126_);
lean_dec_ref(v_data_3122_);
if (lean_obj_tag(v_maximumSize_3110_) == 1)
{
lean_object* v_val_3128_; lean_object* v___x_3129_; uint64_t v___x_3130_; uint64_t v___x_3131_; uint8_t v___x_3132_; 
v_val_3128_ = lean_ctor_get(v_maximumSize_3110_, 0);
v___x_3129_ = lean_byte_array_size(v_result_3127_);
v___x_3130_ = lean_uint64_of_nat(v___x_3129_);
v___x_3131_ = lean_unbox_uint64(v_val_3128_);
v___x_3132_ = lean_uint64_dec_lt(v___x_3131_, v___x_3130_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; 
lean_del_object(v___x_3120_);
lean_dec(v_toBind_3115_);
v___x_3133_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3111_, v_inst_3112_, v_inst_3113_, v_stream_3114_, v_maximumSize_3110_, v_result_3127_);
return v___x_3133_;
}
else
{
lean_object* v_throw_3134_; lean_object* v___f_3135_; lean_object* v___x_3136_; uint64_t v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3144_; 
lean_inc(v_val_3128_);
v_throw_3134_ = lean_ctor_get(v_inst_3112_, 0);
lean_inc(v_throw_3134_);
v___f_3135_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0), 7, 6);
lean_closure_set(v___f_3135_, 0, v_inst_3111_);
lean_closure_set(v___f_3135_, 1, v_inst_3112_);
lean_closure_set(v___f_3135_, 2, v_inst_3113_);
lean_closure_set(v___f_3135_, 3, v_stream_3114_);
lean_closure_set(v___f_3135_, 4, v_maximumSize_3110_);
lean_closure_set(v___f_3135_, 5, v_result_3127_);
v___x_3136_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0));
v___x_3137_ = lean_unbox_uint64(v_val_3128_);
lean_dec(v_val_3128_);
v___x_3138_ = lean_uint64_to_nat(v___x_3137_);
v___x_3139_ = l_Nat_reprFast(v___x_3138_);
v___x_3140_ = lean_string_append(v___x_3136_, v___x_3139_);
lean_dec_ref(v___x_3139_);
v___x_3141_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1));
v___x_3142_ = lean_string_append(v___x_3140_, v___x_3141_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set_tag(v___x_3120_, 18);
lean_ctor_set(v___x_3120_, 0, v___x_3142_);
v___x_3144_ = v___x_3120_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_apply_2(v_throw_3134_, lean_box(0), v___x_3144_);
v___x_3146_ = lean_apply_4(v_toBind_3115_, lean_box(0), lean_box(0), v___x_3145_, v___f_3135_);
return v___x_3146_;
}
}
}
else
{
lean_object* v___x_3148_; 
lean_del_object(v___x_3120_);
lean_dec(v_toBind_3115_);
v___x_3148_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3111_, v_inst_3112_, v_inst_3113_, v_stream_3114_, v_maximumSize_3110_, v_result_3127_);
return v___x_3148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_stream_3153_, lean_object* v_maximumSize_3154_, lean_object* v_result_3155_){
_start:
{
lean_object* v_toApplicative_3156_; lean_object* v_toBind_3157_; lean_object* v_toPure_3158_; lean_object* v___x_3159_; lean_object* v___f_3160_; lean_object* v___x_3161_; 
v_toApplicative_3156_ = lean_ctor_get(v_inst_3150_, 0);
v_toBind_3157_ = lean_ctor_get(v_inst_3150_, 1);
lean_inc_n(v_toBind_3157_, 2);
v_toPure_3158_ = lean_ctor_get(v_toApplicative_3156_, 1);
lean_inc(v_toPure_3158_);
lean_inc(v_inst_3152_);
lean_inc_ref(v_stream_3153_);
v___x_3159_ = lean_apply_1(v_inst_3152_, v_stream_3153_);
v___f_3160_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 9, 8);
lean_closure_set(v___f_3160_, 0, v_toPure_3158_);
lean_closure_set(v___f_3160_, 1, v_result_3155_);
lean_closure_set(v___f_3160_, 2, v_maximumSize_3154_);
lean_closure_set(v___f_3160_, 3, v_inst_3150_);
lean_closure_set(v___f_3160_, 4, v_inst_3151_);
lean_closure_set(v___f_3160_, 5, v_inst_3152_);
lean_closure_set(v___f_3160_, 6, v_stream_3153_);
lean_closure_set(v___f_3160_, 7, v_toBind_3157_);
v___x_3161_ = lean_apply_4(v_toBind_3157_, lean_box(0), lean_box(0), v___x_3159_, v___f_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_stream_3165_, lean_object* v_maximumSize_3166_, lean_object* v_result_3167_, lean_object* v_____r_3168_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3162_, v_inst_3163_, v_inst_3164_, v_stream_3165_, v_maximumSize_3166_, v_result_3167_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_stream_3174_, lean_object* v_maximumSize_3175_, lean_object* v_result_3176_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3171_, v_inst_3172_, v_inst_3173_, v_stream_3174_, v_maximumSize_3175_, v_result_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_toPure_3180_, lean_object* v_result_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_apply_1(v_inst_3178_, v_result_3181_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v_toPure_3180_);
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3192_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3192_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_throw_3187_; lean_object* v___x_3189_; 
v_throw_3187_ = lean_ctor_get(v_inst_3179_, 0);
lean_inc(v_throw_3187_);
lean_dec_ref(v_inst_3179_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 18);
v___x_3189_ = v___x_3185_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3183_);
v___x_3189_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_apply_2(v_throw_3187_, lean_box(0), v___x_3189_);
return v___x_3190_;
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3194_; 
lean_dec_ref(v_inst_3179_);
v_a_3193_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3182_, 1);
v___x_3194_ = lean_apply_2(v_toPure_3180_, lean_box(0), v_a_3193_);
return v___x_3194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_3195_, lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_stream_3199_, lean_object* v_maximumSize_3200_){
_start:
{
lean_object* v_toApplicative_3201_; lean_object* v_toBind_3202_; lean_object* v_toPure_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___f_3206_; lean_object* v___x_3207_; 
v_toApplicative_3201_ = lean_ctor_get(v_inst_3196_, 0);
v_toBind_3202_ = lean_ctor_get(v_inst_3196_, 1);
lean_inc(v_toBind_3202_);
v_toPure_3203_ = lean_ctor_get(v_toApplicative_3201_, 1);
lean_inc(v_toPure_3203_);
v___x_3204_ = l_ByteArray_empty;
lean_inc_ref(v_inst_3197_);
v___x_3205_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3196_, v_inst_3197_, v_inst_3198_, v_stream_3199_, v_maximumSize_3200_, v___x_3204_);
v___f_3206_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3206_, 0, v_inst_3195_);
lean_closure_set(v___f_3206_, 1, v_inst_3197_);
lean_closure_set(v___f_3206_, 2, v_toPure_3203_);
v___x_3207_ = lean_apply_4(v_toBind_3202_, lean_box(0), lean_box(0), v___x_3205_, v___f_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_3208_, lean_object* v_m_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_stream_3214_, lean_object* v_maximumSize_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_3210_, v_inst_3211_, v_inst_3212_, v_inst_3213_, v_stream_3214_, v_maximumSize_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0(lean_object* v_toPure_3217_, lean_object* v_____r_3218_){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_box(0);
v___x_3220_ = lean_apply_2(v_toPure_3217_, lean_box(0), v___x_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(lean_object* v_toPure_3221_, uint64_t v_consumed_3222_, lean_object* v_drainLimit_3223_, lean_object* v_inst_3224_, lean_object* v_inst_3225_, lean_object* v_stream_3226_, lean_object* v_closeStream_3227_, lean_object* v_toBind_3228_, lean_object* v___f_3229_, lean_object* v_____do__lift_3230_){
_start:
{
if (lean_obj_tag(v_____do__lift_3230_) == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec(v___f_3229_);
lean_dec(v_toBind_3228_);
lean_dec(v_closeStream_3227_);
lean_dec_ref(v_stream_3226_);
lean_dec(v_inst_3225_);
lean_dec_ref(v_inst_3224_);
lean_dec(v_drainLimit_3223_);
v___x_3231_ = lean_box(0);
v___x_3232_ = lean_apply_2(v_toPure_3221_, lean_box(0), v___x_3231_);
return v___x_3232_;
}
else
{
lean_object* v_val_3233_; lean_object* v_data_3234_; lean_object* v___x_3235_; uint64_t v___x_3236_; uint64_t v_consumed_3237_; 
lean_dec(v_toPure_3221_);
v_val_3233_ = lean_ctor_get(v_____do__lift_3230_, 0);
v_data_3234_ = lean_ctor_get(v_val_3233_, 0);
v___x_3235_ = lean_byte_array_size(v_data_3234_);
v___x_3236_ = lean_uint64_of_nat(v___x_3235_);
v_consumed_3237_ = lean_uint64_add(v_consumed_3222_, v___x_3236_);
if (lean_obj_tag(v_drainLimit_3223_) == 1)
{
lean_object* v_val_3238_; uint64_t v___x_3239_; uint8_t v___x_3240_; 
v_val_3238_ = lean_ctor_get(v_drainLimit_3223_, 0);
v___x_3239_ = lean_unbox_uint64(v_val_3238_);
v___x_3240_ = lean_uint64_dec_lt(v___x_3239_, v_consumed_3237_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; 
lean_dec(v___f_3229_);
lean_dec(v_toBind_3228_);
v___x_3241_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3224_, v_inst_3225_, v_stream_3226_, v_drainLimit_3223_, v_closeStream_3227_, v_consumed_3237_);
return v___x_3241_;
}
else
{
lean_object* v___x_3242_; 
lean_dec_ref_known(v_drainLimit_3223_, 1);
lean_dec_ref(v_stream_3226_);
lean_dec(v_inst_3225_);
lean_dec_ref(v_inst_3224_);
v___x_3242_ = lean_apply_4(v_toBind_3228_, lean_box(0), lean_box(0), v_closeStream_3227_, v___f_3229_);
return v___x_3242_;
}
}
else
{
lean_object* v___x_3243_; 
lean_dec(v___f_3229_);
lean_dec(v_toBind_3228_);
v___x_3243_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3224_, v_inst_3225_, v_stream_3226_, v_drainLimit_3223_, v_closeStream_3227_, v_consumed_3237_);
return v___x_3243_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed(lean_object* v_toPure_3244_, lean_object* v_consumed_3245_, lean_object* v_drainLimit_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_stream_3249_, lean_object* v_closeStream_3250_, lean_object* v_toBind_3251_, lean_object* v___f_3252_, lean_object* v_____do__lift_3253_){
_start:
{
uint64_t v_consumed_boxed_3254_; lean_object* v_res_3255_; 
v_consumed_boxed_3254_ = lean_unbox_uint64(v_consumed_3245_);
lean_dec_ref(v_consumed_3245_);
v_res_3255_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(v_toPure_3244_, v_consumed_boxed_3254_, v_drainLimit_3246_, v_inst_3247_, v_inst_3248_, v_stream_3249_, v_closeStream_3250_, v_toBind_3251_, v___f_3252_, v_____do__lift_3253_);
lean_dec(v_____do__lift_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_stream_3258_, lean_object* v_drainLimit_3259_, lean_object* v_closeStream_3260_, uint64_t v_consumed_3261_){
_start:
{
lean_object* v_toApplicative_3262_; lean_object* v_toBind_3263_; lean_object* v_toPure_3264_; lean_object* v___x_3265_; lean_object* v___f_3266_; lean_object* v___x_3267_; lean_object* v___f_3268_; lean_object* v___x_3269_; 
v_toApplicative_3262_ = lean_ctor_get(v_inst_3256_, 0);
v_toBind_3263_ = lean_ctor_get(v_inst_3256_, 1);
lean_inc_n(v_toBind_3263_, 2);
v_toPure_3264_ = lean_ctor_get(v_toApplicative_3262_, 1);
lean_inc_n(v_toPure_3264_, 2);
lean_inc(v_inst_3257_);
lean_inc_ref(v_stream_3258_);
v___x_3265_ = lean_apply_1(v_inst_3257_, v_stream_3258_);
v___f_3266_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3266_, 0, v_toPure_3264_);
v___x_3267_ = lean_box_uint64(v_consumed_3261_);
v___f_3268_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3268_, 0, v_toPure_3264_);
lean_closure_set(v___f_3268_, 1, v___x_3267_);
lean_closure_set(v___f_3268_, 2, v_drainLimit_3259_);
lean_closure_set(v___f_3268_, 3, v_inst_3256_);
lean_closure_set(v___f_3268_, 4, v_inst_3257_);
lean_closure_set(v___f_3268_, 5, v_stream_3258_);
lean_closure_set(v___f_3268_, 6, v_closeStream_3260_);
lean_closure_set(v___f_3268_, 7, v_toBind_3263_);
lean_closure_set(v___f_3268_, 8, v___f_3266_);
v___x_3269_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v___x_3265_, v___f_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___boxed(lean_object* v_inst_3270_, lean_object* v_inst_3271_, lean_object* v_stream_3272_, lean_object* v_drainLimit_3273_, lean_object* v_closeStream_3274_, lean_object* v_consumed_3275_){
_start:
{
uint64_t v_consumed_boxed_3276_; lean_object* v_res_3277_; 
v_consumed_boxed_3276_ = lean_unbox_uint64(v_consumed_3275_);
lean_dec_ref(v_consumed_3275_);
v_res_3277_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3270_, v_inst_3271_, v_stream_3272_, v_drainLimit_3273_, v_closeStream_3274_, v_consumed_boxed_3276_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_object* v_m_3278_, lean_object* v_inst_3279_, lean_object* v_inst_3280_, lean_object* v_stream_3281_, lean_object* v_drainLimit_3282_, lean_object* v_closeStream_3283_, uint64_t v_consumed_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3279_, v_inst_3280_, v_stream_3281_, v_drainLimit_3282_, v_closeStream_3283_, v_consumed_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___boxed(lean_object* v_m_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_stream_3289_, lean_object* v_drainLimit_3290_, lean_object* v_closeStream_3291_, lean_object* v_consumed_3292_){
_start:
{
uint64_t v_consumed_boxed_3293_; lean_object* v_res_3294_; 
v_consumed_boxed_3293_ = lean_unbox_uint64(v_consumed_3292_);
lean_dec_ref(v_consumed_3292_);
v_res_3294_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(v_m_3286_, v_inst_3287_, v_inst_3288_, v_stream_3289_, v_drainLimit_3290_, v_closeStream_3291_, v_consumed_boxed_3293_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain___redArg(lean_object* v_inst_3295_, lean_object* v_inst_3296_, lean_object* v_stream_3297_, lean_object* v_drainLimit_3298_, lean_object* v_closeStream_3299_){
_start:
{
uint64_t v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = 0ULL;
v___x_3301_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3295_, v_inst_3296_, v_stream_3297_, v_drainLimit_3298_, v_closeStream_3299_, v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain(lean_object* v_m_3302_, lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_stream_3305_, lean_object* v_drainLimit_3306_, lean_object* v_closeStream_3307_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Std_Http_Body_Stream_drain___redArg(v_inst_3303_, v_inst_3304_, v_stream_3305_, v_drainLimit_3306_, v_closeStream_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t v_incomplete_3314_, lean_object* v_chunk_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v_pendingProducer_3320_; lean_object* v_pendingConsumer_3321_; lean_object* v_interestWaiter_3322_; uint8_t v_closed_3323_; lean_object* v_knownSize_3324_; lean_object* v_pendingIncompleteChunk_3325_; lean_object* v_closeError_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3367_; 
v___x_3318_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_3316_);
v___x_3319_ = lean_st_ref_get(v___y_3316_);
v_pendingProducer_3320_ = lean_ctor_get(v___x_3319_, 0);
v_pendingConsumer_3321_ = lean_ctor_get(v___x_3319_, 1);
v_interestWaiter_3322_ = lean_ctor_get(v___x_3319_, 2);
v_closed_3323_ = lean_ctor_get_uint8(v___x_3319_, sizeof(void*)*6);
v_knownSize_3324_ = lean_ctor_get(v___x_3319_, 3);
v_pendingIncompleteChunk_3325_ = lean_ctor_get(v___x_3319_, 4);
v_closeError_3326_ = lean_ctor_get(v___x_3319_, 5);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3328_ = v___x_3319_;
v_isShared_3329_ = v_isSharedCheck_3367_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_closeError_3326_);
lean_inc(v_pendingIncompleteChunk_3325_);
lean_inc(v_knownSize_3324_);
lean_inc(v_interestWaiter_3322_);
lean_inc(v_pendingConsumer_3321_);
lean_inc(v_pendingProducer_3320_);
lean_dec(v___x_3319_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3367_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___y_3331_; 
if (v_closed_3323_ == 0)
{
if (lean_obj_tag(v_pendingIncompleteChunk_3325_) == 0)
{
v___y_3331_ = v_chunk_3315_;
goto v___jp_3330_;
}
else
{
lean_object* v_val_3345_; lean_object* v_data_3346_; lean_object* v_extensions_3347_; lean_object* v_data_3348_; lean_object* v_extensions_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3365_; 
v_val_3345_ = lean_ctor_get(v_pendingIncompleteChunk_3325_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v_pendingIncompleteChunk_3325_, 1);
v_data_3346_ = lean_ctor_get(v_val_3345_, 0);
lean_inc_ref(v_data_3346_);
v_extensions_3347_ = lean_ctor_get(v_val_3345_, 1);
lean_inc_ref(v_extensions_3347_);
lean_dec(v_val_3345_);
v_data_3348_ = lean_ctor_get(v_chunk_3315_, 0);
v_extensions_3349_ = lean_ctor_get(v_chunk_3315_, 1);
v_isSharedCheck_3365_ = !lean_is_exclusive(v_chunk_3315_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3351_ = v_chunk_3315_;
v_isShared_3352_ = v_isSharedCheck_3365_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_extensions_3349_);
lean_inc(v_data_3348_);
lean_dec(v_chunk_3315_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3365_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_byte_array_size(v_data_3346_);
v___x_3355_ = lean_byte_array_size(v_data_3348_);
v___x_3356_ = lean_byte_array_copy_slice(v_data_3348_, v___x_3353_, v_data_3346_, v___x_3354_, v___x_3355_, v_closed_3323_);
lean_dec_ref(v_data_3348_);
v___x_3357_ = lean_array_get_size(v_extensions_3347_);
v___x_3358_ = lean_nat_dec_eq(v___x_3357_, v___x_3353_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3360_; 
lean_dec_ref(v_extensions_3349_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 1, v_extensions_3347_);
lean_ctor_set(v___x_3351_, 0, v___x_3356_);
v___x_3360_ = v___x_3351_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3356_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_extensions_3347_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
v___y_3331_ = v___x_3360_;
goto v___jp_3330_;
}
}
else
{
lean_object* v___x_3363_; 
lean_dec_ref(v_extensions_3347_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3356_);
v___x_3363_ = v___x_3351_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3356_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_extensions_3349_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
v___y_3331_ = v___x_3363_;
goto v___jp_3330_;
}
}
}
}
}
else
{
lean_object* v___x_3366_; 
lean_del_object(v___x_3328_);
lean_dec(v_closeError_3326_);
lean_dec(v_pendingIncompleteChunk_3325_);
lean_dec(v_knownSize_3324_);
lean_dec(v_interestWaiter_3322_);
lean_dec(v_pendingConsumer_3321_);
lean_dec(v_pendingProducer_3320_);
lean_dec_ref(v_chunk_3315_);
v___x_3366_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_3366_;
}
v___jp_3330_:
{
if (v_incomplete_3314_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3332_ = lean_box(0);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 4, v___x_3332_);
v___x_3334_ = v___x_3328_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_pendingProducer_3320_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_pendingConsumer_3321_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v_interestWaiter_3322_);
lean_ctor_set(v_reuseFailAlloc_3338_, 3, v_knownSize_3324_);
lean_ctor_set(v_reuseFailAlloc_3338_, 4, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3338_, 5, v_closeError_3326_);
lean_ctor_set_uint8(v_reuseFailAlloc_3338_, sizeof(void*)*6, v_closed_3323_);
v___x_3334_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = lean_st_ref_swap(v___y_3316_, v___x_3334_);
lean_dec(v___x_3335_);
v___x_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___y_3331_);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
return v___x_3337_;
}
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___y_3331_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 4, v___x_3339_);
v___x_3341_ = v___x_3328_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_pendingProducer_3320_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_pendingConsumer_3321_);
lean_ctor_set(v_reuseFailAlloc_3344_, 2, v_interestWaiter_3322_);
lean_ctor_set(v_reuseFailAlloc_3344_, 3, v_knownSize_3324_);
lean_ctor_set(v_reuseFailAlloc_3344_, 4, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3344_, 5, v_closeError_3326_);
lean_ctor_set_uint8(v_reuseFailAlloc_3344_, sizeof(void*)*6, v_closed_3323_);
v___x_3341_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = lean_st_ref_swap(v___y_3316_, v___x_3341_);
lean_dec(v___x_3342_);
v___x_3343_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
return v___x_3343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_incomplete_3368_, lean_object* v_chunk_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
uint8_t v_incomplete_boxed_3372_; lean_object* v_res_3373_; 
v_incomplete_boxed_3372_ = lean_unbox(v_incomplete_3368_);
v_res_3373_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_incomplete_boxed_3372_, v_chunk_3369_, v___y_3370_);
lean_dec(v___y_3370_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_3374_, lean_object* v_chunk_3375_, uint8_t v_incomplete_3376_){
_start:
{
lean_object* v___x_3378_; lean_object* v___f_3379_; lean_object* v___x_3380_; 
v___x_3378_ = lean_box(v_incomplete_3376_);
v___f_3379_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3379_, 0, v___x_3378_);
lean_closure_set(v___f_3379_, 1, v_chunk_3375_);
v___x_3380_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_3374_, v___f_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_3381_, lean_object* v_chunk_3382_, lean_object* v_incomplete_3383_, lean_object* v_a_3384_){
_start:
{
uint8_t v_incomplete_boxed_3385_; lean_object* v_res_3386_; 
v_incomplete_boxed_3385_ = lean_unbox(v_incomplete_3383_);
v_res_3386_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3381_, v_chunk_3382_, v_incomplete_boxed_3385_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_3393_){
_start:
{
if (lean_obj_tag(v_x_3393_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3403_; 
v_a_3395_ = lean_ctor_get(v_x_3393_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_x_3393_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3397_ = v_x_3393_;
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v_x_3393_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
return v___x_3401_;
}
}
}
else
{
lean_object* v___x_3404_; 
lean_dec_ref_known(v_x_3393_, 1);
v___x_3404_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_3404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_3405_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___3408_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___3411_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_3418_, lean_object* v_x_3419_){
_start:
{
if (lean_obj_tag(v_x_3419_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v___f_3418_);
v_a_3423_ = lean_ctor_get(v_x_3419_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_x_3419_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3425_ = v_x_3419_;
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v_x_3419_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
}
else
{
lean_object* v_a_3432_; 
v_a_3432_ = lean_ctor_get(v_x_3419_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v_x_3419_, 1);
if (lean_obj_tag(v_a_3432_) == 1)
{
lean_object* v_val_3433_; uint8_t v___x_3434_; 
v_val_3433_ = lean_ctor_get(v_a_3432_, 0);
lean_inc(v_val_3433_);
lean_dec_ref_known(v_a_3432_, 1);
v___x_3434_ = lean_unbox(v_val_3433_);
lean_dec(v_val_3433_);
if (v___x_3434_ == 1)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_apply_2(v___f_3418_, v___x_3435_, lean_box(0));
return v___x_3436_;
}
else
{
lean_dec_ref(v___f_3418_);
goto v___jp_3421_;
}
}
else
{
lean_dec(v_a_3432_);
lean_dec_ref(v___f_3418_);
goto v___jp_3421_;
}
}
v___jp_3421_:
{
lean_object* v___x_3422_; 
v___x_3422_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_3437_, lean_object* v_x_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_3437_, v_x_3438_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_3441_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v_a_3441_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_3443_, lean_object* v_x_3444_){
_start:
{
if (lean_obj_tag(v_x_3444_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3454_; 
v_a_3446_ = lean_ctor_get(v_x_3444_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_x_3444_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3448_ = v_x_3444_;
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v_x_3444_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
return v___x_3452_;
}
}
}
else
{
lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3465_; 
v_isSharedCheck_3465_ = !lean_is_exclusive(v_x_3444_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v_x_3444_, 0);
lean_dec(v_unused_3466_);
v___x_3456_ = v_x_3444_;
v_isShared_3457_ = v_isSharedCheck_3465_;
goto v_resetjp_3455_;
}
else
{
lean_dec(v_x_3444_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3465_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3458_ = lean_box(v___x_3443_);
v___x_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3459_);
v___x_3461_ = v___x_3456_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_3467_, lean_object* v_x_3468_, lean_object* v___y_3469_){
_start:
{
uint8_t v___x_5091__boxed_3470_; lean_object* v_res_3471_; 
v___x_5091__boxed_3470_ = lean_unbox(v___x_3467_);
v_res_3471_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5091__boxed_3470_, v_x_3468_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_3472_, lean_object* v_x_3473_){
_start:
{
if (lean_obj_tag(v_x_3473_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3483_; 
v_a_3475_ = lean_ctor_get(v_x_3473_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_x_3473_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3477_ = v_x_3473_;
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v_x_3473_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
}
}
else
{
lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3494_; 
v_isSharedCheck_3494_ = !lean_is_exclusive(v_x_3473_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; 
v_unused_3495_ = lean_ctor_get(v_x_3473_, 0);
lean_dec(v_unused_3495_);
v___x_3485_ = v_x_3473_;
v_isShared_3486_ = v_isSharedCheck_3494_;
goto v_resetjp_3484_;
}
else
{
lean_dec(v_x_3473_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3494_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
v___x_3487_ = lean_box(v_a_3472_);
v___x_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3488_);
v___x_3490_ = v___x_3485_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
return v___x_3492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_3496_, lean_object* v_x_3497_, lean_object* v___y_3498_){
_start:
{
uint8_t v_a_5143__boxed_3499_; lean_object* v_res_3500_; 
v_a_5143__boxed_3499_ = lean_unbox(v_a_3496_);
v_res_3500_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5143__boxed_3499_, v_x_3497_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_3501_, lean_object* v_interestWaiter_3502_, uint8_t v_closed_3503_, lean_object* v_knownSize_3504_, lean_object* v_pendingIncompleteChunk_3505_, lean_object* v_closeError_3506_, lean_object* v___y_3507_, lean_object* v_chunk_3508_, lean_object* v___f_3509_, lean_object* v_x_3510_){
_start:
{
if (lean_obj_tag(v_x_3510_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v___f_3509_);
lean_dec(v_closeError_3506_);
lean_dec(v_pendingIncompleteChunk_3505_);
lean_dec(v_knownSize_3504_);
lean_dec(v_interestWaiter_3502_);
lean_dec(v_pendingProducer_3501_);
v_a_3512_ = lean_ctor_get(v_x_3510_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_x_3510_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3514_ = v_x_3510_;
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v_x_3510_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; 
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
return v___x_3518_;
}
}
}
else
{
lean_object* v_a_3521_; uint8_t v___x_3522_; 
v_a_3521_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v_x_3510_, 1);
v___x_3522_ = lean_unbox(v_a_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___f_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; 
lean_dec_ref(v___f_3509_);
lean_inc(v_a_3521_);
v___f_3523_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3523_, 0, v_a_3521_);
v___x_3524_ = lean_box(0);
v___x_3525_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3525_, 0, v_pendingProducer_3501_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
lean_ctor_set(v___x_3525_, 2, v_interestWaiter_3502_);
lean_ctor_set(v___x_3525_, 3, v_knownSize_3504_);
lean_ctor_set(v___x_3525_, 4, v_pendingIncompleteChunk_3505_);
lean_ctor_set(v___x_3525_, 5, v_closeError_3506_);
lean_ctor_set_uint8(v___x_3525_, sizeof(void*)*6, v_closed_3503_);
v___x_3526_ = lean_unsigned_to_nat(0u);
v___x_3527_ = lean_st_ref_swap(v___y_3507_, v___x_3525_);
lean_dec(v___x_3527_);
v___x_3528_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3529_ = lean_unbox(v_a_3521_);
lean_dec(v_a_3521_);
v___x_3530_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3526_, v___x_3529_, v___x_3528_, v___f_3523_);
return v___x_3530_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec(v_a_3521_);
v___x_3531_ = lean_box(0);
v___x_3532_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_3504_, v_chunk_3508_);
v___x_3533_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3533_, 0, v_pendingProducer_3501_);
lean_ctor_set(v___x_3533_, 1, v___x_3531_);
lean_ctor_set(v___x_3533_, 2, v_interestWaiter_3502_);
lean_ctor_set(v___x_3533_, 3, v___x_3532_);
lean_ctor_set(v___x_3533_, 4, v_pendingIncompleteChunk_3505_);
lean_ctor_set(v___x_3533_, 5, v_closeError_3506_);
lean_ctor_set_uint8(v___x_3533_, sizeof(void*)*6, v_closed_3503_);
v___x_3534_ = lean_unsigned_to_nat(0u);
v___x_3535_ = lean_st_ref_swap(v___y_3507_, v___x_3533_);
lean_dec(v___x_3535_);
v___x_3536_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3537_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3534_, v_closed_3503_, v___x_3536_, v___f_3509_);
return v___x_3537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_3538_, lean_object* v_interestWaiter_3539_, lean_object* v_closed_3540_, lean_object* v_knownSize_3541_, lean_object* v_pendingIncompleteChunk_3542_, lean_object* v_closeError_3543_, lean_object* v___y_3544_, lean_object* v_chunk_3545_, lean_object* v___f_3546_, lean_object* v_x_3547_, lean_object* v___y_3548_){
_start:
{
uint8_t v_closed_boxed_3549_; lean_object* v_res_3550_; 
v_closed_boxed_3549_ = lean_unbox(v_closed_3540_);
v_res_3550_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_3538_, v_interestWaiter_3539_, v_closed_boxed_3549_, v_knownSize_3541_, v_pendingIncompleteChunk_3542_, v_closeError_3543_, v___y_3544_, v_chunk_3545_, v___f_3546_, v_x_3547_);
lean_dec_ref(v_chunk_3545_);
lean_dec(v___y_3544_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v___y_3569_, lean_object* v_chunk_3570_, lean_object* v_a_3571_, lean_object* v___f_3572_, lean_object* v_x_3573_){
_start:
{
if (lean_obj_tag(v_x_3573_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3583_; 
lean_dec_ref(v___f_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_chunk_3570_);
v_a_3575_ = lean_ctor_get(v_x_3573_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_x_3573_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3577_ = v_x_3573_;
v_isShared_3578_ = v_isSharedCheck_3583_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v_x_3573_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3583_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3637_; 
v_a_3584_ = lean_ctor_get(v_x_3573_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_x_3573_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3586_ = v_x_3573_;
v_isShared_3587_ = v_isSharedCheck_3637_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v_x_3573_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3637_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
uint8_t v_closed_3588_; 
v_closed_3588_ = lean_ctor_get_uint8(v_a_3584_, sizeof(void*)*6);
if (v_closed_3588_ == 0)
{
lean_object* v_pendingConsumer_3589_; 
v_pendingConsumer_3589_ = lean_ctor_get(v_a_3584_, 1);
lean_inc(v_pendingConsumer_3589_);
if (lean_obj_tag(v_pendingConsumer_3589_) == 1)
{
lean_object* v_pendingProducer_3590_; lean_object* v_interestWaiter_3591_; lean_object* v_knownSize_3592_; lean_object* v_pendingIncompleteChunk_3593_; lean_object* v_closeError_3594_; lean_object* v_val_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v___f_3572_);
lean_dec(v_a_3571_);
v_pendingProducer_3590_ = lean_ctor_get(v_a_3584_, 0);
lean_inc(v_pendingProducer_3590_);
v_interestWaiter_3591_ = lean_ctor_get(v_a_3584_, 2);
lean_inc(v_interestWaiter_3591_);
v_knownSize_3592_ = lean_ctor_get(v_a_3584_, 3);
lean_inc(v_knownSize_3592_);
v_pendingIncompleteChunk_3593_ = lean_ctor_get(v_a_3584_, 4);
lean_inc(v_pendingIncompleteChunk_3593_);
v_closeError_3594_ = lean_ctor_get(v_a_3584_, 5);
lean_inc(v_closeError_3594_);
lean_dec(v_a_3584_);
v_val_3595_ = lean_ctor_get(v_pendingConsumer_3589_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_pendingConsumer_3589_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3597_ = v_pendingConsumer_3589_;
v_isShared_3598_ = v_isSharedCheck_3614_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_val_3595_);
lean_dec(v_pendingConsumer_3589_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3614_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___f_3599_; lean_object* v___x_3600_; lean_object* v___f_3601_; lean_object* v___x_3603_; 
v___f_3599_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_3600_ = lean_box(v_closed_3588_);
lean_inc_ref(v_chunk_3570_);
lean_inc(v___y_3569_);
v___f_3601_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 11, 9);
lean_closure_set(v___f_3601_, 0, v_pendingProducer_3590_);
lean_closure_set(v___f_3601_, 1, v_interestWaiter_3591_);
lean_closure_set(v___f_3601_, 2, v___x_3600_);
lean_closure_set(v___f_3601_, 3, v_knownSize_3592_);
lean_closure_set(v___f_3601_, 4, v_pendingIncompleteChunk_3593_);
lean_closure_set(v___f_3601_, 5, v_closeError_3594_);
lean_closure_set(v___f_3601_, 6, v___y_3569_);
lean_closure_set(v___f_3601_, 7, v_chunk_3570_);
lean_closure_set(v___f_3601_, 8, v___f_3599_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v_chunk_3570_);
v___x_3603_ = v___x_3597_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_chunk_3570_);
v___x_3603_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3605_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3603_);
v___x_3605_ = v___x_3586_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; uint8_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3606_ = lean_unsigned_to_nat(0u);
v___x_3607_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_3595_, v___x_3605_);
lean_dec(v_val_3595_);
v___x_3608_ = lean_box(v___x_3607_);
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
v___x_3611_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3606_, v_closed_3588_, v___x_3610_, v___f_3601_);
return v___x_3611_;
}
}
}
}
else
{
lean_object* v_pendingProducer_3615_; 
lean_del_object(v___x_3586_);
v_pendingProducer_3615_ = lean_ctor_get(v_a_3584_, 0);
if (lean_obj_tag(v_pendingProducer_3615_) == 0)
{
lean_object* v_interestWaiter_3616_; lean_object* v_knownSize_3617_; lean_object* v_pendingIncompleteChunk_3618_; lean_object* v_closeError_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3632_; 
v_interestWaiter_3616_ = lean_ctor_get(v_a_3584_, 2);
v_knownSize_3617_ = lean_ctor_get(v_a_3584_, 3);
v_pendingIncompleteChunk_3618_ = lean_ctor_get(v_a_3584_, 4);
v_closeError_3619_ = lean_ctor_get(v_a_3584_, 5);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_a_3584_);
if (v_isSharedCheck_3632_ == 0)
{
lean_object* v_unused_3633_; lean_object* v_unused_3634_; 
v_unused_3633_ = lean_ctor_get(v_a_3584_, 1);
lean_dec(v_unused_3633_);
v_unused_3634_ = lean_ctor_get(v_a_3584_, 0);
lean_dec(v_unused_3634_);
v___x_3621_ = v_a_3584_;
v_isShared_3622_ = v_isSharedCheck_3632_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_closeError_3619_);
lean_inc(v_pendingIncompleteChunk_3618_);
lean_inc(v_knownSize_3617_);
lean_inc(v_interestWaiter_3616_);
lean_dec(v_a_3584_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3632_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v_chunk_3570_);
lean_ctor_set(v___x_3623_, 1, v_a_3571_);
v___x_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v___x_3624_);
v___x_3626_ = v___x_3621_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3624_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v_pendingConsumer_3589_);
lean_ctor_set(v_reuseFailAlloc_3631_, 2, v_interestWaiter_3616_);
lean_ctor_set(v_reuseFailAlloc_3631_, 3, v_knownSize_3617_);
lean_ctor_set(v_reuseFailAlloc_3631_, 4, v_pendingIncompleteChunk_3618_);
lean_ctor_set(v_reuseFailAlloc_3631_, 5, v_closeError_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3631_, sizeof(void*)*6, v_closed_3588_);
v___x_3626_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = lean_st_ref_swap(v___y_3569_, v___x_3626_);
lean_dec(v___x_3628_);
v___x_3629_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3630_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3627_, v_closed_3588_, v___x_3629_, v___f_3572_);
return v___x_3630_;
}
}
}
else
{
lean_object* v___x_3635_; 
lean_dec(v_pendingConsumer_3589_);
lean_dec(v_a_3584_);
lean_dec_ref(v___f_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_chunk_3570_);
v___x_3635_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_3635_;
}
}
}
else
{
lean_object* v___x_3636_; 
lean_del_object(v___x_3586_);
lean_dec(v_a_3584_);
lean_dec_ref(v___f_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_chunk_3570_);
v___x_3636_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_3636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v___y_3638_, lean_object* v_chunk_3639_, lean_object* v_a_3640_, lean_object* v___f_3641_, lean_object* v_x_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v___y_3638_, v_chunk_3639_, v_a_3640_, v___f_3641_, v_x_3642_);
lean_dec(v___y_3638_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_3645_, lean_object* v___f_3646_, lean_object* v_x_3647_){
_start:
{
if (lean_obj_tag(v_x_3647_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3657_; 
lean_dec_ref(v___f_3646_);
v_a_3649_ = lean_ctor_get(v_x_3647_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_x_3647_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3651_ = v_x_3647_;
v_isShared_3652_ = v_isSharedCheck_3657_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v_x_3647_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3657_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; 
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
}
}
else
{
lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3669_; 
v_isSharedCheck_3669_ = !lean_is_exclusive(v_x_3647_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; 
v_unused_3670_ = lean_ctor_get(v_x_3647_, 0);
lean_dec(v_unused_3670_);
v___x_3659_ = v_x_3647_;
v_isShared_3660_ = v_isSharedCheck_3669_;
goto v_resetjp_3658_;
}
else
{
lean_dec(v_x_3647_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3669_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; uint8_t v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
v___x_3661_ = lean_unsigned_to_nat(0u);
v___x_3662_ = 0;
v___x_3663_ = lean_st_ref_get(v___y_3645_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 0, v___x_3663_);
v___x_3665_ = v___x_3659_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
v___x_3667_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3661_, v___x_3662_, v___x_3666_, v___f_3646_);
return v___x_3667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_3671_, lean_object* v___f_3672_, lean_object* v_x_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_3671_, v___f_3672_, v_x_3673_);
lean_dec(v___y_3671_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_3676_, lean_object* v_a_3677_, lean_object* v___f_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v___f_3681_; lean_object* v___f_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
lean_inc_n(v___y_3679_, 2);
v___f_3681_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_3681_, 0, v___y_3679_);
lean_closure_set(v___f_3681_, 1, v_chunk_3676_);
lean_closure_set(v___f_3681_, 2, v_a_3677_);
lean_closure_set(v___f_3681_, 3, v___f_3678_);
v___f_3682_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_3682_, 0, v___y_3679_);
lean_closure_set(v___f_3682_, 1, v___f_3681_);
v___x_3683_ = lean_unsigned_to_nat(0u);
v___x_3684_ = 0;
v___x_3685_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3679_);
v___x_3686_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3683_, v___x_3684_, v___x_3685_, v___f_3682_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_3687_, lean_object* v_a_3688_, lean_object* v___f_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_3687_, v_a_3688_, v___f_3689_, v___y_3690_);
lean_dec(v___y_3690_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_3698_, lean_object* v___f_3699_, lean_object* v___f_3700_, lean_object* v_stream_3701_, lean_object* v_chunk_3702_, lean_object* v___f_3703_, lean_object* v_x_3704_){
_start:
{
if (lean_obj_tag(v_x_3704_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3714_; 
lean_dec_ref(v___f_3703_);
lean_dec_ref(v_chunk_3702_);
lean_dec_ref(v_stream_3701_);
lean_dec_ref(v___f_3700_);
lean_dec_ref(v___f_3699_);
v_a_3706_ = lean_ctor_get(v_x_3704_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_x_3704_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3708_ = v_x_3704_;
v_isShared_3709_ = v_isSharedCheck_3714_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v_x_3704_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3714_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
}
}
else
{
lean_object* v_a_3715_; 
v_a_3715_ = lean_ctor_get(v_x_3704_, 0);
lean_inc(v_a_3715_);
lean_dec_ref_known(v_x_3704_, 1);
if (lean_obj_tag(v_a_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v___f_3703_);
lean_dec_ref(v_chunk_3702_);
lean_dec_ref(v_stream_3701_);
lean_dec_ref(v___f_3700_);
lean_dec_ref(v___f_3699_);
v_a_3716_ = lean_ctor_get(v_a_3715_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v_a_3715_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3718_ = v_a_3715_;
v_isShared_3719_ = v_isSharedCheck_3724_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v_a_3715_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3724_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
return v___x_3722_;
}
}
}
else
{
lean_object* v_a_3725_; 
v_a_3725_ = lean_ctor_get(v_a_3715_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v_a_3715_, 1);
if (lean_obj_tag(v_a_3725_) == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
lean_dec_ref(v___f_3703_);
lean_dec_ref(v_chunk_3702_);
lean_dec_ref(v_stream_3701_);
v___x_3726_ = lean_io_promise_result_opt(v_a_3698_);
v___x_3727_ = lean_unsigned_to_nat(0u);
v___x_3728_ = 0;
v___x_3729_ = lean_task_map(v___f_3699_, v___x_3726_, v___x_3727_, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
v___x_3731_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3727_, v___x_3728_, v___x_3730_, v___f_3700_);
return v___x_3731_;
}
else
{
lean_object* v_val_3732_; uint8_t v___x_3733_; 
lean_dec_ref(v___f_3700_);
lean_dec_ref(v___f_3699_);
v_val_3732_ = lean_ctor_get(v_a_3725_, 0);
lean_inc(v_val_3732_);
lean_dec_ref_known(v_a_3725_, 1);
v___x_3733_ = lean_unbox(v_val_3732_);
lean_dec(v_val_3732_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; 
lean_dec_ref(v___f_3703_);
v___x_3734_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3701_, v_chunk_3702_);
return v___x_3734_;
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
lean_dec_ref(v_chunk_3702_);
lean_dec_ref(v_stream_3701_);
v___x_3735_ = lean_box(0);
v___x_3736_ = lean_apply_2(v___f_3703_, v___x_3735_, lean_box(0));
return v___x_3736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_3737_, lean_object* v___f_3738_, lean_object* v___f_3739_, lean_object* v_stream_3740_, lean_object* v_chunk_3741_, lean_object* v___f_3742_, lean_object* v_x_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_3737_, v___f_3738_, v___f_3739_, v_stream_3740_, v_chunk_3741_, v___f_3742_, v_x_3743_);
lean_dec(v_a_3737_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_3746_, lean_object* v___f_3747_, lean_object* v___f_3748_, lean_object* v___f_3749_, lean_object* v_stream_3750_, lean_object* v___f_3751_, lean_object* v_x_3752_){
_start:
{
if (lean_obj_tag(v_x_3752_) == 0)
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3762_; 
lean_dec_ref(v___f_3751_);
lean_dec_ref(v_stream_3750_);
lean_dec_ref(v___f_3749_);
lean_dec_ref(v___f_3748_);
lean_dec_ref(v___f_3747_);
lean_dec_ref(v_chunk_3746_);
v_a_3754_ = lean_ctor_get(v_x_3752_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_x_3752_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3756_ = v_x_3752_;
v_isShared_3757_ = v_isSharedCheck_3762_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v_x_3752_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3762_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
return v___x_3760_;
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___f_3764_; lean_object* v___f_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v_a_3763_ = lean_ctor_get(v_x_3752_, 0);
lean_inc_n(v_a_3763_, 2);
lean_dec_ref_known(v_x_3752_, 1);
lean_inc_ref(v_chunk_3746_);
v___f_3764_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_3764_, 0, v_chunk_3746_);
lean_closure_set(v___f_3764_, 1, v_a_3763_);
lean_closure_set(v___f_3764_, 2, v___f_3747_);
lean_inc_ref(v_stream_3750_);
v___f_3765_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3765_, 0, v_a_3763_);
lean_closure_set(v___f_3765_, 1, v___f_3748_);
lean_closure_set(v___f_3765_, 2, v___f_3749_);
lean_closure_set(v___f_3765_, 3, v_stream_3750_);
lean_closure_set(v___f_3765_, 4, v_chunk_3746_);
lean_closure_set(v___f_3765_, 5, v___f_3751_);
v___x_3766_ = lean_unsigned_to_nat(0u);
v___x_3767_ = 0;
v___x_3768_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3750_, v___f_3764_);
v___x_3769_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3766_, v___x_3767_, v___x_3768_, v___f_3765_);
return v___x_3769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_3770_, lean_object* v___f_3771_, lean_object* v___f_3772_, lean_object* v___f_3773_, lean_object* v_stream_3774_, lean_object* v___f_3775_, lean_object* v_x_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_3770_, v___f_3771_, v___f_3772_, v___f_3773_, v_stream_3774_, v___f_3775_, v_x_3776_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_3779_, lean_object* v_chunk_3780_){
_start:
{
lean_object* v___f_3782_; lean_object* v___f_3783_; lean_object* v___f_3784_; lean_object* v___f_3785_; lean_object* v___f_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___f_3782_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_3783_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_3784_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_3785_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_3786_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_3786_, 0, v_chunk_3780_);
lean_closure_set(v___f_3786_, 1, v___f_3782_);
lean_closure_set(v___f_3786_, 2, v___f_3785_);
lean_closure_set(v___f_3786_, 3, v___f_3784_);
lean_closure_set(v___f_3786_, 4, v_stream_3779_);
lean_closure_set(v___f_3786_, 5, v___f_3783_);
v___x_3787_ = lean_unsigned_to_nat(0u);
v___x_3788_ = 0;
v___x_3789_ = lean_io_promise_new();
v___x_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
v___x_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
v___x_3792_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3787_, v___x_3788_, v___x_3791_, v___f_3786_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_3793_, lean_object* v_chunk_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3793_, v_chunk_3794_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_3797_, lean_object* v_x_3798_){
_start:
{
if (lean_obj_tag(v_x_3798_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v_stream_3797_);
v_a_3800_ = lean_ctor_get(v_x_3798_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_x_3798_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3802_ = v_x_3798_;
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v_x_3798_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
return v___x_3806_;
}
}
}
else
{
lean_object* v_a_3809_; 
v_a_3809_ = lean_ctor_get(v_x_3798_, 0);
lean_inc(v_a_3809_);
lean_dec_ref_known(v_x_3798_, 1);
if (lean_obj_tag(v_a_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v_stream_3797_);
v_a_3810_ = lean_ctor_get(v_a_3809_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_a_3809_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3812_ = v_a_3809_;
v_isShared_3813_ = v_isSharedCheck_3818_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v_a_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3818_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
return v___x_3816_;
}
}
}
else
{
lean_object* v_a_3819_; 
v_a_3819_ = lean_ctor_get(v_a_3809_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v_a_3809_, 1);
if (lean_obj_tag(v_a_3819_) == 0)
{
lean_object* v___x_3820_; 
lean_dec_ref(v_stream_3797_);
v___x_3820_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3820_;
}
else
{
lean_object* v_val_3821_; uint8_t v___y_3823_; lean_object* v_data_3826_; lean_object* v_extensions_3827_; uint8_t v___x_3828_; 
v_val_3821_ = lean_ctor_get(v_a_3819_, 0);
lean_inc(v_val_3821_);
lean_dec_ref_known(v_a_3819_, 1);
v_data_3826_ = lean_ctor_get(v_val_3821_, 0);
v_extensions_3827_ = lean_ctor_get(v_val_3821_, 1);
v___x_3828_ = l_ByteArray_isEmpty(v_data_3826_);
if (v___x_3828_ == 0)
{
v___y_3823_ = v___x_3828_;
goto v___jp_3822_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v___x_3829_ = lean_array_get_size(v_extensions_3827_);
v___x_3830_ = lean_unsigned_to_nat(0u);
v___x_3831_ = lean_nat_dec_eq(v___x_3829_, v___x_3830_);
v___y_3823_ = v___x_3831_;
goto v___jp_3822_;
}
v___jp_3822_:
{
if (v___y_3823_ == 0)
{
lean_object* v___x_3824_; 
v___x_3824_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3797_, v_val_3821_);
return v___x_3824_;
}
else
{
lean_object* v___x_3825_; 
lean_dec(v_val_3821_);
lean_dec_ref(v_stream_3797_);
v___x_3825_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3825_;
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
lean_object* v___f_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_inc_ref(v_stream_3836_);
v___f_3840_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3840_, 0, v_stream_3836_);
v___x_3841_ = lean_unsigned_to_nat(0u);
v___x_3842_ = 0;
v___x_3843_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3836_, v_chunk_3837_, v_incomplete_3838_);
v___x_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3843_);
v___x_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
v___x_3846_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3841_, v___x_3842_, v___x_3845_, v___f_3840_);
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
lean_object* v___f_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___f_3879_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_3880_ = lean_unsigned_to_nat(0u);
v___x_3881_ = 0;
v___x_3882_ = lean_st_ref_get(v_a_3877_);
v___x_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
v___x_3885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3880_, v___x_3881_, v___x_3884_, v___f_3879_);
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
lean_object* v___f_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
lean_inc(v___y_3906_);
v___f_3908_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3908_, 0, v___y_3906_);
v___x_3909_ = lean_unsigned_to_nat(0u);
v___x_3910_ = 0;
v___x_3911_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3906_);
v___x_3912_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3909_, v___x_3910_, v___x_3911_, v___f_3908_);
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
uint8_t v___x_4067__boxed_3959_; lean_object* v_res_3960_; 
v___x_4067__boxed_3959_ = lean_unbox(v___x_3955_);
v_res_3960_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_3953_, v___y_3954_, v___x_4067__boxed_3959_, v_promise_3956_, v_x_3957_);
lean_dec(v_promise_3956_);
lean_dec(v___y_3954_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_3961_, lean_object* v_lose_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_finished_3965_; lean_object* v_promise_3966_; uint8_t v___x_3967_; lean_object* v___x_3968_; lean_object* v___f_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___y_3973_; uint8_t v___x_3981_; 
v_finished_3965_ = lean_ctor_get(v_w_3961_, 0);
lean_inc(v_finished_3965_);
v_promise_3966_ = lean_ctor_get(v_w_3961_, 1);
lean_inc(v_promise_3966_);
lean_dec_ref(v_w_3961_);
v___x_3967_ = 0;
v___x_3968_ = lean_box(v___x_3967_);
lean_inc(v___y_3963_);
v___f_3969_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3969_, 0, v_lose_3962_);
lean_closure_set(v___f_3969_, 1, v___y_3963_);
lean_closure_set(v___f_3969_, 2, v___x_3968_);
lean_closure_set(v___f_3969_, 3, v_promise_3966_);
v___x_3970_ = lean_unsigned_to_nat(0u);
v___x_3971_ = lean_st_ref_take(v_finished_3965_);
v___x_3981_ = lean_unbox(v___x_3971_);
lean_dec(v___x_3971_);
if (v___x_3981_ == 0)
{
uint8_t v___x_3982_; 
v___x_3982_ = 1;
v___y_3973_ = v___x_3982_;
goto v___jp_3972_;
}
else
{
v___y_3973_ = v___x_3967_;
goto v___jp_3972_;
}
v___jp_3972_:
{
uint8_t v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3974_ = 1;
v___x_3975_ = lean_box(v___x_3974_);
v___x_3976_ = lean_st_ref_put(v_finished_3965_, v___x_3975_);
lean_dec(v_finished_3965_);
v___x_3977_ = lean_box(v___y_3973_);
v___x_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
v___x_3980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3970_, v___x_3967_, v___x_3979_, v___f_3969_);
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
lean_object* v_finished_3992_; lean_object* v_promise_3993_; uint8_t v___x_3994_; lean_object* v___x_3995_; lean_object* v___f_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; uint8_t v___y_4001_; uint8_t v___x_4008_; 
v_finished_3992_ = lean_ctor_get(v_w_3988_, 0);
lean_inc(v_finished_3992_);
v_promise_3993_ = lean_ctor_get(v_w_3988_, 1);
lean_inc(v_promise_3993_);
lean_dec_ref(v_w_3988_);
v___x_3994_ = 1;
v___x_3995_ = lean_box(v___x_3994_);
lean_inc(v___y_3990_);
v___f_3996_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3996_, 0, v_lose_3989_);
lean_closure_set(v___f_3996_, 1, v___y_3990_);
lean_closure_set(v___f_3996_, 2, v___x_3995_);
lean_closure_set(v___f_3996_, 3, v_promise_3993_);
v___x_3997_ = lean_unsigned_to_nat(0u);
v___x_3998_ = 0;
v___x_3999_ = lean_st_ref_take(v_finished_3992_);
v___x_4008_ = lean_unbox(v___x_3999_);
lean_dec(v___x_3999_);
if (v___x_4008_ == 0)
{
v___y_4001_ = v___x_3994_;
goto v___jp_4000_;
}
else
{
v___y_4001_ = v___x_3998_;
goto v___jp_4000_;
}
v___jp_4000_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4002_ = lean_box(v___x_3994_);
v___x_4003_ = lean_st_ref_put(v_finished_3992_, v___x_4002_);
lean_dec(v_finished_3992_);
v___x_4004_ = lean_box(v___y_4001_);
v___x_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
v___x_4007_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3997_, v___x_3998_, v___x_4006_, v___f_3996_);
return v___x_4007_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_4009_, lean_object* v_lose_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_4009_, v_lose_4010_, v___y_4011_);
lean_dec(v___y_4011_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_4030_){
_start:
{
if (lean_obj_tag(v_x_4030_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4040_; 
v_a_4032_ = lean_ctor_get(v_x_4030_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_x_4030_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4034_ = v_x_4030_;
v_isShared_4035_ = v_isSharedCheck_4040_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v_x_4030_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4040_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; 
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
return v___x_4038_;
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v_pendingConsumer_4042_; 
v_a_4041_ = lean_ctor_get(v_x_4030_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v_x_4030_, 1);
v_pendingConsumer_4042_ = lean_ctor_get(v_a_4041_, 1);
if (lean_obj_tag(v_pendingConsumer_4042_) == 0)
{
uint8_t v_closed_4043_; 
v_closed_4043_ = lean_ctor_get_uint8(v_a_4041_, sizeof(void*)*6);
lean_dec(v_a_4041_);
if (v_closed_4043_ == 0)
{
lean_object* v___x_4044_; 
v___x_4044_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_4044_;
}
else
{
lean_object* v___x_4045_; 
v___x_4045_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_4045_;
}
}
else
{
lean_object* v___x_4046_; 
lean_dec(v_a_4041_);
v___x_4046_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_4046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_4047_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_4057_, lean_object* v___y_4058_, lean_object* v_x_4059_){
_start:
{
if (lean_obj_tag(v_x_4059_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4069_; 
lean_dec_ref(v_waiter_4057_);
v_a_4061_ = lean_ctor_get(v_x_4059_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v_x_4059_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4063_ = v_x_4059_;
v_isShared_4064_ = v_isSharedCheck_4069_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v_x_4059_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4069_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4067_; 
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
return v___x_4067_;
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v_pendingConsumer_4071_; 
v_a_4070_ = lean_ctor_get(v_x_4059_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v_x_4059_, 1);
v_pendingConsumer_4071_ = lean_ctor_get(v_a_4070_, 1);
lean_inc(v_pendingConsumer_4071_);
if (lean_obj_tag(v_pendingConsumer_4071_) == 0)
{
uint8_t v_closed_4072_; 
v_closed_4072_ = lean_ctor_get_uint8(v_a_4070_, sizeof(void*)*6);
if (v_closed_4072_ == 0)
{
lean_object* v_interestWaiter_4073_; 
v_interestWaiter_4073_ = lean_ctor_get(v_a_4070_, 2);
if (lean_obj_tag(v_interestWaiter_4073_) == 0)
{
lean_object* v_pendingProducer_4074_; lean_object* v_knownSize_4075_; lean_object* v_pendingIncompleteChunk_4076_; lean_object* v_closeError_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4087_; 
v_pendingProducer_4074_ = lean_ctor_get(v_a_4070_, 0);
v_knownSize_4075_ = lean_ctor_get(v_a_4070_, 3);
v_pendingIncompleteChunk_4076_ = lean_ctor_get(v_a_4070_, 4);
v_closeError_4077_ = lean_ctor_get(v_a_4070_, 5);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_a_4070_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; lean_object* v_unused_4089_; 
v_unused_4088_ = lean_ctor_get(v_a_4070_, 2);
lean_dec(v_unused_4088_);
v_unused_4089_ = lean_ctor_get(v_a_4070_, 1);
lean_dec(v_unused_4089_);
v___x_4079_ = v_a_4070_;
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_closeError_4077_);
lean_inc(v_pendingIncompleteChunk_4076_);
lean_inc(v_knownSize_4075_);
lean_inc(v_pendingProducer_4074_);
lean_dec(v_a_4070_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4081_, 0, v_waiter_4057_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 2, v___x_4081_);
v___x_4083_ = v___x_4079_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_pendingProducer_4074_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_pendingConsumer_4071_);
lean_ctor_set(v_reuseFailAlloc_4086_, 2, v___x_4081_);
lean_ctor_set(v_reuseFailAlloc_4086_, 3, v_knownSize_4075_);
lean_ctor_set(v_reuseFailAlloc_4086_, 4, v_pendingIncompleteChunk_4076_);
lean_ctor_set(v_reuseFailAlloc_4086_, 5, v_closeError_4077_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*6, v_closed_4072_);
v___x_4083_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = lean_st_ref_swap(v___y_4058_, v___x_4083_);
lean_dec(v___x_4084_);
v___x_4085_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4085_;
}
}
}
else
{
lean_object* v___x_4090_; 
lean_dec(v_a_4070_);
lean_dec_ref(v_waiter_4057_);
v___x_4090_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_4090_;
}
}
else
{
lean_object* v___f_4091_; lean_object* v___x_4092_; 
lean_dec(v_a_4070_);
v___f_4091_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4092_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_4057_, v___f_4091_, v___y_4058_);
return v___x_4092_;
}
}
else
{
lean_object* v___f_4093_; lean_object* v___x_4094_; 
lean_dec_ref_known(v_pendingConsumer_4071_, 1);
lean_dec(v_a_4070_);
v___f_4093_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4094_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_4057_, v___f_4093_, v___y_4058_);
return v___x_4094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_4095_, lean_object* v___y_4096_, lean_object* v_x_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_4095_, v___y_4096_, v_x_4097_);
lean_dec(v___y_4096_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_4100_, lean_object* v___f_4101_, lean_object* v_x_4102_){
_start:
{
if (lean_obj_tag(v_x_4102_) == 0)
{
lean_object* v___x_4104_; 
lean_dec_ref(v___f_4101_);
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v_x_4102_);
return v___x_4104_;
}
else
{
lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4116_; 
v_isSharedCheck_4116_ = !lean_is_exclusive(v_x_4102_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; 
v_unused_4117_ = lean_ctor_get(v_x_4102_, 0);
lean_dec(v_unused_4117_);
v___x_4106_ = v_x_4102_;
v_isShared_4107_ = v_isSharedCheck_4116_;
goto v_resetjp_4105_;
}
else
{
lean_dec(v_x_4102_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4116_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; uint8_t v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; 
v___x_4108_ = lean_unsigned_to_nat(0u);
v___x_4109_ = 0;
v___x_4110_ = lean_st_ref_get(v___y_4100_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4110_);
v___x_4112_ = v___x_4106_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4110_);
v___x_4112_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
v___x_4114_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4108_, v___x_4109_, v___x_4113_, v___f_4101_);
return v___x_4114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_4118_, lean_object* v___f_4119_, lean_object* v_x_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_4118_, v___f_4119_, v_x_4120_);
lean_dec(v___y_4118_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v___f_4126_; lean_object* v___f_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
lean_inc_n(v___y_4124_, 2);
v___f_4126_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_4126_, 0, v_waiter_4123_);
lean_closure_set(v___f_4126_, 1, v___y_4124_);
v___f_4127_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4127_, 0, v___y_4124_);
lean_closure_set(v___f_4127_, 1, v___f_4126_);
v___x_4128_ = lean_unsigned_to_nat(0u);
v___x_4129_ = 0;
v___x_4130_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4124_);
v___x_4131_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4128_, v___x_4129_, v___x_4130_, v___f_4127_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_4132_, v___y_4133_);
lean_dec(v___y_4133_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_4136_, lean_object* v_waiter_4137_){
_start:
{
lean_object* v___f_4139_; lean_object* v___x_4140_; 
v___f_4139_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4139_, 0, v_waiter_4137_);
v___x_4140_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_4136_, v___f_4139_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_4141_, lean_object* v_waiter_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_4141_, v_waiter_4142_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_4145_, lean_object* v___f_4146_, lean_object* v_x_4147_){
_start:
{
if (lean_obj_tag(v_x_4147_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4157_; 
lean_dec_ref(v___f_4146_);
v_a_4149_ = lean_ctor_get(v_x_4147_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v_x_4147_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4151_ = v_x_4147_;
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v_x_4147_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4155_; 
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
return v___x_4155_;
}
}
}
else
{
lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4169_; 
v_isSharedCheck_4169_ = !lean_is_exclusive(v_x_4147_);
if (v_isSharedCheck_4169_ == 0)
{
lean_object* v_unused_4170_; 
v_unused_4170_ = lean_ctor_get(v_x_4147_, 0);
lean_dec(v_unused_4170_);
v___x_4159_ = v_x_4147_;
v_isShared_4160_ = v_isSharedCheck_4169_;
goto v_resetjp_4158_;
}
else
{
lean_dec(v_x_4147_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4169_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4161_; uint8_t v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
v___x_4161_ = lean_unsigned_to_nat(0u);
v___x_4162_ = 0;
v___x_4163_ = lean_st_ref_get(v___y_4145_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 0, v___x_4163_);
v___x_4165_ = v___x_4159_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
v___x_4167_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4161_, v___x_4162_, v___x_4166_, v___f_4146_);
return v___x_4167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_4171_, lean_object* v___f_4172_, lean_object* v_x_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_4171_, v___f_4172_, v_x_4173_);
lean_dec(v___y_4171_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v___f_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_inc(v___y_4177_);
v___f_4179_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_4179_, 0, v___y_4177_);
lean_closure_set(v___f_4179_, 1, v___f_4176_);
v___x_4180_ = lean_unsigned_to_nat(0u);
v___x_4181_ = 0;
v___x_4182_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4177_);
v___x_4183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4180_, v___x_4181_, v___x_4182_, v___f_4179_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_4184_, v___y_4185_);
lean_dec(v___y_4185_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_4191_){
_start:
{
lean_object* v___f_4192_; lean_object* v___f_4193_; lean_object* v___f_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___f_4192_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_4191_, 2);
v___f_4193_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_4193_, 0, v_stream_4191_);
v___f_4194_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_4195_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4195_, 0, lean_box(0));
lean_closure_set(v___x_4195_, 1, lean_box(0));
lean_closure_set(v___x_4195_, 2, v_stream_4191_);
lean_closure_set(v___x_4195_, 3, v___f_4194_);
v___x_4196_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4196_, 0, lean_box(0));
lean_closure_set(v___x_4196_, 1, lean_box(0));
lean_closure_set(v___x_4196_, 2, v_stream_4191_);
lean_closure_set(v___x_4196_, 3, v___f_4192_);
v___x_4197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4195_);
lean_ctor_set(v___x_4197_, 1, v___f_4193_);
lean_ctor_set(v___x_4197_, 2, v___x_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v_x_4198_, lean_object* v_x_4199_){
_start:
{
if (lean_obj_tag(v_x_4199_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v_x_4198_);
v_a_4201_ = lean_ctor_get(v_x_4199_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_x_4199_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4203_ = v_x_4199_;
v_isShared_4204_ = v_isSharedCheck_4209_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v_x_4199_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4209_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4207_; 
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
}
}
else
{
lean_object* v___x_4210_; 
lean_dec_ref_known(v_x_4199_, 1);
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_x_4198_);
return v___x_4210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0___boxed(lean_object* v_x_4211_, lean_object* v_x_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_Std_Http_Body_stream___lam__0(v_x_4211_, v_x_4212_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_a_4215_, lean_object* v_x_4216_){
_start:
{
if (lean_obj_tag(v_x_4216_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4219_; 
v_a_4218_ = lean_ctor_get(v_x_4216_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v_x_4216_, 1);
v___x_4219_ = l_Std_Http_Body_Stream_closeWithError(v_a_4215_, v_a_4218_);
return v___x_4219_;
}
else
{
lean_object* v___x_4220_; 
lean_dec_ref(v_a_4215_);
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v_x_4216_);
return v___x_4220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_a_4221_, lean_object* v_x_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Std_Http_Body_stream___lam__1(v_a_4221_, v_x_4222_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v_a_4225_, lean_object* v_x_4226_){
_start:
{
if (lean_obj_tag(v_x_4226_) == 0)
{
lean_object* v___x_4228_; 
lean_dec_ref(v_a_4225_);
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v_x_4226_);
return v___x_4228_;
}
else
{
lean_object* v___x_4229_; 
lean_dec_ref_known(v_x_4226_, 1);
v___x_4229_ = l_Std_Http_Body_Stream_close(v_a_4225_);
return v___x_4229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v_a_4230_, lean_object* v_x_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Std_Http_Body_stream___lam__2(v_a_4230_, v_x_4231_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_gen_4234_, lean_object* v_a_4235_, lean_object* v___x_4236_, uint8_t v___x_4237_, lean_object* v___f_4238_, lean_object* v___f_4239_){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4241_ = lean_apply_2(v_gen_4234_, v_a_4235_, lean_box(0));
lean_inc(v___x_4236_);
v___x_4242_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4236_, v___x_4237_, v___x_4241_, v___f_4238_);
v___x_4243_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4236_, v___x_4237_, v___x_4242_, v___f_4239_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_gen_4244_, lean_object* v_a_4245_, lean_object* v___x_4246_, lean_object* v___x_4247_, lean_object* v___f_4248_, lean_object* v___f_4249_, lean_object* v___y_4250_){
_start:
{
uint8_t v___x_1066__boxed_4251_; lean_object* v_res_4252_; 
v___x_1066__boxed_4251_ = lean_unbox(v___x_4247_);
v_res_4252_ = l_Std_Http_Body_stream___lam__3(v_gen_4244_, v_a_4245_, v___x_4246_, v___x_1066__boxed_4251_, v___f_4248_, v___f_4249_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_4253_, lean_object* v_a_4254_, lean_object* v___f_4255_, lean_object* v___f_4256_, lean_object* v___f_4257_, lean_object* v_x_4258_){
_start:
{
if (lean_obj_tag(v_x_4258_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4268_; 
lean_dec_ref(v___f_4257_);
lean_dec_ref(v___f_4256_);
lean_dec_ref(v___f_4255_);
lean_dec_ref(v_a_4254_);
lean_dec_ref(v_gen_4253_);
v_a_4260_ = lean_ctor_get(v_x_4258_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v_x_4258_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4262_ = v_x_4258_;
v_isShared_4263_ = v_isSharedCheck_4268_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v_x_4258_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4268_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
lean_object* v___x_4266_; 
v___x_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4265_);
return v___x_4266_;
}
}
}
else
{
lean_object* v___x_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; lean_object* v___f_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
lean_dec_ref_known(v_x_4258_, 1);
v___x_4269_ = lean_unsigned_to_nat(0u);
v___x_4270_ = 0;
v___x_4271_ = lean_box(v___x_4270_);
v___f_4272_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 7, 6);
lean_closure_set(v___f_4272_, 0, v_gen_4253_);
lean_closure_set(v___f_4272_, 1, v_a_4254_);
lean_closure_set(v___f_4272_, 2, v___x_4269_);
lean_closure_set(v___f_4272_, 3, v___x_4271_);
lean_closure_set(v___f_4272_, 4, v___f_4255_);
lean_closure_set(v___f_4272_, 5, v___f_4256_);
v___x_4273_ = lean_io_as_task(v___f_4272_, v___x_4269_);
lean_dec_ref(v___x_4273_);
v___x_4274_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4275_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4269_, v___x_4270_, v___x_4274_, v___f_4257_);
return v___x_4275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_4276_, lean_object* v_a_4277_, lean_object* v___f_4278_, lean_object* v___f_4279_, lean_object* v___f_4280_, lean_object* v_x_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Std_Http_Body_stream___lam__4(v_gen_4276_, v_a_4277_, v___f_4278_, v___f_4279_, v___f_4280_, v_x_4281_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5(lean_object* v___x_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; lean_object* v_pendingProducer_4288_; lean_object* v_pendingConsumer_4289_; lean_object* v_interestWaiter_4290_; uint8_t v_closed_4291_; lean_object* v_pendingIncompleteChunk_4292_; lean_object* v_closeError_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4302_; 
v___x_4287_ = lean_st_ref_take(v___y_4285_);
v_pendingProducer_4288_ = lean_ctor_get(v___x_4287_, 0);
v_pendingConsumer_4289_ = lean_ctor_get(v___x_4287_, 1);
v_interestWaiter_4290_ = lean_ctor_get(v___x_4287_, 2);
v_closed_4291_ = lean_ctor_get_uint8(v___x_4287_, sizeof(void*)*6);
v_pendingIncompleteChunk_4292_ = lean_ctor_get(v___x_4287_, 4);
v_closeError_4293_ = lean_ctor_get(v___x_4287_, 5);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4302_ == 0)
{
lean_object* v_unused_4303_; 
v_unused_4303_ = lean_ctor_get(v___x_4287_, 3);
lean_dec(v_unused_4303_);
v___x_4295_ = v___x_4287_;
v_isShared_4296_ = v_isSharedCheck_4302_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_closeError_4293_);
lean_inc(v_pendingIncompleteChunk_4292_);
lean_inc(v_interestWaiter_4290_);
lean_inc(v_pendingConsumer_4289_);
lean_inc(v_pendingProducer_4288_);
lean_dec(v___x_4287_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4302_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 3, v___x_4284_);
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_pendingProducer_4288_);
lean_ctor_set(v_reuseFailAlloc_4301_, 1, v_pendingConsumer_4289_);
lean_ctor_set(v_reuseFailAlloc_4301_, 2, v_interestWaiter_4290_);
lean_ctor_set(v_reuseFailAlloc_4301_, 3, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4301_, 4, v_pendingIncompleteChunk_4292_);
lean_ctor_set(v_reuseFailAlloc_4301_, 5, v_closeError_4293_);
lean_ctor_set_uint8(v_reuseFailAlloc_4301_, sizeof(void*)*6, v_closed_4291_);
v___x_4298_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = lean_st_ref_put(v___y_4285_, v___x_4298_);
v___x_4300_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object* v___x_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l_Std_Http_Body_stream___lam__5(v___x_4304_, v___y_4305_);
lean_dec(v___y_4305_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6(lean_object* v_gen_4312_, lean_object* v_x_4313_){
_start:
{
if (lean_obj_tag(v_x_4313_) == 0)
{
lean_object* v___x_4315_; 
lean_dec_ref(v_gen_4312_);
v___x_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4315_, 0, v_x_4313_);
return v___x_4315_;
}
else
{
lean_object* v_a_4316_; lean_object* v___f_4317_; lean_object* v___f_4318_; lean_object* v___f_4319_; lean_object* v___f_4320_; lean_object* v___f_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v_a_4316_ = lean_ctor_get(v_x_4313_, 0);
lean_inc_n(v_a_4316_, 4);
v___f_4317_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4317_, 0, v_x_4313_);
v___f_4318_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4318_, 0, v_a_4316_);
v___f_4319_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4319_, 0, v_a_4316_);
v___f_4320_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 7, 5);
lean_closure_set(v___f_4320_, 0, v_gen_4312_);
lean_closure_set(v___f_4320_, 1, v_a_4316_);
lean_closure_set(v___f_4320_, 2, v___f_4319_);
lean_closure_set(v___f_4320_, 3, v___f_4318_);
lean_closure_set(v___f_4320_, 4, v___f_4317_);
v___f_4321_ = ((lean_object*)(l_Std_Http_Body_stream___lam__6___closed__1));
v___x_4322_ = lean_unsigned_to_nat(0u);
v___x_4323_ = 0;
v___x_4324_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4316_, v___f_4321_);
v___x_4325_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4322_, v___x_4323_, v___x_4324_, v___f_4320_);
return v___x_4325_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object* v_gen_4326_, lean_object* v_x_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Std_Http_Body_stream___lam__6(v_gen_4326_, v_x_4327_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object* v_gen_4330_){
_start:
{
lean_object* v___f_4332_; lean_object* v___x_4333_; uint8_t v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___f_4332_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4332_, 0, v_gen_4330_);
v___x_4333_ = lean_unsigned_to_nat(0u);
v___x_4334_ = 0;
v___x_4335_ = l_Std_Http_Body_mkStream();
v___x_4336_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4333_, v___x_4334_, v___x_4335_, v___f_4332_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_4337_, lean_object* v_a_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Std_Http_Body_stream(v_gen_4337_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v___x_4340_, lean_object* v_content_4341_, lean_object* v_s_4342_, lean_object* v_x_4343_){
_start:
{
if (lean_obj_tag(v_x_4343_) == 0)
{
lean_object* v___x_4345_; 
lean_dec_ref(v_s_4342_);
lean_dec_ref(v_content_4341_);
v___x_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4345_, 0, v_x_4343_);
return v___x_4345_;
}
else
{
lean_object* v___x_4346_; uint8_t v___x_4347_; 
lean_dec_ref_known(v_x_4343_, 1);
v___x_4346_ = lean_unsigned_to_nat(0u);
v___x_4347_ = lean_nat_dec_lt(v___x_4346_, v___x_4340_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4348_; 
lean_dec_ref(v_s_4342_);
lean_dec_ref(v_content_4341_);
v___x_4348_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4348_;
}
else
{
lean_object* v___x_4349_; uint8_t v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = l_Std_Http_Chunk_ofByteArray(v_content_4341_);
v___x_4350_ = 0;
v___x_4351_ = l_Std_Http_Body_Stream_send(v_s_4342_, v___x_4349_, v___x_4350_);
return v___x_4351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v___x_4352_, lean_object* v_content_4353_, lean_object* v_s_4354_, lean_object* v_x_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_Std_Http_Body_fromBytes___lam__0(v___x_4352_, v_content_4353_, v_s_4354_, v_x_4355_);
lean_dec(v___x_4352_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object* v_content_4358_, lean_object* v_s_4359_){
_start:
{
lean_object* v___x_4361_; lean_object* v___f_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___f_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4361_ = lean_byte_array_size(v_content_4358_);
lean_inc_ref(v_s_4359_);
v___f_4362_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4362_, 0, v___x_4361_);
lean_closure_set(v___f_4362_, 1, v_content_4358_);
lean_closure_set(v___f_4362_, 2, v_s_4359_);
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4361_);
v___x_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
v___f_4365_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4365_, 0, v___x_4364_);
v___x_4366_ = lean_unsigned_to_nat(0u);
v___x_4367_ = 0;
v___x_4368_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_4359_, v___f_4365_);
v___x_4369_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4366_, v___x_4367_, v___x_4368_, v___f_4362_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object* v_content_4370_, lean_object* v_s_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Std_Http_Body_fromBytes___lam__2(v_content_4370_, v_s_4371_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_4374_){
_start:
{
lean_object* v___f_4376_; lean_object* v___x_4377_; 
v___f_4376_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4376_, 0, v_content_4374_);
v___x_4377_ = l_Std_Http_Body_stream(v___f_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_4378_, lean_object* v_a_4379_){
_start:
{
lean_object* v_res_4380_; 
v_res_4380_ = l_Std_Http_Body_fromBytes(v_content_4378_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1(lean_object* v_a_4381_, lean_object* v___f_4382_, lean_object* v_x_4383_){
_start:
{
if (lean_obj_tag(v_x_4383_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4393_; 
lean_dec_ref(v___f_4382_);
lean_dec_ref(v_a_4381_);
v_a_4385_ = lean_ctor_get(v_x_4383_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v_x_4383_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4387_ = v_x_4383_;
v_isShared_4388_ = v_isSharedCheck_4393_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v_x_4383_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4393_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; 
v___x_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
return v___x_4391_;
}
}
}
else
{
lean_object* v___x_4394_; uint8_t v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
lean_dec_ref_known(v_x_4383_, 1);
v___x_4394_ = lean_unsigned_to_nat(0u);
v___x_4395_ = 0;
v___x_4396_ = l_Std_Http_Body_Stream_close(v_a_4381_);
v___x_4397_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4394_, v___x_4395_, v___x_4396_, v___f_4382_);
return v___x_4397_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1___boxed(lean_object* v_a_4398_, lean_object* v___f_4399_, lean_object* v_x_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Std_Http_Body_empty___lam__1(v_a_4398_, v___f_4399_, v_x_4400_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_x_4409_){
_start:
{
if (lean_obj_tag(v_x_4409_) == 0)
{
lean_object* v___x_4411_; 
v___x_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4411_, 0, v_x_4409_);
return v___x_4411_;
}
else
{
lean_object* v_a_4412_; lean_object* v___f_4413_; lean_object* v___f_4414_; lean_object* v___x_4415_; lean_object* v___f_4416_; uint8_t v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v_a_4412_ = lean_ctor_get(v_x_4409_, 0);
lean_inc_n(v_a_4412_, 2);
v___f_4413_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4413_, 0, v_x_4409_);
v___f_4414_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4414_, 0, v_a_4412_);
lean_closure_set(v___f_4414_, 1, v___f_4413_);
v___x_4415_ = lean_unsigned_to_nat(0u);
v___f_4416_ = ((lean_object*)(l_Std_Http_Body_empty___lam__2___closed__2));
v___x_4417_ = 0;
v___x_4418_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4412_, v___f_4416_);
v___x_4419_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4415_, v___x_4417_, v___x_4418_, v___f_4414_);
return v___x_4419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_x_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Std_Http_Body_empty___lam__2(v_x_4420_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___f_4425_; lean_object* v___x_4426_; uint8_t v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___f_4425_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_4426_ = lean_unsigned_to_nat(0u);
v___x_4427_ = 0;
v___x_4428_ = l_Std_Http_Body_mkStream();
v___x_4429_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4426_, v___x_4427_, v___x_4428_, v___f_4425_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Std_Http_Body_empty();
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_4454_, lean_object* v_f_4455_){
_start:
{
lean_object* v_line_4456_; lean_object* v_body_4457_; lean_object* v_extensions_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4466_; 
v_line_4456_ = lean_ctor_get(v_f_4455_, 0);
v_body_4457_ = lean_ctor_get(v_f_4455_, 1);
v_extensions_4458_ = lean_ctor_get(v_f_4455_, 2);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_f_4455_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4460_ = v_f_4455_;
v_isShared_4461_ = v_isSharedCheck_4466_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_extensions_4458_);
lean_inc(v_body_4457_);
lean_inc(v_line_4456_);
lean_dec(v_f_4455_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4466_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4462_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4454_, v_body_4457_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 1, v___x_4462_);
v___x_4464_ = v___x_4460_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_line_4456_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v___x_4462_);
lean_ctor_set(v_reuseFailAlloc_4465_, 2, v_extensions_4458_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_4470_, lean_object* v_x_4471_){
_start:
{
if (lean_obj_tag(v_x_4471_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4481_; 
lean_dec_ref(v___x_4470_);
v_a_4473_ = lean_ctor_get(v_x_4471_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v_x_4471_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4475_ = v_x_4471_;
v_isShared_4476_ = v_isSharedCheck_4481_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v_x_4471_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4481_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
lean_object* v___x_4479_; 
v___x_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
return v___x_4479_;
}
}
}
else
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4501_; 
v_a_4482_ = lean_ctor_get(v_x_4471_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_x_4471_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4484_ = v_x_4471_;
v_isShared_4485_ = v_isSharedCheck_4501_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v_x_4471_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4501_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v_line_4486_; lean_object* v_body_4487_; lean_object* v_extensions_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4500_; 
v_line_4486_ = lean_ctor_get(v_a_4482_, 0);
v_body_4487_ = lean_ctor_get(v_a_4482_, 1);
v_extensions_4488_ = lean_ctor_get(v_a_4482_, 2);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_a_4482_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4490_ = v_a_4482_;
v_isShared_4491_ = v_isSharedCheck_4500_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_extensions_4488_);
lean_inc(v_body_4487_);
lean_inc(v_line_4486_);
lean_dec(v_a_4482_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4500_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4492_; lean_object* v___x_4494_; 
v___x_4492_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4470_, v_body_4487_);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 1, v___x_4492_);
v___x_4494_ = v___x_4490_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_line_4486_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v___x_4492_);
lean_ctor_set(v_reuseFailAlloc_4499_, 2, v_extensions_4488_);
v___x_4494_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4496_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4494_);
v___x_4496_ = v___x_4484_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4494_);
v___x_4496_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4497_; 
v___x_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
return v___x_4497_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_4502_, lean_object* v_x_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_4502_, v_x_4503_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_4506_, lean_object* v_action_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v___x_4510_; uint8_t v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4510_ = lean_unsigned_to_nat(0u);
v___x_4511_ = 0;
lean_inc_ref(v___y_4508_);
v___x_4512_ = lean_apply_2(v_action_4507_, v___y_4508_, lean_box(0));
v___x_4513_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4510_, v___x_4511_, v___x_4512_, v___f_4506_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_4514_, lean_object* v_action_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_4514_, v_action_4515_, v___y_4516_);
lean_dec_ref(v___y_4516_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_4524_, lean_object* v_action_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v___x_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4528_ = lean_unsigned_to_nat(0u);
v___x_4529_ = 0;
v___x_4530_ = lean_apply_1(v_action_4525_, lean_box(0));
v___x_4531_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4528_, v___x_4529_, v___x_4530_, v___f_4524_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_4532_, lean_object* v_action_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_4532_, v_action_4533_, v___y_4534_);
lean_dec_ref(v___y_4534_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_4540_, lean_object* v_x_4541_){
_start:
{
if (lean_obj_tag(v_x_4541_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4551_; 
v_a_4543_ = lean_ctor_get(v_x_4541_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v_x_4541_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4545_ = v_x_4541_;
v_isShared_4546_ = v_isSharedCheck_4551_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v_x_4541_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4551_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
lean_object* v___x_4549_; 
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
return v___x_4549_;
}
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4561_; 
v_a_4552_ = lean_ctor_get(v_x_4541_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_x_4541_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4554_ = v_x_4541_;
v_isShared_4555_ = v_isSharedCheck_4561_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v_x_4541_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4561_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4556_; lean_object* v___x_4558_; 
v___x_4556_ = l_Std_Http_Request_Builder_body___redArg(v_builder_4540_, v_a_4552_);
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 0, v___x_4556_);
v___x_4558_ = v___x_4554_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
lean_object* v___x_4559_; 
v___x_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
return v___x_4559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_4562_, lean_object* v_x_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_4562_, v_x_4563_);
lean_dec_ref(v_builder_4562_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_4566_, lean_object* v_gen_4567_){
_start:
{
lean_object* v___f_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___f_4569_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4569_, 0, v_builder_4566_);
v___x_4570_ = lean_unsigned_to_nat(0u);
v___x_4571_ = 0;
v___x_4572_ = l_Std_Http_Body_stream(v_gen_4567_);
v___x_4573_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4570_, v___x_4571_, v___x_4572_, v___f_4569_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_4574_, lean_object* v_gen_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Std_Http_Request_Builder_stream(v_builder_4574_, v_gen_4575_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_4578_, lean_object* v_x_4579_){
_start:
{
if (lean_obj_tag(v_x_4579_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4589_; 
v_a_4581_ = lean_ctor_get(v_x_4579_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v_x_4579_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4583_ = v_x_4579_;
v_isShared_4584_ = v_isSharedCheck_4589_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v_x_4579_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4589_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4581_);
v___x_4586_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
lean_object* v___x_4587_; 
v___x_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
return v___x_4587_;
}
}
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4599_; 
v_a_4590_ = lean_ctor_get(v_x_4579_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_x_4579_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4592_ = v_x_4579_;
v_isShared_4593_ = v_isSharedCheck_4599_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v_x_4579_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4599_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4594_; lean_object* v___x_4596_; 
v___x_4594_ = l_Std_Http_Response_Builder_body___redArg(v_builder_4578_, v_a_4590_);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4594_);
v___x_4596_ = v___x_4592_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4594_);
v___x_4596_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
return v___x_4597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_4600_, lean_object* v_x_4601_, lean_object* v___y_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_4600_, v_x_4601_);
lean_dec_ref(v_builder_4600_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_4604_, lean_object* v_gen_4605_){
_start:
{
lean_object* v___f_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___f_4607_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4607_, 0, v_builder_4604_);
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = 0;
v___x_4610_ = l_Std_Http_Body_stream(v_gen_4605_);
v___x_4611_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4608_, v___x_4609_, v___x_4610_, v___f_4607_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_4612_, lean_object* v_gen_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_Std_Http_Response_Builder_stream(v_builder_4612_, v_gen_4613_);
return v_res_4615_;
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

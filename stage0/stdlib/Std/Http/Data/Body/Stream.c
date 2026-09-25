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
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_recv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_instNextChunkAsync___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_Stream_instNextChunkAsync = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0_value),((lean_object*)&l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1_value),((lean_object*)&l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2_value)} };
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0(lean_object* v_step_2678_, lean_object* v_acc_2679_, lean_object* v_x_2680_){
_start:
{
if (lean_obj_tag(v_x_2680_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v_acc_2679_);
lean_dec_ref(v_step_2678_);
v_a_2682_ = lean_ctor_get(v_x_2680_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_x_2680_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2684_ = v_x_2680_;
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v_x_2680_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
return v___x_2688_;
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2702_; 
v_a_2691_ = lean_ctor_get(v_x_2680_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_x_2680_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2693_ = v_x_2680_;
v_isShared_2694_ = v_isSharedCheck_2702_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v_x_2680_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2702_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
if (lean_obj_tag(v_a_2691_) == 1)
{
lean_object* v_val_2695_; lean_object* v___x_2696_; 
lean_del_object(v___x_2693_);
v_val_2695_ = lean_ctor_get(v_a_2691_, 0);
lean_inc(v_val_2695_);
lean_dec_ref_known(v_a_2691_, 1);
v___x_2696_ = lean_apply_3(v_step_2678_, v_val_2695_, v_acc_2679_, lean_box(0));
return v___x_2696_;
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_dec(v_a_2691_);
lean_dec_ref(v_step_2678_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_acc_2679_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2697_);
v___x_2699_ = v___x_2693_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed(lean_object* v_step_2703_, lean_object* v_acc_2704_, lean_object* v_x_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Std_Http_Body_Stream_forIn___redArg___lam__0(v_step_2703_, v_acc_2704_, v_x_2705_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1(lean_object* v_step_2708_, lean_object* v_stream_2709_, lean_object* v_x_2710_, lean_object* v_acc_2711_){
_start:
{
lean_object* v___f_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___f_2713_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2713_, 0, v_step_2708_);
lean_closure_set(v___f_2713_, 1, v_acc_2711_);
v___x_2714_ = lean_unsigned_to_nat(0u);
v___x_2715_ = 0;
v___x_2716_ = l_Std_Http_Body_Stream_recv(v_stream_2709_);
v___x_2717_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2714_, v___x_2715_, v___x_2716_, v___f_2713_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed(lean_object* v_step_2718_, lean_object* v_stream_2719_, lean_object* v_x_2720_, lean_object* v_acc_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Std_Http_Body_Stream_forIn___redArg___lam__1(v_step_2718_, v_stream_2719_, v_x_2720_, v_acc_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2(lean_object* v_a_2724_, lean_object* v_x_2725_){
_start:
{
if (lean_obj_tag(v_x_2725_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2735_; 
v_a_2727_ = lean_ctor_get(v_x_2725_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_x_2725_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2729_ = v_x_2725_;
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v_x_2725_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
}
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec_ref_known(v_x_2725_, 1);
v___x_2736_ = l_IO_Promise_result_x21___redArg(v_a_2724_);
v___x_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed(lean_object* v_a_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Std_Http_Body_Stream_forIn___redArg___lam__2(v_a_2738_, v_x_2739_);
lean_dec(v_a_2738_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3(lean_object* v___f_2742_, lean_object* v___x_2743_, lean_object* v_acc_2744_, lean_object* v_x_2745_){
_start:
{
if (lean_obj_tag(v_x_2745_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_acc_2744_);
lean_dec(v___x_2743_);
lean_dec_ref(v___f_2742_);
v_a_2747_ = lean_ctor_get(v_x_2745_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_x_2745_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2749_ = v_x_2745_;
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v_x_2745_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2768_; 
v_a_2756_ = lean_ctor_get(v_x_2745_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_x_2745_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2758_ = v_x_2745_;
v_isShared_2759_ = v_isSharedCheck_2768_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v_x_2745_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2768_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___f_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
lean_inc(v_a_2756_);
v___f_2760_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2760_, 0, v_a_2756_);
v___x_2761_ = 0;
lean_inc(v___x_2743_);
v___x_2762_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_2742_, v___x_2743_, v_a_2756_, v_acc_2744_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2762_);
v___x_2764_ = v___x_2758_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
v___x_2766_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2743_, v___x_2761_, v___x_2765_, v___f_2760_);
return v___x_2766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed(lean_object* v___f_2769_, lean_object* v___x_2770_, lean_object* v_acc_2771_, lean_object* v_x_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Std_Http_Body_Stream_forIn___redArg___lam__3(v___f_2769_, v___x_2770_, v_acc_2771_, v_x_2772_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_2775_, lean_object* v_acc_2776_, lean_object* v_step_2777_){
_start:
{
lean_object* v___f_2779_; lean_object* v___x_2780_; lean_object* v___f_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___f_2779_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2779_, 0, v_step_2777_);
lean_closure_set(v___f_2779_, 1, v_stream_2775_);
v___x_2780_ = lean_unsigned_to_nat(0u);
v___f_2781_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2781_, 0, v___f_2779_);
lean_closure_set(v___f_2781_, 1, v___x_2780_);
lean_closure_set(v___f_2781_, 2, v_acc_2776_);
v___x_2782_ = 0;
v___x_2783_ = lean_io_promise_new();
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
v___x_2786_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2780_, v___x_2782_, v___x_2785_, v___f_2781_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_2787_, lean_object* v_acc_2788_, lean_object* v_step_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_2787_, v_acc_2788_, v_step_2789_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_2792_, lean_object* v_stream_2793_, lean_object* v_acc_2794_, lean_object* v_step_2795_){
_start:
{
lean_object* v___f_2797_; lean_object* v___x_2798_; lean_object* v___f_2799_; uint8_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___f_2797_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2797_, 0, v_step_2795_);
lean_closure_set(v___f_2797_, 1, v_stream_2793_);
v___x_2798_ = lean_unsigned_to_nat(0u);
v___f_2799_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2799_, 0, v___f_2797_);
lean_closure_set(v___f_2799_, 1, v___x_2798_);
lean_closure_set(v___f_2799_, 2, v_acc_2794_);
v___x_2800_ = 0;
v___x_2801_ = lean_io_promise_new();
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
v___x_2804_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2798_, v___x_2800_, v___x_2803_, v___f_2799_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_2805_, lean_object* v_stream_2806_, lean_object* v_acc_2807_, lean_object* v_step_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_2805_, v_stream_2806_, v_acc_2807_, v_step_2808_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___y_2811_);
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0___boxed(lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(v___y_2815_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(lean_object* v_x_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1___boxed(lean_object* v_x_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(v_x_2821_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(lean_object* v_x_2824_){
_start:
{
if (lean_obj_tag(v_x_2824_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2834_; 
v_a_2826_ = lean_ctor_get(v_x_2824_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_x_2824_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2828_ = v_x_2824_;
v_isShared_2829_ = v_isSharedCheck_2834_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v_x_2824_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2834_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
return v___x_2832_;
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2845_; 
v_a_2835_ = lean_ctor_get(v_x_2824_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_x_2824_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2837_ = v_x_2824_;
v_isShared_2838_ = v_isSharedCheck_2845_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v_x_2824_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2845_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v_token_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v_token_2839_ = lean_ctor_get(v_a_2835_, 1);
lean_inc_ref(v_token_2839_);
lean_dec(v_a_2835_);
v___x_2840_ = l_Std_CancellationToken_selector(v_token_2839_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2840_);
v___x_2842_ = v___x_2837_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2___boxed(lean_object* v_x_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(v_x_2846_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(lean_object* v_step_2849_, lean_object* v_b_2850_, lean_object* v_a_2851_, lean_object* v_x_2852_){
_start:
{
if (lean_obj_tag(v_x_2852_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_b_2850_);
lean_dec_ref(v_step_2849_);
v_a_2854_ = lean_ctor_get(v_x_2852_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2856_ = v_x_2852_;
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v_x_2852_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2874_; 
v_a_2863_ = lean_ctor_get(v_x_2852_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2865_ = v_x_2852_;
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v_x_2852_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
if (lean_obj_tag(v_a_2863_) == 1)
{
lean_object* v_val_2867_; lean_object* v___x_2868_; 
lean_del_object(v___x_2865_);
v_val_2867_ = lean_ctor_get(v_a_2863_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v_a_2863_, 1);
lean_inc_ref(v_a_2851_);
v___x_2868_ = lean_apply_4(v_step_2849_, v_val_2867_, v_b_2850_, v_a_2851_, lean_box(0));
return v___x_2868_;
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2871_; 
lean_dec(v_a_2863_);
lean_dec_ref(v_step_2849_);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v_b_2850_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2869_);
v___x_2871_ = v___x_2865_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed(lean_object* v_step_2875_, lean_object* v_b_2876_, lean_object* v_a_2877_, lean_object* v_x_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(v_step_2875_, v_b_2876_, v_a_2877_, v_x_2878_);
lean_dec_ref(v_a_2877_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(lean_object* v_stream_2881_, lean_object* v___f_2882_, lean_object* v___f_2883_, lean_object* v___f_2884_, lean_object* v_x_2885_){
_start:
{
if (lean_obj_tag(v_x_2885_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v___f_2884_);
lean_dec_ref(v___f_2883_);
lean_dec_ref(v___f_2882_);
lean_dec_ref(v_stream_2881_);
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
lean_object* v_a_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_a_2896_ = lean_ctor_get(v_x_2885_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v_x_2885_, 1);
v___x_2897_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2881_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
lean_ctor_set(v___x_2898_, 1, v___f_2882_);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v_a_2896_);
lean_ctor_set(v___x_2899_, 1, v___f_2883_);
v___x_2900_ = lean_unsigned_to_nat(2u);
v___x_2901_ = lean_mk_empty_array_with_capacity(v___x_2900_);
v___x_2902_ = lean_array_push(v___x_2901_, v___x_2898_);
v___x_2903_ = lean_array_push(v___x_2902_, v___x_2899_);
v___x_2904_ = lean_unsigned_to_nat(0u);
v___x_2905_ = 0;
v___x_2906_ = l_Std_Async_Selectable_one___redArg(v___x_2903_);
v___x_2907_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2904_, v___x_2905_, v___x_2906_, v___f_2884_);
return v___x_2907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed(lean_object* v_stream_2908_, lean_object* v___f_2909_, lean_object* v___f_2910_, lean_object* v___f_2911_, lean_object* v_x_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(v_stream_2908_, v___f_2909_, v___f_2910_, v___f_2911_, v_x_2912_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(lean_object* v_step_2915_, lean_object* v_a_2916_, lean_object* v_stream_2917_, lean_object* v___f_2918_, lean_object* v___f_2919_, lean_object* v___f_2920_, lean_object* v_u_2921_, lean_object* v_b_2922_){
_start:
{
lean_object* v___f_2924_; lean_object* v___f_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_inc_ref_n(v_a_2916_, 2);
v___f_2924_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2924_, 0, v_step_2915_);
lean_closure_set(v___f_2924_, 1, v_b_2922_);
lean_closure_set(v___f_2924_, 2, v_a_2916_);
v___f_2925_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_2925_, 0, v_stream_2917_);
lean_closure_set(v___f_2925_, 1, v___f_2918_);
lean_closure_set(v___f_2925_, 2, v___f_2919_);
lean_closure_set(v___f_2925_, 3, v___f_2924_);
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = 0;
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_a_2916_);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
v___x_2930_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2926_, v___x_2927_, v___x_2929_, v___f_2920_);
v___x_2931_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2926_, v___x_2927_, v___x_2930_, v___f_2925_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed(lean_object* v_step_2932_, lean_object* v_a_2933_, lean_object* v_stream_2934_, lean_object* v___f_2935_, lean_object* v___f_2936_, lean_object* v___f_2937_, lean_object* v_u_2938_, lean_object* v_b_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(v_step_2932_, v_a_2933_, v_stream_2934_, v___f_2935_, v___f_2936_, v___f_2937_, v_u_2938_, v_b_2939_);
lean_dec_ref(v_a_2933_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_2945_, lean_object* v_acc_2946_, lean_object* v_step_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___f_2950_; lean_object* v___f_2951_; lean_object* v___f_2952_; lean_object* v___f_2953_; lean_object* v___x_2954_; lean_object* v___f_2955_; uint8_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___f_2950_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_2951_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_2952_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_2948_);
v___f_2953_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_2953_, 0, v_step_2947_);
lean_closure_set(v___f_2953_, 1, v_a_2948_);
lean_closure_set(v___f_2953_, 2, v_stream_2945_);
lean_closure_set(v___f_2953_, 3, v___f_2950_);
lean_closure_set(v___f_2953_, 4, v___f_2951_);
lean_closure_set(v___f_2953_, 5, v___f_2952_);
v___x_2954_ = lean_unsigned_to_nat(0u);
v___f_2955_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2955_, 0, v___f_2953_);
lean_closure_set(v___f_2955_, 1, v___x_2954_);
lean_closure_set(v___f_2955_, 2, v_acc_2946_);
v___x_2956_ = 0;
v___x_2957_ = lean_io_promise_new();
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
v___x_2960_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2954_, v___x_2956_, v___x_2959_, v___f_2955_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_2961_, lean_object* v_acc_2962_, lean_object* v_step_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_2961_, v_acc_2962_, v_step_2963_, v_a_2964_);
lean_dec_ref(v_a_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_2967_, lean_object* v_stream_2968_, lean_object* v_acc_2969_, lean_object* v_step_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___f_2978_; uint8_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___f_2973_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_2974_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_2975_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_2971_);
v___f_2976_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_2976_, 0, v_step_2970_);
lean_closure_set(v___f_2976_, 1, v_a_2971_);
lean_closure_set(v___f_2976_, 2, v_stream_2968_);
lean_closure_set(v___f_2976_, 3, v___f_2973_);
lean_closure_set(v___f_2976_, 4, v___f_2974_);
lean_closure_set(v___f_2976_, 5, v___f_2975_);
v___x_2977_ = lean_unsigned_to_nat(0u);
v___f_2978_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2978_, 0, v___f_2976_);
lean_closure_set(v___f_2978_, 1, v___x_2977_);
lean_closure_set(v___f_2978_, 2, v_acc_2969_);
v___x_2979_ = 0;
v___x_2980_ = lean_io_promise_new();
v___x_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
v___x_2983_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2977_, v___x_2979_, v___x_2982_, v___f_2978_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_2984_, lean_object* v_stream_2985_, lean_object* v_acc_2986_, lean_object* v_step_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_2984_, v_stream_2985_, v_acc_2986_, v_step_2987_, v_a_2988_);
lean_dec_ref(v_a_2988_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v_stream_2993_, lean_object* v___f_2994_, lean_object* v___f_2995_, lean_object* v_x_2996_){
_start:
{
if (lean_obj_tag(v_x_2996_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v___f_2995_);
lean_dec_ref(v___f_2994_);
lean_dec_ref(v_stream_2993_);
v_a_2998_ = lean_ctor_get(v_x_2996_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_x_2996_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3000_ = v_x_2996_;
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v_x_2996_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_a_3007_ = lean_ctor_get(v_x_2996_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v_x_2996_, 1);
v___x_3008_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2993_);
v___x_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set(v___x_3009_, 1, v___f_2994_);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v_a_3007_);
lean_ctor_set(v___x_3010_, 1, v___f_2995_);
v___x_3011_ = lean_unsigned_to_nat(2u);
v___x_3012_ = lean_mk_empty_array_with_capacity(v___x_3011_);
v___x_3013_ = lean_array_push(v___x_3012_, v___x_3009_);
v___x_3014_ = lean_array_push(v___x_3013_, v___x_3010_);
v___x_3015_ = l_Std_Async_Selectable_one___redArg(v___x_3014_);
return v___x_3015_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v_stream_3016_, lean_object* v___f_3017_, lean_object* v___f_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_3016_, v___f_3017_, v___f_3018_, v_x_3019_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v___f_3022_, lean_object* v___f_3023_, lean_object* v___f_3024_, lean_object* v_stream_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___f_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___f_3028_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3028_, 0, v_stream_3025_);
lean_closure_set(v___f_3028_, 1, v___f_3022_);
lean_closure_set(v___f_3028_, 2, v___f_3023_);
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = 0;
lean_inc_ref(v___y_3026_);
v___x_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___y_3026_);
v___x_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
v___x_3033_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3029_, v___x_3030_, v___x_3032_, v___f_3024_);
v___x_3034_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3029_, v___x_3030_, v___x_3033_, v___f_3028_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v___f_3035_, lean_object* v___f_3036_, lean_object* v___f_3037_, lean_object* v_stream_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v___f_3035_, v___f_3036_, v___f_3037_, v_stream_3038_, v___y_3039_);
lean_dec_ref(v___y_3039_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v_toPure_3049_, lean_object* v_result_3050_, lean_object* v_maximumSize_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_stream_3055_, lean_object* v_toBind_3056_, lean_object* v_____do__lift_3057_){
_start:
{
if (lean_obj_tag(v_____do__lift_3057_) == 0)
{
lean_object* v___x_3058_; 
lean_dec(v_toBind_3056_);
lean_dec_ref(v_stream_3055_);
lean_dec(v_inst_3054_);
lean_dec_ref(v_inst_3053_);
lean_dec_ref(v_inst_3052_);
lean_dec(v_maximumSize_3051_);
v___x_3058_ = lean_apply_2(v_toPure_3049_, lean_box(0), v_result_3050_);
return v___x_3058_;
}
else
{
lean_object* v_val_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_toPure_3049_);
v_val_3059_ = lean_ctor_get(v_____do__lift_3057_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_____do__lift_3057_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3061_ = v_____do__lift_3057_;
v_isShared_3062_ = v_isSharedCheck_3090_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_val_3059_);
lean_dec(v_____do__lift_3057_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3090_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_data_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; lean_object* v_result_3068_; 
v_data_3063_ = lean_ctor_get(v_val_3059_, 0);
lean_inc_ref(v_data_3063_);
lean_dec(v_val_3059_);
v___x_3064_ = lean_unsigned_to_nat(0u);
v___x_3065_ = lean_byte_array_size(v_result_3050_);
v___x_3066_ = lean_byte_array_size(v_data_3063_);
v___x_3067_ = 0;
v_result_3068_ = lean_byte_array_copy_slice(v_data_3063_, v___x_3064_, v_result_3050_, v___x_3065_, v___x_3066_, v___x_3067_);
lean_dec_ref(v_data_3063_);
if (lean_obj_tag(v_maximumSize_3051_) == 1)
{
lean_object* v_val_3069_; lean_object* v___x_3070_; uint64_t v___x_3071_; uint64_t v___x_3072_; uint8_t v___x_3073_; 
v_val_3069_ = lean_ctor_get(v_maximumSize_3051_, 0);
v___x_3070_ = lean_byte_array_size(v_result_3068_);
v___x_3071_ = lean_uint64_of_nat(v___x_3070_);
v___x_3072_ = lean_unbox_uint64(v_val_3069_);
v___x_3073_ = lean_uint64_dec_lt(v___x_3072_, v___x_3071_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; 
lean_del_object(v___x_3061_);
lean_dec(v_toBind_3056_);
v___x_3074_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3052_, v_inst_3053_, v_inst_3054_, v_stream_3055_, v_maximumSize_3051_, v_result_3068_);
return v___x_3074_;
}
else
{
lean_object* v_throw_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; uint64_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
lean_inc(v_val_3069_);
v_throw_3075_ = lean_ctor_get(v_inst_3053_, 0);
lean_inc(v_throw_3075_);
v___f_3076_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0), 7, 6);
lean_closure_set(v___f_3076_, 0, v_inst_3052_);
lean_closure_set(v___f_3076_, 1, v_inst_3053_);
lean_closure_set(v___f_3076_, 2, v_inst_3054_);
lean_closure_set(v___f_3076_, 3, v_stream_3055_);
lean_closure_set(v___f_3076_, 4, v_maximumSize_3051_);
lean_closure_set(v___f_3076_, 5, v_result_3068_);
v___x_3077_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0));
v___x_3078_ = lean_unbox_uint64(v_val_3069_);
lean_dec(v_val_3069_);
v___x_3079_ = lean_uint64_to_nat(v___x_3078_);
v___x_3080_ = l_Nat_reprFast(v___x_3079_);
v___x_3081_ = lean_string_append(v___x_3077_, v___x_3080_);
lean_dec_ref(v___x_3080_);
v___x_3082_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1));
v___x_3083_ = lean_string_append(v___x_3081_, v___x_3082_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 18);
lean_ctor_set(v___x_3061_, 0, v___x_3083_);
v___x_3085_ = v___x_3061_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_apply_2(v_throw_3075_, lean_box(0), v___x_3085_);
v___x_3087_ = lean_apply_4(v_toBind_3056_, lean_box(0), lean_box(0), v___x_3086_, v___f_3076_);
return v___x_3087_;
}
}
}
else
{
lean_object* v___x_3089_; 
lean_del_object(v___x_3061_);
lean_dec(v_toBind_3056_);
v___x_3089_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3052_, v_inst_3053_, v_inst_3054_, v_stream_3055_, v_maximumSize_3051_, v_result_3068_);
return v___x_3089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_stream_3094_, lean_object* v_maximumSize_3095_, lean_object* v_result_3096_){
_start:
{
lean_object* v_toApplicative_3097_; lean_object* v_toBind_3098_; lean_object* v_toPure_3099_; lean_object* v___x_3100_; lean_object* v___f_3101_; lean_object* v___x_3102_; 
v_toApplicative_3097_ = lean_ctor_get(v_inst_3091_, 0);
v_toBind_3098_ = lean_ctor_get(v_inst_3091_, 1);
lean_inc_n(v_toBind_3098_, 2);
v_toPure_3099_ = lean_ctor_get(v_toApplicative_3097_, 1);
lean_inc(v_toPure_3099_);
lean_inc(v_inst_3093_);
lean_inc_ref(v_stream_3094_);
v___x_3100_ = lean_apply_1(v_inst_3093_, v_stream_3094_);
v___f_3101_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 9, 8);
lean_closure_set(v___f_3101_, 0, v_toPure_3099_);
lean_closure_set(v___f_3101_, 1, v_result_3096_);
lean_closure_set(v___f_3101_, 2, v_maximumSize_3095_);
lean_closure_set(v___f_3101_, 3, v_inst_3091_);
lean_closure_set(v___f_3101_, 4, v_inst_3092_);
lean_closure_set(v___f_3101_, 5, v_inst_3093_);
lean_closure_set(v___f_3101_, 6, v_stream_3094_);
lean_closure_set(v___f_3101_, 7, v_toBind_3098_);
v___x_3102_ = lean_apply_4(v_toBind_3098_, lean_box(0), lean_box(0), v___x_3100_, v___f_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_inst_3103_, lean_object* v_inst_3104_, lean_object* v_inst_3105_, lean_object* v_stream_3106_, lean_object* v_maximumSize_3107_, lean_object* v_result_3108_, lean_object* v_____r_3109_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3103_, v_inst_3104_, v_inst_3105_, v_stream_3106_, v_maximumSize_3107_, v_result_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_3111_, lean_object* v_inst_3112_, lean_object* v_inst_3113_, lean_object* v_inst_3114_, lean_object* v_stream_3115_, lean_object* v_maximumSize_3116_, lean_object* v_result_3117_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3112_, v_inst_3113_, v_inst_3114_, v_stream_3115_, v_maximumSize_3116_, v_result_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_toPure_3121_, lean_object* v_result_3122_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_apply_1(v_inst_3119_, v_result_3122_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_toPure_3121_);
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3133_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3133_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v_throw_3128_; lean_object* v___x_3130_; 
v_throw_3128_ = lean_ctor_get(v_inst_3120_, 0);
lean_inc(v_throw_3128_);
lean_dec_ref(v_inst_3120_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set_tag(v___x_3126_, 18);
v___x_3130_ = v___x_3126_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3124_);
v___x_3130_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3131_; 
v___x_3131_ = lean_apply_2(v_throw_3128_, lean_box(0), v___x_3130_);
return v___x_3131_;
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3135_; 
lean_dec_ref(v_inst_3120_);
v_a_3134_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v___x_3123_, 1);
v___x_3135_ = lean_apply_2(v_toPure_3121_, lean_box(0), v_a_3134_);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_inst_3139_, lean_object* v_stream_3140_, lean_object* v_maximumSize_3141_){
_start:
{
lean_object* v_toApplicative_3142_; lean_object* v_toBind_3143_; lean_object* v_toPure_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___f_3147_; lean_object* v___x_3148_; 
v_toApplicative_3142_ = lean_ctor_get(v_inst_3137_, 0);
v_toBind_3143_ = lean_ctor_get(v_inst_3137_, 1);
lean_inc(v_toBind_3143_);
v_toPure_3144_ = lean_ctor_get(v_toApplicative_3142_, 1);
lean_inc(v_toPure_3144_);
v___x_3145_ = l_ByteArray_empty;
lean_inc_ref(v_inst_3138_);
v___x_3146_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3137_, v_inst_3138_, v_inst_3139_, v_stream_3140_, v_maximumSize_3141_, v___x_3145_);
v___f_3147_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3147_, 0, v_inst_3136_);
lean_closure_set(v___f_3147_, 1, v_inst_3138_);
lean_closure_set(v___f_3147_, 2, v_toPure_3144_);
v___x_3148_ = lean_apply_4(v_toBind_3143_, lean_box(0), lean_box(0), v___x_3146_, v___f_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_3149_, lean_object* v_m_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_stream_3155_, lean_object* v_maximumSize_3156_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_3151_, v_inst_3152_, v_inst_3153_, v_inst_3154_, v_stream_3155_, v_maximumSize_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0(lean_object* v_toPure_3158_, lean_object* v_____r_3159_){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = lean_box(0);
v___x_3161_ = lean_apply_2(v_toPure_3158_, lean_box(0), v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(lean_object* v_toPure_3162_, uint64_t v_consumed_3163_, lean_object* v_drainLimit_3164_, lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_stream_3167_, lean_object* v_closeStream_3168_, lean_object* v_toBind_3169_, lean_object* v___f_3170_, lean_object* v_____do__lift_3171_){
_start:
{
if (lean_obj_tag(v_____do__lift_3171_) == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_dec(v___f_3170_);
lean_dec(v_toBind_3169_);
lean_dec(v_closeStream_3168_);
lean_dec_ref(v_stream_3167_);
lean_dec(v_inst_3166_);
lean_dec_ref(v_inst_3165_);
lean_dec(v_drainLimit_3164_);
v___x_3172_ = lean_box(0);
v___x_3173_ = lean_apply_2(v_toPure_3162_, lean_box(0), v___x_3172_);
return v___x_3173_;
}
else
{
lean_object* v_val_3174_; lean_object* v_data_3175_; lean_object* v___x_3176_; uint64_t v___x_3177_; uint64_t v_consumed_3178_; 
lean_dec(v_toPure_3162_);
v_val_3174_ = lean_ctor_get(v_____do__lift_3171_, 0);
v_data_3175_ = lean_ctor_get(v_val_3174_, 0);
v___x_3176_ = lean_byte_array_size(v_data_3175_);
v___x_3177_ = lean_uint64_of_nat(v___x_3176_);
v_consumed_3178_ = lean_uint64_add(v_consumed_3163_, v___x_3177_);
if (lean_obj_tag(v_drainLimit_3164_) == 1)
{
lean_object* v_val_3179_; uint64_t v___x_3180_; uint8_t v___x_3181_; 
v_val_3179_ = lean_ctor_get(v_drainLimit_3164_, 0);
v___x_3180_ = lean_unbox_uint64(v_val_3179_);
v___x_3181_ = lean_uint64_dec_lt(v___x_3180_, v_consumed_3178_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; 
lean_dec(v___f_3170_);
lean_dec(v_toBind_3169_);
v___x_3182_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3165_, v_inst_3166_, v_stream_3167_, v_drainLimit_3164_, v_closeStream_3168_, v_consumed_3178_);
return v___x_3182_;
}
else
{
lean_object* v___x_3183_; 
lean_dec_ref_known(v_drainLimit_3164_, 1);
lean_dec_ref(v_stream_3167_);
lean_dec(v_inst_3166_);
lean_dec_ref(v_inst_3165_);
v___x_3183_ = lean_apply_4(v_toBind_3169_, lean_box(0), lean_box(0), v_closeStream_3168_, v___f_3170_);
return v___x_3183_;
}
}
else
{
lean_object* v___x_3184_; 
lean_dec(v___f_3170_);
lean_dec(v_toBind_3169_);
v___x_3184_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3165_, v_inst_3166_, v_stream_3167_, v_drainLimit_3164_, v_closeStream_3168_, v_consumed_3178_);
return v___x_3184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed(lean_object* v_toPure_3185_, lean_object* v_consumed_3186_, lean_object* v_drainLimit_3187_, lean_object* v_inst_3188_, lean_object* v_inst_3189_, lean_object* v_stream_3190_, lean_object* v_closeStream_3191_, lean_object* v_toBind_3192_, lean_object* v___f_3193_, lean_object* v_____do__lift_3194_){
_start:
{
uint64_t v_consumed_boxed_3195_; lean_object* v_res_3196_; 
v_consumed_boxed_3195_ = lean_unbox_uint64(v_consumed_3186_);
lean_dec_ref(v_consumed_3186_);
v_res_3196_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(v_toPure_3185_, v_consumed_boxed_3195_, v_drainLimit_3187_, v_inst_3188_, v_inst_3189_, v_stream_3190_, v_closeStream_3191_, v_toBind_3192_, v___f_3193_, v_____do__lift_3194_);
lean_dec(v_____do__lift_3194_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_stream_3199_, lean_object* v_drainLimit_3200_, lean_object* v_closeStream_3201_, uint64_t v_consumed_3202_){
_start:
{
lean_object* v_toApplicative_3203_; lean_object* v_toBind_3204_; lean_object* v_toPure_3205_; lean_object* v___x_3206_; lean_object* v___f_3207_; lean_object* v___x_3208_; lean_object* v___f_3209_; lean_object* v___x_3210_; 
v_toApplicative_3203_ = lean_ctor_get(v_inst_3197_, 0);
v_toBind_3204_ = lean_ctor_get(v_inst_3197_, 1);
lean_inc_n(v_toBind_3204_, 2);
v_toPure_3205_ = lean_ctor_get(v_toApplicative_3203_, 1);
lean_inc_n(v_toPure_3205_, 2);
lean_inc(v_inst_3198_);
lean_inc_ref(v_stream_3199_);
v___x_3206_ = lean_apply_1(v_inst_3198_, v_stream_3199_);
v___f_3207_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3207_, 0, v_toPure_3205_);
v___x_3208_ = lean_box_uint64(v_consumed_3202_);
v___f_3209_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3209_, 0, v_toPure_3205_);
lean_closure_set(v___f_3209_, 1, v___x_3208_);
lean_closure_set(v___f_3209_, 2, v_drainLimit_3200_);
lean_closure_set(v___f_3209_, 3, v_inst_3197_);
lean_closure_set(v___f_3209_, 4, v_inst_3198_);
lean_closure_set(v___f_3209_, 5, v_stream_3199_);
lean_closure_set(v___f_3209_, 6, v_closeStream_3201_);
lean_closure_set(v___f_3209_, 7, v_toBind_3204_);
lean_closure_set(v___f_3209_, 8, v___f_3207_);
v___x_3210_ = lean_apply_4(v_toBind_3204_, lean_box(0), lean_box(0), v___x_3206_, v___f_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___boxed(lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_stream_3213_, lean_object* v_drainLimit_3214_, lean_object* v_closeStream_3215_, lean_object* v_consumed_3216_){
_start:
{
uint64_t v_consumed_boxed_3217_; lean_object* v_res_3218_; 
v_consumed_boxed_3217_ = lean_unbox_uint64(v_consumed_3216_);
lean_dec_ref(v_consumed_3216_);
v_res_3218_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3211_, v_inst_3212_, v_stream_3213_, v_drainLimit_3214_, v_closeStream_3215_, v_consumed_boxed_3217_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_object* v_m_3219_, lean_object* v_inst_3220_, lean_object* v_inst_3221_, lean_object* v_stream_3222_, lean_object* v_drainLimit_3223_, lean_object* v_closeStream_3224_, uint64_t v_consumed_3225_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3220_, v_inst_3221_, v_stream_3222_, v_drainLimit_3223_, v_closeStream_3224_, v_consumed_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___boxed(lean_object* v_m_3227_, lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_stream_3230_, lean_object* v_drainLimit_3231_, lean_object* v_closeStream_3232_, lean_object* v_consumed_3233_){
_start:
{
uint64_t v_consumed_boxed_3234_; lean_object* v_res_3235_; 
v_consumed_boxed_3234_ = lean_unbox_uint64(v_consumed_3233_);
lean_dec_ref(v_consumed_3233_);
v_res_3235_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(v_m_3227_, v_inst_3228_, v_inst_3229_, v_stream_3230_, v_drainLimit_3231_, v_closeStream_3232_, v_consumed_boxed_3234_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain___redArg(lean_object* v_inst_3236_, lean_object* v_inst_3237_, lean_object* v_stream_3238_, lean_object* v_drainLimit_3239_, lean_object* v_closeStream_3240_){
_start:
{
uint64_t v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = 0ULL;
v___x_3242_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3236_, v_inst_3237_, v_stream_3238_, v_drainLimit_3239_, v_closeStream_3240_, v___x_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain(lean_object* v_m_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_stream_3246_, lean_object* v_drainLimit_3247_, lean_object* v_closeStream_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Std_Http_Body_Stream_drain___redArg(v_inst_3244_, v_inst_3245_, v_stream_3246_, v_drainLimit_3247_, v_closeStream_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t v_incomplete_3255_, lean_object* v_chunk_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v_pendingProducer_3261_; lean_object* v_pendingConsumer_3262_; lean_object* v_interestWaiter_3263_; uint8_t v_closed_3264_; lean_object* v_knownSize_3265_; lean_object* v_pendingIncompleteChunk_3266_; lean_object* v_closeError_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3308_; 
v___x_3259_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_3257_);
v___x_3260_ = lean_st_ref_get(v___y_3257_);
v_pendingProducer_3261_ = lean_ctor_get(v___x_3260_, 0);
v_pendingConsumer_3262_ = lean_ctor_get(v___x_3260_, 1);
v_interestWaiter_3263_ = lean_ctor_get(v___x_3260_, 2);
v_closed_3264_ = lean_ctor_get_uint8(v___x_3260_, sizeof(void*)*6);
v_knownSize_3265_ = lean_ctor_get(v___x_3260_, 3);
v_pendingIncompleteChunk_3266_ = lean_ctor_get(v___x_3260_, 4);
v_closeError_3267_ = lean_ctor_get(v___x_3260_, 5);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3269_ = v___x_3260_;
v_isShared_3270_ = v_isSharedCheck_3308_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_closeError_3267_);
lean_inc(v_pendingIncompleteChunk_3266_);
lean_inc(v_knownSize_3265_);
lean_inc(v_interestWaiter_3263_);
lean_inc(v_pendingConsumer_3262_);
lean_inc(v_pendingProducer_3261_);
lean_dec(v___x_3260_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3308_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___y_3272_; 
if (v_closed_3264_ == 0)
{
if (lean_obj_tag(v_pendingIncompleteChunk_3266_) == 0)
{
v___y_3272_ = v_chunk_3256_;
goto v___jp_3271_;
}
else
{
lean_object* v_val_3286_; lean_object* v_data_3287_; lean_object* v_extensions_3288_; lean_object* v_data_3289_; lean_object* v_extensions_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3306_; 
v_val_3286_ = lean_ctor_get(v_pendingIncompleteChunk_3266_, 0);
lean_inc(v_val_3286_);
lean_dec_ref_known(v_pendingIncompleteChunk_3266_, 1);
v_data_3287_ = lean_ctor_get(v_val_3286_, 0);
lean_inc_ref(v_data_3287_);
v_extensions_3288_ = lean_ctor_get(v_val_3286_, 1);
lean_inc_ref(v_extensions_3288_);
lean_dec(v_val_3286_);
v_data_3289_ = lean_ctor_get(v_chunk_3256_, 0);
v_extensions_3290_ = lean_ctor_get(v_chunk_3256_, 1);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_chunk_3256_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3292_ = v_chunk_3256_;
v_isShared_3293_ = v_isSharedCheck_3306_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_extensions_3290_);
lean_inc(v_data_3289_);
lean_dec(v_chunk_3256_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3306_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
v___x_3294_ = lean_unsigned_to_nat(0u);
v___x_3295_ = lean_byte_array_size(v_data_3287_);
v___x_3296_ = lean_byte_array_size(v_data_3289_);
v___x_3297_ = lean_byte_array_copy_slice(v_data_3289_, v___x_3294_, v_data_3287_, v___x_3295_, v___x_3296_, v_closed_3264_);
lean_dec_ref(v_data_3289_);
v___x_3298_ = lean_array_get_size(v_extensions_3288_);
v___x_3299_ = lean_nat_dec_eq(v___x_3298_, v___x_3294_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3301_; 
lean_dec_ref(v_extensions_3290_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 1, v_extensions_3288_);
lean_ctor_set(v___x_3292_, 0, v___x_3297_);
v___x_3301_ = v___x_3292_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_extensions_3288_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
v___y_3272_ = v___x_3301_;
goto v___jp_3271_;
}
}
else
{
lean_object* v___x_3304_; 
lean_dec_ref(v_extensions_3288_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3297_);
v___x_3304_ = v___x_3292_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_extensions_3290_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
v___y_3272_ = v___x_3304_;
goto v___jp_3271_;
}
}
}
}
}
else
{
lean_object* v___x_3307_; 
lean_del_object(v___x_3269_);
lean_dec(v_closeError_3267_);
lean_dec(v_pendingIncompleteChunk_3266_);
lean_dec(v_knownSize_3265_);
lean_dec(v_interestWaiter_3263_);
lean_dec(v_pendingConsumer_3262_);
lean_dec(v_pendingProducer_3261_);
lean_dec_ref(v_chunk_3256_);
v___x_3307_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_3307_;
}
v___jp_3271_:
{
if (v_incomplete_3255_ == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3273_ = lean_box(0);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 4, v___x_3273_);
v___x_3275_ = v___x_3269_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_pendingProducer_3261_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_pendingConsumer_3262_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v_interestWaiter_3263_);
lean_ctor_set(v_reuseFailAlloc_3279_, 3, v_knownSize_3265_);
lean_ctor_set(v_reuseFailAlloc_3279_, 4, v___x_3273_);
lean_ctor_set(v_reuseFailAlloc_3279_, 5, v_closeError_3267_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*6, v_closed_3264_);
v___x_3275_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = lean_st_ref_swap(v___y_3257_, v___x_3275_);
lean_dec(v___x_3276_);
v___x_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___y_3272_);
v___x_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
return v___x_3278_;
}
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___y_3272_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 4, v___x_3280_);
v___x_3282_ = v___x_3269_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_pendingProducer_3261_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_pendingConsumer_3262_);
lean_ctor_set(v_reuseFailAlloc_3285_, 2, v_interestWaiter_3263_);
lean_ctor_set(v_reuseFailAlloc_3285_, 3, v_knownSize_3265_);
lean_ctor_set(v_reuseFailAlloc_3285_, 4, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3285_, 5, v_closeError_3267_);
lean_ctor_set_uint8(v_reuseFailAlloc_3285_, sizeof(void*)*6, v_closed_3264_);
v___x_3282_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_st_ref_swap(v___y_3257_, v___x_3282_);
lean_dec(v___x_3283_);
v___x_3284_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
return v___x_3284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_incomplete_3309_, lean_object* v_chunk_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
uint8_t v_incomplete_boxed_3313_; lean_object* v_res_3314_; 
v_incomplete_boxed_3313_ = lean_unbox(v_incomplete_3309_);
v_res_3314_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_incomplete_boxed_3313_, v_chunk_3310_, v___y_3311_);
lean_dec(v___y_3311_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_3315_, lean_object* v_chunk_3316_, uint8_t v_incomplete_3317_){
_start:
{
lean_object* v___x_3319_; lean_object* v___f_3320_; lean_object* v___x_3321_; 
v___x_3319_ = lean_box(v_incomplete_3317_);
v___f_3320_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3320_, 0, v___x_3319_);
lean_closure_set(v___f_3320_, 1, v_chunk_3316_);
v___x_3321_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_3315_, v___f_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_3322_, lean_object* v_chunk_3323_, lean_object* v_incomplete_3324_, lean_object* v_a_3325_){
_start:
{
uint8_t v_incomplete_boxed_3326_; lean_object* v_res_3327_; 
v_incomplete_boxed_3326_ = lean_unbox(v_incomplete_3324_);
v_res_3327_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3322_, v_chunk_3323_, v_incomplete_boxed_3326_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_3334_){
_start:
{
if (lean_obj_tag(v_x_3334_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3344_; 
v_a_3336_ = lean_ctor_get(v_x_3334_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_x_3334_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3338_ = v_x_3334_;
v_isShared_3339_ = v_isSharedCheck_3344_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v_x_3334_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3344_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3342_; 
v___x_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
return v___x_3342_;
}
}
}
else
{
lean_object* v___x_3345_; 
lean_dec_ref_known(v_x_3334_, 1);
v___x_3345_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_3345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_3346_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___3349_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___3352_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_3359_, lean_object* v_x_3360_){
_start:
{
if (lean_obj_tag(v_x_3360_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref(v___f_3359_);
v_a_3364_ = lean_ctor_get(v_x_3360_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_x_3360_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3366_ = v_x_3360_;
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v_x_3360_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
return v___x_3370_;
}
}
}
else
{
lean_object* v_a_3373_; 
v_a_3373_ = lean_ctor_get(v_x_3360_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v_x_3360_, 1);
if (lean_obj_tag(v_a_3373_) == 1)
{
lean_object* v_val_3374_; uint8_t v___x_3375_; 
v_val_3374_ = lean_ctor_get(v_a_3373_, 0);
lean_inc(v_val_3374_);
lean_dec_ref_known(v_a_3373_, 1);
v___x_3375_ = lean_unbox(v_val_3374_);
lean_dec(v_val_3374_);
if (v___x_3375_ == 1)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = lean_box(0);
v___x_3377_ = lean_apply_2(v___f_3359_, v___x_3376_, lean_box(0));
return v___x_3377_;
}
else
{
lean_dec_ref(v___f_3359_);
goto v___jp_3362_;
}
}
else
{
lean_dec(v_a_3373_);
lean_dec_ref(v___f_3359_);
goto v___jp_3362_;
}
}
v___jp_3362_:
{
lean_object* v___x_3363_; 
v___x_3363_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_3363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_3378_, lean_object* v_x_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_3378_, v_x_3379_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_3382_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3383_, 0, v_a_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_3384_, lean_object* v_x_3385_){
_start:
{
if (lean_obj_tag(v_x_3385_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3395_; 
v_a_3387_ = lean_ctor_get(v_x_3385_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_x_3385_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3389_ = v_x_3385_;
v_isShared_3390_ = v_isSharedCheck_3395_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v_x_3385_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3395_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; 
v___x_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
return v___x_3393_;
}
}
}
else
{
lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3406_; 
v_isSharedCheck_3406_ = !lean_is_exclusive(v_x_3385_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_x_3385_, 0);
lean_dec(v_unused_3407_);
v___x_3397_ = v_x_3385_;
v_isShared_3398_ = v_isSharedCheck_3406_;
goto v_resetjp_3396_;
}
else
{
lean_dec(v_x_3385_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3406_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3399_ = lean_box(v___x_3384_);
v___x_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3400_);
v___x_3402_ = v___x_3397_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
return v___x_3404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_3408_, lean_object* v_x_3409_, lean_object* v___y_3410_){
_start:
{
uint8_t v___x_5091__boxed_3411_; lean_object* v_res_3412_; 
v___x_5091__boxed_3411_ = lean_unbox(v___x_3408_);
v_res_3412_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5091__boxed_3411_, v_x_3409_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_3413_, lean_object* v_x_3414_){
_start:
{
if (lean_obj_tag(v_x_3414_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3424_; 
v_a_3416_ = lean_ctor_get(v_x_3414_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_x_3414_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3418_ = v_x_3414_;
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v_x_3414_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
return v___x_3422_;
}
}
}
else
{
lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3435_; 
v_isSharedCheck_3435_ = !lean_is_exclusive(v_x_3414_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v_x_3414_, 0);
lean_dec(v_unused_3436_);
v___x_3426_ = v_x_3414_;
v_isShared_3427_ = v_isSharedCheck_3435_;
goto v_resetjp_3425_;
}
else
{
lean_dec(v_x_3414_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3435_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3428_ = lean_box(v_a_3413_);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3429_);
v___x_3431_ = v___x_3426_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
v___x_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
return v___x_3433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_3437_, lean_object* v_x_3438_, lean_object* v___y_3439_){
_start:
{
uint8_t v_a_5143__boxed_3440_; lean_object* v_res_3441_; 
v_a_5143__boxed_3440_ = lean_unbox(v_a_3437_);
v_res_3441_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5143__boxed_3440_, v_x_3438_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_3442_, lean_object* v_interestWaiter_3443_, uint8_t v_closed_3444_, lean_object* v_knownSize_3445_, lean_object* v_pendingIncompleteChunk_3446_, lean_object* v_closeError_3447_, lean_object* v___y_3448_, lean_object* v_chunk_3449_, lean_object* v___f_3450_, lean_object* v_x_3451_){
_start:
{
if (lean_obj_tag(v_x_3451_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3461_; 
lean_dec_ref(v___f_3450_);
lean_dec(v_closeError_3447_);
lean_dec(v_pendingIncompleteChunk_3446_);
lean_dec(v_knownSize_3445_);
lean_dec(v_interestWaiter_3443_);
lean_dec(v_pendingProducer_3442_);
v_a_3453_ = lean_ctor_get(v_x_3451_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v_x_3451_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3455_ = v_x_3451_;
v_isShared_3456_ = v_isSharedCheck_3461_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v_x_3451_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3461_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
return v___x_3459_;
}
}
}
else
{
lean_object* v_a_3462_; uint8_t v___x_3463_; 
v_a_3462_ = lean_ctor_get(v_x_3451_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v_x_3451_, 1);
v___x_3463_ = lean_unbox(v_a_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___f_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; lean_object* v___x_3471_; 
lean_dec_ref(v___f_3450_);
lean_inc(v_a_3462_);
v___f_3464_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3464_, 0, v_a_3462_);
v___x_3465_ = lean_box(0);
v___x_3466_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3466_, 0, v_pendingProducer_3442_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
lean_ctor_set(v___x_3466_, 2, v_interestWaiter_3443_);
lean_ctor_set(v___x_3466_, 3, v_knownSize_3445_);
lean_ctor_set(v___x_3466_, 4, v_pendingIncompleteChunk_3446_);
lean_ctor_set(v___x_3466_, 5, v_closeError_3447_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*6, v_closed_3444_);
v___x_3467_ = lean_unsigned_to_nat(0u);
v___x_3468_ = lean_st_ref_swap(v___y_3448_, v___x_3466_);
lean_dec(v___x_3468_);
v___x_3469_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3470_ = lean_unbox(v_a_3462_);
lean_dec(v_a_3462_);
v___x_3471_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3467_, v___x_3470_, v___x_3469_, v___f_3464_);
return v___x_3471_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
lean_dec(v_a_3462_);
v___x_3472_ = lean_box(0);
v___x_3473_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_3445_, v_chunk_3449_);
v___x_3474_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3474_, 0, v_pendingProducer_3442_);
lean_ctor_set(v___x_3474_, 1, v___x_3472_);
lean_ctor_set(v___x_3474_, 2, v_interestWaiter_3443_);
lean_ctor_set(v___x_3474_, 3, v___x_3473_);
lean_ctor_set(v___x_3474_, 4, v_pendingIncompleteChunk_3446_);
lean_ctor_set(v___x_3474_, 5, v_closeError_3447_);
lean_ctor_set_uint8(v___x_3474_, sizeof(void*)*6, v_closed_3444_);
v___x_3475_ = lean_unsigned_to_nat(0u);
v___x_3476_ = lean_st_ref_swap(v___y_3448_, v___x_3474_);
lean_dec(v___x_3476_);
v___x_3477_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3478_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3475_, v_closed_3444_, v___x_3477_, v___f_3450_);
return v___x_3478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_3479_, lean_object* v_interestWaiter_3480_, lean_object* v_closed_3481_, lean_object* v_knownSize_3482_, lean_object* v_pendingIncompleteChunk_3483_, lean_object* v_closeError_3484_, lean_object* v___y_3485_, lean_object* v_chunk_3486_, lean_object* v___f_3487_, lean_object* v_x_3488_, lean_object* v___y_3489_){
_start:
{
uint8_t v_closed_boxed_3490_; lean_object* v_res_3491_; 
v_closed_boxed_3490_ = lean_unbox(v_closed_3481_);
v_res_3491_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_3479_, v_interestWaiter_3480_, v_closed_boxed_3490_, v_knownSize_3482_, v_pendingIncompleteChunk_3483_, v_closeError_3484_, v___y_3485_, v_chunk_3486_, v___f_3487_, v_x_3488_);
lean_dec_ref(v_chunk_3486_);
lean_dec(v___y_3485_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v___y_3510_, lean_object* v_chunk_3511_, lean_object* v_a_3512_, lean_object* v___f_3513_, lean_object* v_x_3514_){
_start:
{
if (lean_obj_tag(v_x_3514_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v___f_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_chunk_3511_);
v_a_3516_ = lean_ctor_get(v_x_3514_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v_x_3514_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3518_ = v_x_3514_;
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v_x_3514_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; 
v___x_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
return v___x_3522_;
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3578_; 
v_a_3525_ = lean_ctor_get(v_x_3514_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_x_3514_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3527_ = v_x_3514_;
v_isShared_3528_ = v_isSharedCheck_3578_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v_x_3514_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3578_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
uint8_t v_closed_3529_; 
v_closed_3529_ = lean_ctor_get_uint8(v_a_3525_, sizeof(void*)*6);
if (v_closed_3529_ == 0)
{
lean_object* v_pendingConsumer_3530_; 
v_pendingConsumer_3530_ = lean_ctor_get(v_a_3525_, 1);
lean_inc(v_pendingConsumer_3530_);
if (lean_obj_tag(v_pendingConsumer_3530_) == 1)
{
lean_object* v_pendingProducer_3531_; lean_object* v_interestWaiter_3532_; lean_object* v_knownSize_3533_; lean_object* v_pendingIncompleteChunk_3534_; lean_object* v_closeError_3535_; lean_object* v_val_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3555_; 
lean_dec_ref(v___f_3513_);
lean_dec(v_a_3512_);
v_pendingProducer_3531_ = lean_ctor_get(v_a_3525_, 0);
lean_inc(v_pendingProducer_3531_);
v_interestWaiter_3532_ = lean_ctor_get(v_a_3525_, 2);
lean_inc(v_interestWaiter_3532_);
v_knownSize_3533_ = lean_ctor_get(v_a_3525_, 3);
lean_inc(v_knownSize_3533_);
v_pendingIncompleteChunk_3534_ = lean_ctor_get(v_a_3525_, 4);
lean_inc(v_pendingIncompleteChunk_3534_);
v_closeError_3535_ = lean_ctor_get(v_a_3525_, 5);
lean_inc(v_closeError_3535_);
lean_dec(v_a_3525_);
v_val_3536_ = lean_ctor_get(v_pendingConsumer_3530_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_pendingConsumer_3530_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3538_ = v_pendingConsumer_3530_;
v_isShared_3539_ = v_isSharedCheck_3555_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_val_3536_);
lean_dec(v_pendingConsumer_3530_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3555_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___f_3540_; lean_object* v___x_3541_; lean_object* v___f_3542_; lean_object* v___x_3544_; 
v___f_3540_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_3541_ = lean_box(v_closed_3529_);
lean_inc_ref(v_chunk_3511_);
lean_inc(v___y_3510_);
v___f_3542_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 11, 9);
lean_closure_set(v___f_3542_, 0, v_pendingProducer_3531_);
lean_closure_set(v___f_3542_, 1, v_interestWaiter_3532_);
lean_closure_set(v___f_3542_, 2, v___x_3541_);
lean_closure_set(v___f_3542_, 3, v_knownSize_3533_);
lean_closure_set(v___f_3542_, 4, v_pendingIncompleteChunk_3534_);
lean_closure_set(v___f_3542_, 5, v_closeError_3535_);
lean_closure_set(v___f_3542_, 6, v___y_3510_);
lean_closure_set(v___f_3542_, 7, v_chunk_3511_);
lean_closure_set(v___f_3542_, 8, v___f_3540_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v_chunk_3511_);
v___x_3544_ = v___x_3538_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_chunk_3511_);
v___x_3544_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3546_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v___x_3544_);
v___x_3546_ = v___x_3527_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3547_ = lean_unsigned_to_nat(0u);
v___x_3548_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_3536_, v___x_3546_);
lean_dec(v_val_3536_);
v___x_3549_ = lean_box(v___x_3548_);
v___x_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
v___x_3552_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3547_, v_closed_3529_, v___x_3551_, v___f_3542_);
return v___x_3552_;
}
}
}
}
else
{
lean_object* v_pendingProducer_3556_; 
lean_del_object(v___x_3527_);
v_pendingProducer_3556_ = lean_ctor_get(v_a_3525_, 0);
if (lean_obj_tag(v_pendingProducer_3556_) == 0)
{
lean_object* v_interestWaiter_3557_; lean_object* v_knownSize_3558_; lean_object* v_pendingIncompleteChunk_3559_; lean_object* v_closeError_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3573_; 
v_interestWaiter_3557_ = lean_ctor_get(v_a_3525_, 2);
v_knownSize_3558_ = lean_ctor_get(v_a_3525_, 3);
v_pendingIncompleteChunk_3559_ = lean_ctor_get(v_a_3525_, 4);
v_closeError_3560_ = lean_ctor_get(v_a_3525_, 5);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_a_3525_);
if (v_isSharedCheck_3573_ == 0)
{
lean_object* v_unused_3574_; lean_object* v_unused_3575_; 
v_unused_3574_ = lean_ctor_get(v_a_3525_, 1);
lean_dec(v_unused_3574_);
v_unused_3575_ = lean_ctor_get(v_a_3525_, 0);
lean_dec(v_unused_3575_);
v___x_3562_ = v_a_3525_;
v_isShared_3563_ = v_isSharedCheck_3573_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_closeError_3560_);
lean_inc(v_pendingIncompleteChunk_3559_);
lean_inc(v_knownSize_3558_);
lean_inc(v_interestWaiter_3557_);
lean_dec(v_a_3525_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3573_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3567_; 
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v_chunk_3511_);
lean_ctor_set(v___x_3564_, 1, v_a_3512_);
v___x_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v___x_3565_);
v___x_3567_ = v___x_3562_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_pendingConsumer_3530_);
lean_ctor_set(v_reuseFailAlloc_3572_, 2, v_interestWaiter_3557_);
lean_ctor_set(v_reuseFailAlloc_3572_, 3, v_knownSize_3558_);
lean_ctor_set(v_reuseFailAlloc_3572_, 4, v_pendingIncompleteChunk_3559_);
lean_ctor_set(v_reuseFailAlloc_3572_, 5, v_closeError_3560_);
lean_ctor_set_uint8(v_reuseFailAlloc_3572_, sizeof(void*)*6, v_closed_3529_);
v___x_3567_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3568_ = lean_unsigned_to_nat(0u);
v___x_3569_ = lean_st_ref_swap(v___y_3510_, v___x_3567_);
lean_dec(v___x_3569_);
v___x_3570_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3571_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3568_, v_closed_3529_, v___x_3570_, v___f_3513_);
return v___x_3571_;
}
}
}
else
{
lean_object* v___x_3576_; 
lean_dec(v_pendingConsumer_3530_);
lean_dec(v_a_3525_);
lean_dec_ref(v___f_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_chunk_3511_);
v___x_3576_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_3576_;
}
}
}
else
{
lean_object* v___x_3577_; 
lean_del_object(v___x_3527_);
lean_dec(v_a_3525_);
lean_dec_ref(v___f_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_chunk_3511_);
v___x_3577_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_3577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v___y_3579_, lean_object* v_chunk_3580_, lean_object* v_a_3581_, lean_object* v___f_3582_, lean_object* v_x_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v___y_3579_, v_chunk_3580_, v_a_3581_, v___f_3582_, v_x_3583_);
lean_dec(v___y_3579_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_3586_, lean_object* v___f_3587_, lean_object* v_x_3588_){
_start:
{
if (lean_obj_tag(v_x_3588_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref(v___f_3587_);
v_a_3590_ = lean_ctor_get(v_x_3588_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_x_3588_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3592_ = v_x_3588_;
v_isShared_3593_ = v_isSharedCheck_3598_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v_x_3588_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3598_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3596_; 
v___x_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
return v___x_3596_;
}
}
}
else
{
lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3610_; 
v_isSharedCheck_3610_ = !lean_is_exclusive(v_x_3588_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; 
v_unused_3611_ = lean_ctor_get(v_x_3588_, 0);
lean_dec(v_unused_3611_);
v___x_3600_ = v_x_3588_;
v_isShared_3601_ = v_isSharedCheck_3610_;
goto v_resetjp_3599_;
}
else
{
lean_dec(v_x_3588_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3610_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
v___x_3602_ = lean_unsigned_to_nat(0u);
v___x_3603_ = 0;
v___x_3604_ = lean_st_ref_get(v___y_3586_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3604_);
v___x_3606_ = v___x_3600_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
v___x_3608_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3602_, v___x_3603_, v___x_3607_, v___f_3587_);
return v___x_3608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_3612_, lean_object* v___f_3613_, lean_object* v_x_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_3612_, v___f_3613_, v_x_3614_);
lean_dec(v___y_3612_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_3617_, lean_object* v_a_3618_, lean_object* v___f_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___f_3622_; lean_object* v___f_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_inc_n(v___y_3620_, 2);
v___f_3622_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_3622_, 0, v___y_3620_);
lean_closure_set(v___f_3622_, 1, v_chunk_3617_);
lean_closure_set(v___f_3622_, 2, v_a_3618_);
lean_closure_set(v___f_3622_, 3, v___f_3619_);
v___f_3623_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_3623_, 0, v___y_3620_);
lean_closure_set(v___f_3623_, 1, v___f_3622_);
v___x_3624_ = lean_unsigned_to_nat(0u);
v___x_3625_ = 0;
v___x_3626_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3620_);
v___x_3627_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3624_, v___x_3625_, v___x_3626_, v___f_3623_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_3628_, lean_object* v_a_3629_, lean_object* v___f_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_3628_, v_a_3629_, v___f_3630_, v___y_3631_);
lean_dec(v___y_3631_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_3639_, lean_object* v___f_3640_, lean_object* v___f_3641_, lean_object* v_stream_3642_, lean_object* v_chunk_3643_, lean_object* v___f_3644_, lean_object* v_x_3645_){
_start:
{
if (lean_obj_tag(v_x_3645_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3655_; 
lean_dec_ref(v___f_3644_);
lean_dec_ref(v_chunk_3643_);
lean_dec_ref(v_stream_3642_);
lean_dec_ref(v___f_3641_);
lean_dec_ref(v___f_3640_);
v_a_3647_ = lean_ctor_get(v_x_3645_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_x_3645_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3649_ = v_x_3645_;
v_isShared_3650_ = v_isSharedCheck_3655_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v_x_3645_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3655_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; 
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
return v___x_3653_;
}
}
}
else
{
lean_object* v_a_3656_; 
v_a_3656_ = lean_ctor_get(v_x_3645_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v_x_3645_, 1);
if (lean_obj_tag(v_a_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3665_; 
lean_dec_ref(v___f_3644_);
lean_dec_ref(v_chunk_3643_);
lean_dec_ref(v_stream_3642_);
lean_dec_ref(v___f_3641_);
lean_dec_ref(v___f_3640_);
v_a_3657_ = lean_ctor_get(v_a_3656_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_a_3656_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3659_ = v_a_3656_;
v_isShared_3660_ = v_isSharedCheck_3665_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v_a_3656_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3665_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
return v___x_3663_;
}
}
}
else
{
lean_object* v_a_3666_; 
v_a_3666_ = lean_ctor_get(v_a_3656_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v_a_3656_, 1);
if (lean_obj_tag(v_a_3666_) == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_dec_ref(v___f_3644_);
lean_dec_ref(v_chunk_3643_);
lean_dec_ref(v_stream_3642_);
v___x_3667_ = lean_io_promise_result_opt(v_a_3639_);
v___x_3668_ = lean_unsigned_to_nat(0u);
v___x_3669_ = 0;
v___x_3670_ = lean_task_map(v___f_3640_, v___x_3667_, v___x_3668_, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
v___x_3672_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3668_, v___x_3669_, v___x_3671_, v___f_3641_);
return v___x_3672_;
}
else
{
lean_object* v_val_3673_; uint8_t v___x_3674_; 
lean_dec_ref(v___f_3641_);
lean_dec_ref(v___f_3640_);
v_val_3673_ = lean_ctor_get(v_a_3666_, 0);
lean_inc(v_val_3673_);
lean_dec_ref_known(v_a_3666_, 1);
v___x_3674_ = lean_unbox(v_val_3673_);
lean_dec(v_val_3673_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; 
lean_dec_ref(v___f_3644_);
v___x_3675_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3642_, v_chunk_3643_);
return v___x_3675_;
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
lean_dec_ref(v_chunk_3643_);
lean_dec_ref(v_stream_3642_);
v___x_3676_ = lean_box(0);
v___x_3677_ = lean_apply_2(v___f_3644_, v___x_3676_, lean_box(0));
return v___x_3677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_3678_, lean_object* v___f_3679_, lean_object* v___f_3680_, lean_object* v_stream_3681_, lean_object* v_chunk_3682_, lean_object* v___f_3683_, lean_object* v_x_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_3678_, v___f_3679_, v___f_3680_, v_stream_3681_, v_chunk_3682_, v___f_3683_, v_x_3684_);
lean_dec(v_a_3678_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_3687_, lean_object* v___f_3688_, lean_object* v___f_3689_, lean_object* v___f_3690_, lean_object* v_stream_3691_, lean_object* v___f_3692_, lean_object* v_x_3693_){
_start:
{
if (lean_obj_tag(v_x_3693_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v___f_3692_);
lean_dec_ref(v_stream_3691_);
lean_dec_ref(v___f_3690_);
lean_dec_ref(v___f_3689_);
lean_dec_ref(v___f_3688_);
lean_dec_ref(v_chunk_3687_);
v_a_3695_ = lean_ctor_get(v_x_3693_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_x_3693_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3697_ = v_x_3693_;
v_isShared_3698_ = v_isSharedCheck_3703_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v_x_3693_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3703_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3701_; 
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
return v___x_3701_;
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___f_3705_; lean_object* v___f_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_a_3704_ = lean_ctor_get(v_x_3693_, 0);
lean_inc_n(v_a_3704_, 2);
lean_dec_ref_known(v_x_3693_, 1);
lean_inc_ref(v_chunk_3687_);
v___f_3705_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_3705_, 0, v_chunk_3687_);
lean_closure_set(v___f_3705_, 1, v_a_3704_);
lean_closure_set(v___f_3705_, 2, v___f_3688_);
lean_inc_ref(v_stream_3691_);
v___f_3706_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3706_, 0, v_a_3704_);
lean_closure_set(v___f_3706_, 1, v___f_3689_);
lean_closure_set(v___f_3706_, 2, v___f_3690_);
lean_closure_set(v___f_3706_, 3, v_stream_3691_);
lean_closure_set(v___f_3706_, 4, v_chunk_3687_);
lean_closure_set(v___f_3706_, 5, v___f_3692_);
v___x_3707_ = lean_unsigned_to_nat(0u);
v___x_3708_ = 0;
v___x_3709_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3691_, v___f_3705_);
v___x_3710_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3707_, v___x_3708_, v___x_3709_, v___f_3706_);
return v___x_3710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_3711_, lean_object* v___f_3712_, lean_object* v___f_3713_, lean_object* v___f_3714_, lean_object* v_stream_3715_, lean_object* v___f_3716_, lean_object* v_x_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_3711_, v___f_3712_, v___f_3713_, v___f_3714_, v_stream_3715_, v___f_3716_, v_x_3717_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_3720_, lean_object* v_chunk_3721_){
_start:
{
lean_object* v___f_3723_; lean_object* v___f_3724_; lean_object* v___f_3725_; lean_object* v___f_3726_; lean_object* v___f_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___f_3723_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_3724_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_3725_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_3726_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_3727_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_3727_, 0, v_chunk_3721_);
lean_closure_set(v___f_3727_, 1, v___f_3723_);
lean_closure_set(v___f_3727_, 2, v___f_3726_);
lean_closure_set(v___f_3727_, 3, v___f_3725_);
lean_closure_set(v___f_3727_, 4, v_stream_3720_);
lean_closure_set(v___f_3727_, 5, v___f_3724_);
v___x_3728_ = lean_unsigned_to_nat(0u);
v___x_3729_ = 0;
v___x_3730_ = lean_io_promise_new();
v___x_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
v___x_3733_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3728_, v___x_3729_, v___x_3732_, v___f_3727_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_3734_, lean_object* v_chunk_3735_, lean_object* v_a_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3734_, v_chunk_3735_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_3738_, lean_object* v_x_3739_){
_start:
{
if (lean_obj_tag(v_x_3739_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref(v_stream_3738_);
v_a_3741_ = lean_ctor_get(v_x_3739_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_x_3739_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3743_ = v_x_3739_;
v_isShared_3744_ = v_isSharedCheck_3749_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v_x_3739_);
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
v_a_3750_ = lean_ctor_get(v_x_3739_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v_x_3739_, 1);
if (lean_obj_tag(v_a_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3759_; 
lean_dec_ref(v_stream_3738_);
v_a_3751_ = lean_ctor_get(v_a_3750_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_a_3750_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3753_ = v_a_3750_;
v_isShared_3754_ = v_isSharedCheck_3759_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v_a_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3759_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
return v___x_3757_;
}
}
}
else
{
lean_object* v_a_3760_; 
v_a_3760_ = lean_ctor_get(v_a_3750_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v_a_3750_, 1);
if (lean_obj_tag(v_a_3760_) == 0)
{
lean_object* v___x_3761_; 
lean_dec_ref(v_stream_3738_);
v___x_3761_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3761_;
}
else
{
lean_object* v_val_3762_; uint8_t v___y_3764_; lean_object* v_data_3767_; lean_object* v_extensions_3768_; uint8_t v___x_3769_; 
v_val_3762_ = lean_ctor_get(v_a_3760_, 0);
lean_inc(v_val_3762_);
lean_dec_ref_known(v_a_3760_, 1);
v_data_3767_ = lean_ctor_get(v_val_3762_, 0);
v_extensions_3768_ = lean_ctor_get(v_val_3762_, 1);
v___x_3769_ = l_ByteArray_isEmpty(v_data_3767_);
if (v___x_3769_ == 0)
{
v___y_3764_ = v___x_3769_;
goto v___jp_3763_;
}
else
{
lean_object* v___x_3770_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v___x_3770_ = lean_array_get_size(v_extensions_3768_);
v___x_3771_ = lean_unsigned_to_nat(0u);
v___x_3772_ = lean_nat_dec_eq(v___x_3770_, v___x_3771_);
v___y_3764_ = v___x_3772_;
goto v___jp_3763_;
}
v___jp_3763_:
{
if (v___y_3764_ == 0)
{
lean_object* v___x_3765_; 
v___x_3765_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3738_, v_val_3762_);
return v___x_3765_;
}
else
{
lean_object* v___x_3766_; 
lean_dec(v_val_3762_);
lean_dec_ref(v_stream_3738_);
v___x_3766_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3766_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object* v_stream_3773_, lean_object* v_x_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_3773_, v_x_3774_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object* v_stream_3777_, lean_object* v_chunk_3778_, uint8_t v_incomplete_3779_){
_start:
{
lean_object* v___f_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_inc_ref(v_stream_3777_);
v___f_3781_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3781_, 0, v_stream_3777_);
v___x_3782_ = lean_unsigned_to_nat(0u);
v___x_3783_ = 0;
v___x_3784_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3777_, v_chunk_3778_, v_incomplete_3779_);
v___x_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
v___x_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
v___x_3787_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3782_, v___x_3783_, v___x_3786_, v___f_3781_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object* v_stream_3788_, lean_object* v_chunk_3789_, lean_object* v_incomplete_3790_, lean_object* v_a_3791_){
_start:
{
uint8_t v_incomplete_boxed_3792_; lean_object* v_res_3793_; 
v_incomplete_boxed_3792_ = lean_unbox(v_incomplete_3790_);
v_res_3793_ = l_Std_Http_Body_Stream_send(v_stream_3788_, v_chunk_3789_, v_incomplete_boxed_3792_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object* v_x_3794_){
_start:
{
uint8_t v___y_3797_; 
if (lean_obj_tag(v_x_3794_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3809_; 
v_a_3801_ = lean_ctor_get(v_x_3794_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_x_3794_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3803_ = v_x_3794_;
v_isShared_3804_ = v_isSharedCheck_3809_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v_x_3794_);
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
lean_object* v_a_3810_; lean_object* v_pendingConsumer_3811_; 
v_a_3810_ = lean_ctor_get(v_x_3794_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v_x_3794_, 1);
v_pendingConsumer_3811_ = lean_ctor_get(v_a_3810_, 1);
lean_inc(v_pendingConsumer_3811_);
lean_dec(v_a_3810_);
if (lean_obj_tag(v_pendingConsumer_3811_) == 0)
{
uint8_t v___x_3812_; 
v___x_3812_ = 0;
v___y_3797_ = v___x_3812_;
goto v___jp_3796_;
}
else
{
uint8_t v___x_3813_; 
lean_dec_ref_known(v_pendingConsumer_3811_, 1);
v___x_3813_ = 1;
v___y_3797_ = v___x_3813_;
goto v___jp_3796_;
}
}
v___jp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = lean_box(v___y_3797_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
return v___x_3800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object* v_x_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_3814_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object* v_a_3818_){
_start:
{
lean_object* v___f_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___f_3820_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_3821_ = lean_unsigned_to_nat(0u);
v___x_3822_ = 0;
v___x_3823_ = lean_st_ref_get(v_a_3818_);
v___x_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
v___x_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
v___x_3826_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3821_, v___x_3822_, v___x_3825_, v___f_3820_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object* v_a_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_3827_);
lean_dec(v_a_3827_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object* v___y_3830_, lean_object* v_x_3831_){
_start:
{
if (lean_obj_tag(v_x_3831_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3841_; 
v_a_3833_ = lean_ctor_get(v_x_3831_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_x_3831_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3835_ = v_x_3831_;
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v_x_3831_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
return v___x_3839_;
}
}
}
else
{
lean_object* v___x_3842_; 
lean_dec_ref_known(v_x_3831_, 1);
v___x_3842_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_3830_);
return v___x_3842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object* v___y_3843_, lean_object* v_x_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_3843_, v_x_3844_);
lean_dec(v___y_3843_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object* v___y_3847_){
_start:
{
lean_object* v___f_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_inc(v___y_3847_);
v___f_3849_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3849_, 0, v___y_3847_);
v___x_3850_ = lean_unsigned_to_nat(0u);
v___x_3851_ = 0;
v___x_3852_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3847_);
v___x_3853_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3850_, v___x_3851_, v___x_3852_, v___f_3849_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_3854_);
lean_dec(v___y_3854_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object* v_stream_3858_){
_start:
{
lean_object* v___f_3860_; lean_object* v___x_3861_; 
v___f_3860_ = ((lean_object*)(l_Std_Http_Body_Stream_hasInterest___closed__0));
v___x_3861_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3858_, v___f_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object* v_stream_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Std_Http_Body_Stream_hasInterest(v_stream_3862_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object* v_lose_3865_, lean_object* v___y_3866_, uint8_t v___x_3867_, lean_object* v_promise_3868_, lean_object* v_x_3869_){
_start:
{
if (lean_obj_tag(v_x_3869_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3879_; 
lean_dec_ref(v_lose_3865_);
v_a_3871_ = lean_ctor_get(v_x_3869_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v_x_3869_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3873_ = v_x_3869_;
v_isShared_3874_ = v_isSharedCheck_3879_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v_x_3869_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3879_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3871_);
v___x_3876_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3877_; 
v___x_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3876_);
return v___x_3877_;
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3893_; 
v_a_3880_ = lean_ctor_get(v_x_3869_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_x_3869_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3882_ = v_x_3869_;
v_isShared_3883_ = v_isSharedCheck_3893_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v_x_3869_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3893_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
uint8_t v___x_3884_; 
v___x_3884_ = lean_unbox(v_a_3880_);
lean_dec(v_a_3880_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; 
lean_del_object(v___x_3882_);
lean_inc(v___y_3866_);
v___x_3885_ = lean_apply_2(v_lose_3865_, v___y_3866_, lean_box(0));
return v___x_3885_;
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
lean_dec_ref(v_lose_3865_);
v___x_3886_ = lean_box(v___x_3867_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v___x_3886_);
v___x_3888_ = v___x_3882_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3889_ = lean_io_promise_resolve(v___x_3888_, v_promise_3868_);
v___x_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
v___x_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
return v___x_3891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object* v_lose_3894_, lean_object* v___y_3895_, lean_object* v___x_3896_, lean_object* v_promise_3897_, lean_object* v_x_3898_, lean_object* v___y_3899_){
_start:
{
uint8_t v___x_4067__boxed_3900_; lean_object* v_res_3901_; 
v___x_4067__boxed_3900_ = lean_unbox(v___x_3896_);
v_res_3901_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_3894_, v___y_3895_, v___x_4067__boxed_3900_, v_promise_3897_, v_x_3898_);
lean_dec(v_promise_3897_);
lean_dec(v___y_3895_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_3902_, lean_object* v_lose_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v_finished_3906_; lean_object* v_promise_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___f_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; uint8_t v___y_3914_; uint8_t v___x_3922_; 
v_finished_3906_ = lean_ctor_get(v_w_3902_, 0);
lean_inc(v_finished_3906_);
v_promise_3907_ = lean_ctor_get(v_w_3902_, 1);
lean_inc(v_promise_3907_);
lean_dec_ref(v_w_3902_);
v___x_3908_ = 0;
v___x_3909_ = lean_box(v___x_3908_);
lean_inc(v___y_3904_);
v___f_3910_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3910_, 0, v_lose_3903_);
lean_closure_set(v___f_3910_, 1, v___y_3904_);
lean_closure_set(v___f_3910_, 2, v___x_3909_);
lean_closure_set(v___f_3910_, 3, v_promise_3907_);
v___x_3911_ = lean_unsigned_to_nat(0u);
v___x_3912_ = lean_st_ref_take(v_finished_3906_);
v___x_3922_ = lean_unbox(v___x_3912_);
lean_dec(v___x_3912_);
if (v___x_3922_ == 0)
{
uint8_t v___x_3923_; 
v___x_3923_ = 1;
v___y_3914_ = v___x_3923_;
goto v___jp_3913_;
}
else
{
v___y_3914_ = v___x_3908_;
goto v___jp_3913_;
}
v___jp_3913_:
{
uint8_t v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3915_ = 1;
v___x_3916_ = lean_box(v___x_3915_);
v___x_3917_ = lean_st_ref_put(v_finished_3906_, v___x_3916_);
lean_dec(v_finished_3906_);
v___x_3918_ = lean_box(v___y_3914_);
v___x_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
v___x_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
v___x_3921_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3911_, v___x_3908_, v___x_3920_, v___f_3910_);
return v___x_3921_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object* v_w_3924_, lean_object* v_lose_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_3924_, v_lose_3925_, v___y_3926_);
lean_dec(v___y_3926_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object* v_w_3929_, lean_object* v_lose_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v_finished_3933_; lean_object* v_promise_3934_; uint8_t v___x_3935_; lean_object* v___x_3936_; lean_object* v___f_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; lean_object* v___x_3940_; uint8_t v___y_3942_; uint8_t v___x_3949_; 
v_finished_3933_ = lean_ctor_get(v_w_3929_, 0);
lean_inc(v_finished_3933_);
v_promise_3934_ = lean_ctor_get(v_w_3929_, 1);
lean_inc(v_promise_3934_);
lean_dec_ref(v_w_3929_);
v___x_3935_ = 1;
v___x_3936_ = lean_box(v___x_3935_);
lean_inc(v___y_3931_);
v___f_3937_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3937_, 0, v_lose_3930_);
lean_closure_set(v___f_3937_, 1, v___y_3931_);
lean_closure_set(v___f_3937_, 2, v___x_3936_);
lean_closure_set(v___f_3937_, 3, v_promise_3934_);
v___x_3938_ = lean_unsigned_to_nat(0u);
v___x_3939_ = 0;
v___x_3940_ = lean_st_ref_take(v_finished_3933_);
v___x_3949_ = lean_unbox(v___x_3940_);
lean_dec(v___x_3940_);
if (v___x_3949_ == 0)
{
v___y_3942_ = v___x_3935_;
goto v___jp_3941_;
}
else
{
v___y_3942_ = v___x_3939_;
goto v___jp_3941_;
}
v___jp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3943_ = lean_box(v___x_3935_);
v___x_3944_ = lean_st_ref_put(v_finished_3933_, v___x_3943_);
lean_dec(v_finished_3933_);
v___x_3945_ = lean_box(v___y_3942_);
v___x_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
v___x_3948_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3938_, v___x_3939_, v___x_3947_, v___f_3937_);
return v___x_3948_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_3950_, lean_object* v_lose_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_3950_, v_lose_3951_, v___y_3952_);
lean_dec(v___y_3952_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_3971_){
_start:
{
if (lean_obj_tag(v_x_3971_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3981_; 
v_a_3973_ = lean_ctor_get(v_x_3971_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v_x_3971_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3975_ = v_x_3971_;
v_isShared_3976_ = v_isSharedCheck_3981_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v_x_3971_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3981_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
return v___x_3979_;
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v_pendingConsumer_3983_; 
v_a_3982_ = lean_ctor_get(v_x_3971_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v_x_3971_, 1);
v_pendingConsumer_3983_ = lean_ctor_get(v_a_3982_, 1);
if (lean_obj_tag(v_pendingConsumer_3983_) == 0)
{
uint8_t v_closed_3984_; 
v_closed_3984_ = lean_ctor_get_uint8(v_a_3982_, sizeof(void*)*6);
lean_dec(v_a_3982_);
if (v_closed_3984_ == 0)
{
lean_object* v___x_3985_; 
v___x_3985_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_3985_;
}
else
{
lean_object* v___x_3986_; 
v___x_3986_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_3986_;
}
}
else
{
lean_object* v___x_3987_; 
lean_dec(v_a_3982_);
v___x_3987_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_3987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_3998_, lean_object* v___y_3999_, lean_object* v_x_4000_){
_start:
{
if (lean_obj_tag(v_x_4000_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v_waiter_3998_);
v_a_4002_ = lean_ctor_get(v_x_4000_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_x_4000_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4004_ = v_x_4000_;
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v_x_4000_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4008_; 
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
return v___x_4008_;
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v_pendingConsumer_4012_; 
v_a_4011_ = lean_ctor_get(v_x_4000_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v_x_4000_, 1);
v_pendingConsumer_4012_ = lean_ctor_get(v_a_4011_, 1);
lean_inc(v_pendingConsumer_4012_);
if (lean_obj_tag(v_pendingConsumer_4012_) == 0)
{
uint8_t v_closed_4013_; 
v_closed_4013_ = lean_ctor_get_uint8(v_a_4011_, sizeof(void*)*6);
if (v_closed_4013_ == 0)
{
lean_object* v_interestWaiter_4014_; 
v_interestWaiter_4014_ = lean_ctor_get(v_a_4011_, 2);
if (lean_obj_tag(v_interestWaiter_4014_) == 0)
{
lean_object* v_pendingProducer_4015_; lean_object* v_knownSize_4016_; lean_object* v_pendingIncompleteChunk_4017_; lean_object* v_closeError_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4028_; 
v_pendingProducer_4015_ = lean_ctor_get(v_a_4011_, 0);
v_knownSize_4016_ = lean_ctor_get(v_a_4011_, 3);
v_pendingIncompleteChunk_4017_ = lean_ctor_get(v_a_4011_, 4);
v_closeError_4018_ = lean_ctor_get(v_a_4011_, 5);
v_isSharedCheck_4028_ = !lean_is_exclusive(v_a_4011_);
if (v_isSharedCheck_4028_ == 0)
{
lean_object* v_unused_4029_; lean_object* v_unused_4030_; 
v_unused_4029_ = lean_ctor_get(v_a_4011_, 2);
lean_dec(v_unused_4029_);
v_unused_4030_ = lean_ctor_get(v_a_4011_, 1);
lean_dec(v_unused_4030_);
v___x_4020_ = v_a_4011_;
v_isShared_4021_ = v_isSharedCheck_4028_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_closeError_4018_);
lean_inc(v_pendingIncompleteChunk_4017_);
lean_inc(v_knownSize_4016_);
lean_inc(v_pendingProducer_4015_);
lean_dec(v_a_4011_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4028_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4022_, 0, v_waiter_3998_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 2, v___x_4022_);
v___x_4024_ = v___x_4020_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_pendingProducer_4015_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v_pendingConsumer_4012_);
lean_ctor_set(v_reuseFailAlloc_4027_, 2, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4027_, 3, v_knownSize_4016_);
lean_ctor_set(v_reuseFailAlloc_4027_, 4, v_pendingIncompleteChunk_4017_);
lean_ctor_set(v_reuseFailAlloc_4027_, 5, v_closeError_4018_);
lean_ctor_set_uint8(v_reuseFailAlloc_4027_, sizeof(void*)*6, v_closed_4013_);
v___x_4024_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = lean_st_ref_swap(v___y_3999_, v___x_4024_);
lean_dec(v___x_4025_);
v___x_4026_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4026_;
}
}
}
else
{
lean_object* v___x_4031_; 
lean_dec(v_a_4011_);
lean_dec_ref(v_waiter_3998_);
v___x_4031_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_4031_;
}
}
else
{
lean_object* v___f_4032_; lean_object* v___x_4033_; 
lean_dec(v_a_4011_);
v___f_4032_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4033_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_3998_, v___f_4032_, v___y_3999_);
return v___x_4033_;
}
}
else
{
lean_object* v___f_4034_; lean_object* v___x_4035_; 
lean_dec_ref_known(v_pendingConsumer_4012_, 1);
lean_dec(v_a_4011_);
v___f_4034_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4035_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_3998_, v___f_4034_, v___y_3999_);
return v___x_4035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_4036_, lean_object* v___y_4037_, lean_object* v_x_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_4036_, v___y_4037_, v_x_4038_);
lean_dec(v___y_4037_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_4041_, lean_object* v___f_4042_, lean_object* v_x_4043_){
_start:
{
if (lean_obj_tag(v_x_4043_) == 0)
{
lean_object* v___x_4045_; 
lean_dec_ref(v___f_4042_);
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v_x_4043_);
return v___x_4045_;
}
else
{
lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4057_; 
v_isSharedCheck_4057_ = !lean_is_exclusive(v_x_4043_);
if (v_isSharedCheck_4057_ == 0)
{
lean_object* v_unused_4058_; 
v_unused_4058_ = lean_ctor_get(v_x_4043_, 0);
lean_dec(v_unused_4058_);
v___x_4047_ = v_x_4043_;
v_isShared_4048_ = v_isSharedCheck_4057_;
goto v_resetjp_4046_;
}
else
{
lean_dec(v_x_4043_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4057_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4049_; uint8_t v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4053_; 
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = 0;
v___x_4051_ = lean_st_ref_get(v___y_4041_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v___x_4051_);
v___x_4053_ = v___x_4047_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4051_);
v___x_4053_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
v___x_4055_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4049_, v___x_4050_, v___x_4054_, v___f_4042_);
return v___x_4055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_4059_, lean_object* v___f_4060_, lean_object* v_x_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_4059_, v___f_4060_, v_x_4061_);
lean_dec(v___y_4059_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v___f_4067_; lean_object* v___f_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
lean_inc_n(v___y_4065_, 2);
v___f_4067_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_4067_, 0, v_waiter_4064_);
lean_closure_set(v___f_4067_, 1, v___y_4065_);
v___f_4068_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4068_, 0, v___y_4065_);
lean_closure_set(v___f_4068_, 1, v___f_4067_);
v___x_4069_ = lean_unsigned_to_nat(0u);
v___x_4070_ = 0;
v___x_4071_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4065_);
v___x_4072_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4069_, v___x_4070_, v___x_4071_, v___f_4068_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_4073_, v___y_4074_);
lean_dec(v___y_4074_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_4077_, lean_object* v_waiter_4078_){
_start:
{
lean_object* v___f_4080_; lean_object* v___x_4081_; 
v___f_4080_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4080_, 0, v_waiter_4078_);
v___x_4081_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_4077_, v___f_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_4082_, lean_object* v_waiter_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_4082_, v_waiter_4083_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_4086_, lean_object* v___f_4087_, lean_object* v_x_4088_){
_start:
{
if (lean_obj_tag(v_x_4088_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4098_; 
lean_dec_ref(v___f_4087_);
v_a_4090_ = lean_ctor_get(v_x_4088_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_x_4088_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4092_ = v_x_4088_;
v_isShared_4093_ = v_isSharedCheck_4098_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v_x_4088_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4098_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
return v___x_4096_;
}
}
}
else
{
lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4110_; 
v_isSharedCheck_4110_ = !lean_is_exclusive(v_x_4088_);
if (v_isSharedCheck_4110_ == 0)
{
lean_object* v_unused_4111_; 
v_unused_4111_ = lean_ctor_get(v_x_4088_, 0);
lean_dec(v_unused_4111_);
v___x_4100_ = v_x_4088_;
v_isShared_4101_ = v_isSharedCheck_4110_;
goto v_resetjp_4099_;
}
else
{
lean_dec(v_x_4088_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4110_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; uint8_t v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4106_; 
v___x_4102_ = lean_unsigned_to_nat(0u);
v___x_4103_ = 0;
v___x_4104_ = lean_st_ref_get(v___y_4086_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4104_);
v___x_4106_ = v___x_4100_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4104_);
v___x_4106_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
v___x_4108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4102_, v___x_4103_, v___x_4107_, v___f_4087_);
return v___x_4108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_4112_, lean_object* v___f_4113_, lean_object* v_x_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_4112_, v___f_4113_, v_x_4114_);
lean_dec(v___y_4112_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___f_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_inc(v___y_4118_);
v___f_4120_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_4120_, 0, v___y_4118_);
lean_closure_set(v___f_4120_, 1, v___f_4117_);
v___x_4121_ = lean_unsigned_to_nat(0u);
v___x_4122_ = 0;
v___x_4123_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4118_);
v___x_4124_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4121_, v___x_4122_, v___x_4123_, v___f_4120_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_4125_, v___y_4126_);
lean_dec(v___y_4126_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_4132_){
_start:
{
lean_object* v___f_4133_; lean_object* v___f_4134_; lean_object* v___f_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___f_4133_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_4132_, 2);
v___f_4134_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_4134_, 0, v_stream_4132_);
v___f_4135_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_4136_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4136_, 0, lean_box(0));
lean_closure_set(v___x_4136_, 1, lean_box(0));
lean_closure_set(v___x_4136_, 2, v_stream_4132_);
lean_closure_set(v___x_4136_, 3, v___f_4135_);
v___x_4137_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4137_, 0, lean_box(0));
lean_closure_set(v___x_4137_, 1, lean_box(0));
lean_closure_set(v___x_4137_, 2, v_stream_4132_);
lean_closure_set(v___x_4137_, 3, v___f_4133_);
v___x_4138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4136_);
lean_ctor_set(v___x_4138_, 1, v___f_4134_);
lean_ctor_set(v___x_4138_, 2, v___x_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v_x_4139_, lean_object* v_x_4140_){
_start:
{
if (lean_obj_tag(v_x_4140_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v_x_4139_);
v_a_4142_ = lean_ctor_get(v_x_4140_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v_x_4140_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4144_ = v_x_4140_;
v_isShared_4145_ = v_isSharedCheck_4150_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v_x_4140_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4150_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
lean_object* v___x_4148_; 
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
return v___x_4148_;
}
}
}
else
{
lean_object* v___x_4151_; 
lean_dec_ref_known(v_x_4140_, 1);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v_x_4139_);
return v___x_4151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0___boxed(lean_object* v_x_4152_, lean_object* v_x_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Std_Http_Body_stream___lam__0(v_x_4152_, v_x_4153_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_a_4156_, lean_object* v_x_4157_){
_start:
{
if (lean_obj_tag(v_x_4157_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4160_; 
v_a_4159_ = lean_ctor_get(v_x_4157_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v_x_4157_, 1);
v___x_4160_ = l_Std_Http_Body_Stream_closeWithError(v_a_4156_, v_a_4159_);
return v___x_4160_;
}
else
{
lean_object* v___x_4161_; 
lean_dec_ref(v_a_4156_);
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v_x_4157_);
return v___x_4161_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_a_4162_, lean_object* v_x_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Std_Http_Body_stream___lam__1(v_a_4162_, v_x_4163_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v_a_4166_, lean_object* v_x_4167_){
_start:
{
if (lean_obj_tag(v_x_4167_) == 0)
{
lean_object* v___x_4169_; 
lean_dec_ref(v_a_4166_);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v_x_4167_);
return v___x_4169_;
}
else
{
lean_object* v___x_4170_; 
lean_dec_ref_known(v_x_4167_, 1);
v___x_4170_ = l_Std_Http_Body_Stream_close(v_a_4166_);
return v___x_4170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v_a_4171_, lean_object* v_x_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Std_Http_Body_stream___lam__2(v_a_4171_, v_x_4172_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_gen_4175_, lean_object* v_a_4176_, lean_object* v___x_4177_, uint8_t v___x_4178_, lean_object* v___f_4179_, lean_object* v___f_4180_){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4182_ = lean_apply_2(v_gen_4175_, v_a_4176_, lean_box(0));
lean_inc(v___x_4177_);
v___x_4183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4177_, v___x_4178_, v___x_4182_, v___f_4179_);
v___x_4184_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4177_, v___x_4178_, v___x_4183_, v___f_4180_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_gen_4185_, lean_object* v_a_4186_, lean_object* v___x_4187_, lean_object* v___x_4188_, lean_object* v___f_4189_, lean_object* v___f_4190_, lean_object* v___y_4191_){
_start:
{
uint8_t v___x_1066__boxed_4192_; lean_object* v_res_4193_; 
v___x_1066__boxed_4192_ = lean_unbox(v___x_4188_);
v_res_4193_ = l_Std_Http_Body_stream___lam__3(v_gen_4185_, v_a_4186_, v___x_4187_, v___x_1066__boxed_4192_, v___f_4189_, v___f_4190_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_4194_, lean_object* v_a_4195_, lean_object* v___f_4196_, lean_object* v___f_4197_, lean_object* v___f_4198_, lean_object* v_x_4199_){
_start:
{
if (lean_obj_tag(v_x_4199_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v___f_4198_);
lean_dec_ref(v___f_4197_);
lean_dec_ref(v___f_4196_);
lean_dec_ref(v_a_4195_);
lean_dec_ref(v_gen_4194_);
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
lean_object* v___x_4210_; uint8_t v___x_4211_; lean_object* v___x_4212_; lean_object* v___f_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
lean_dec_ref_known(v_x_4199_, 1);
v___x_4210_ = lean_unsigned_to_nat(0u);
v___x_4211_ = 0;
v___x_4212_ = lean_box(v___x_4211_);
v___f_4213_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 7, 6);
lean_closure_set(v___f_4213_, 0, v_gen_4194_);
lean_closure_set(v___f_4213_, 1, v_a_4195_);
lean_closure_set(v___f_4213_, 2, v___x_4210_);
lean_closure_set(v___f_4213_, 3, v___x_4212_);
lean_closure_set(v___f_4213_, 4, v___f_4196_);
lean_closure_set(v___f_4213_, 5, v___f_4197_);
v___x_4214_ = lean_io_as_task(v___f_4213_, v___x_4210_);
lean_dec_ref(v___x_4214_);
v___x_4215_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4210_, v___x_4211_, v___x_4215_, v___f_4198_);
return v___x_4216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_4217_, lean_object* v_a_4218_, lean_object* v___f_4219_, lean_object* v___f_4220_, lean_object* v___f_4221_, lean_object* v_x_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Std_Http_Body_stream___lam__4(v_gen_4217_, v_a_4218_, v___f_4219_, v___f_4220_, v___f_4221_, v_x_4222_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5(lean_object* v___x_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; lean_object* v_pendingProducer_4229_; lean_object* v_pendingConsumer_4230_; lean_object* v_interestWaiter_4231_; uint8_t v_closed_4232_; lean_object* v_pendingIncompleteChunk_4233_; lean_object* v_closeError_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4243_; 
v___x_4228_ = lean_st_ref_take(v___y_4226_);
v_pendingProducer_4229_ = lean_ctor_get(v___x_4228_, 0);
v_pendingConsumer_4230_ = lean_ctor_get(v___x_4228_, 1);
v_interestWaiter_4231_ = lean_ctor_get(v___x_4228_, 2);
v_closed_4232_ = lean_ctor_get_uint8(v___x_4228_, sizeof(void*)*6);
v_pendingIncompleteChunk_4233_ = lean_ctor_get(v___x_4228_, 4);
v_closeError_4234_ = lean_ctor_get(v___x_4228_, 5);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4243_ == 0)
{
lean_object* v_unused_4244_; 
v_unused_4244_ = lean_ctor_get(v___x_4228_, 3);
lean_dec(v_unused_4244_);
v___x_4236_ = v___x_4228_;
v_isShared_4237_ = v_isSharedCheck_4243_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_closeError_4234_);
lean_inc(v_pendingIncompleteChunk_4233_);
lean_inc(v_interestWaiter_4231_);
lean_inc(v_pendingConsumer_4230_);
lean_inc(v_pendingProducer_4229_);
lean_dec(v___x_4228_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4243_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 3, v___x_4225_);
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_pendingProducer_4229_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v_pendingConsumer_4230_);
lean_ctor_set(v_reuseFailAlloc_4242_, 2, v_interestWaiter_4231_);
lean_ctor_set(v_reuseFailAlloc_4242_, 3, v___x_4225_);
lean_ctor_set(v_reuseFailAlloc_4242_, 4, v_pendingIncompleteChunk_4233_);
lean_ctor_set(v_reuseFailAlloc_4242_, 5, v_closeError_4234_);
lean_ctor_set_uint8(v_reuseFailAlloc_4242_, sizeof(void*)*6, v_closed_4232_);
v___x_4239_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = lean_st_ref_put(v___y_4226_, v___x_4239_);
v___x_4241_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object* v___x_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Std_Http_Body_stream___lam__5(v___x_4245_, v___y_4246_);
lean_dec(v___y_4246_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6(lean_object* v_gen_4253_, lean_object* v_x_4254_){
_start:
{
if (lean_obj_tag(v_x_4254_) == 0)
{
lean_object* v___x_4256_; 
lean_dec_ref(v_gen_4253_);
v___x_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4256_, 0, v_x_4254_);
return v___x_4256_;
}
else
{
lean_object* v_a_4257_; lean_object* v___f_4258_; lean_object* v___f_4259_; lean_object* v___f_4260_; lean_object* v___f_4261_; lean_object* v___f_4262_; lean_object* v___x_4263_; uint8_t v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v_a_4257_ = lean_ctor_get(v_x_4254_, 0);
lean_inc_n(v_a_4257_, 4);
v___f_4258_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4258_, 0, v_x_4254_);
v___f_4259_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4259_, 0, v_a_4257_);
v___f_4260_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4260_, 0, v_a_4257_);
v___f_4261_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 7, 5);
lean_closure_set(v___f_4261_, 0, v_gen_4253_);
lean_closure_set(v___f_4261_, 1, v_a_4257_);
lean_closure_set(v___f_4261_, 2, v___f_4260_);
lean_closure_set(v___f_4261_, 3, v___f_4259_);
lean_closure_set(v___f_4261_, 4, v___f_4258_);
v___f_4262_ = ((lean_object*)(l_Std_Http_Body_stream___lam__6___closed__1));
v___x_4263_ = lean_unsigned_to_nat(0u);
v___x_4264_ = 0;
v___x_4265_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4257_, v___f_4262_);
v___x_4266_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4263_, v___x_4264_, v___x_4265_, v___f_4261_);
return v___x_4266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object* v_gen_4267_, lean_object* v_x_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Std_Http_Body_stream___lam__6(v_gen_4267_, v_x_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object* v_gen_4271_){
_start:
{
lean_object* v___f_4273_; lean_object* v___x_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___f_4273_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4273_, 0, v_gen_4271_);
v___x_4274_ = lean_unsigned_to_nat(0u);
v___x_4275_ = 0;
v___x_4276_ = l_Std_Http_Body_mkStream();
v___x_4277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4274_, v___x_4275_, v___x_4276_, v___f_4273_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_4278_, lean_object* v_a_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Std_Http_Body_stream(v_gen_4278_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v___x_4281_, lean_object* v_content_4282_, lean_object* v_s_4283_, lean_object* v_x_4284_){
_start:
{
if (lean_obj_tag(v_x_4284_) == 0)
{
lean_object* v___x_4286_; 
lean_dec_ref(v_s_4283_);
lean_dec_ref(v_content_4282_);
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v_x_4284_);
return v___x_4286_;
}
else
{
lean_object* v___x_4287_; uint8_t v___x_4288_; 
lean_dec_ref_known(v_x_4284_, 1);
v___x_4287_ = lean_unsigned_to_nat(0u);
v___x_4288_ = lean_nat_dec_lt(v___x_4287_, v___x_4281_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; 
lean_dec_ref(v_s_4283_);
lean_dec_ref(v_content_4282_);
v___x_4289_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4289_;
}
else
{
lean_object* v___x_4290_; uint8_t v___x_4291_; lean_object* v___x_4292_; 
v___x_4290_ = l_Std_Http_Chunk_ofByteArray(v_content_4282_);
v___x_4291_ = 0;
v___x_4292_ = l_Std_Http_Body_Stream_send(v_s_4283_, v___x_4290_, v___x_4291_);
return v___x_4292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v___x_4293_, lean_object* v_content_4294_, lean_object* v_s_4295_, lean_object* v_x_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Std_Http_Body_fromBytes___lam__0(v___x_4293_, v_content_4294_, v_s_4295_, v_x_4296_);
lean_dec(v___x_4293_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object* v_content_4299_, lean_object* v_s_4300_){
_start:
{
lean_object* v___x_4302_; lean_object* v___f_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___f_4306_; lean_object* v___x_4307_; uint8_t v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4302_ = lean_byte_array_size(v_content_4299_);
lean_inc_ref(v_s_4300_);
v___f_4303_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4303_, 0, v___x_4302_);
lean_closure_set(v___f_4303_, 1, v_content_4299_);
lean_closure_set(v___f_4303_, 2, v_s_4300_);
v___x_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
v___x_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
v___f_4306_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4306_, 0, v___x_4305_);
v___x_4307_ = lean_unsigned_to_nat(0u);
v___x_4308_ = 0;
v___x_4309_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_4300_, v___f_4306_);
v___x_4310_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4307_, v___x_4308_, v___x_4309_, v___f_4303_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object* v_content_4311_, lean_object* v_s_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Std_Http_Body_fromBytes___lam__2(v_content_4311_, v_s_4312_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_4315_){
_start:
{
lean_object* v___f_4317_; lean_object* v___x_4318_; 
v___f_4317_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4317_, 0, v_content_4315_);
v___x_4318_ = l_Std_Http_Body_stream(v___f_4317_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_4319_, lean_object* v_a_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Std_Http_Body_fromBytes(v_content_4319_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1(lean_object* v_a_4322_, lean_object* v___f_4323_, lean_object* v_x_4324_){
_start:
{
if (lean_obj_tag(v_x_4324_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4334_; 
lean_dec_ref(v___f_4323_);
lean_dec_ref(v_a_4322_);
v_a_4326_ = lean_ctor_get(v_x_4324_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v_x_4324_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4328_ = v_x_4324_;
v_isShared_4329_ = v_isSharedCheck_4334_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v_x_4324_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4334_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
lean_object* v___x_4332_; 
v___x_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
return v___x_4332_;
}
}
}
else
{
lean_object* v___x_4335_; uint8_t v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
lean_dec_ref_known(v_x_4324_, 1);
v___x_4335_ = lean_unsigned_to_nat(0u);
v___x_4336_ = 0;
v___x_4337_ = l_Std_Http_Body_Stream_close(v_a_4322_);
v___x_4338_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4335_, v___x_4336_, v___x_4337_, v___f_4323_);
return v___x_4338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1___boxed(lean_object* v_a_4339_, lean_object* v___f_4340_, lean_object* v_x_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Std_Http_Body_empty___lam__1(v_a_4339_, v___f_4340_, v_x_4341_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_x_4350_){
_start:
{
if (lean_obj_tag(v_x_4350_) == 0)
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v_x_4350_);
return v___x_4352_;
}
else
{
lean_object* v_a_4353_; lean_object* v___f_4354_; lean_object* v___f_4355_; lean_object* v___x_4356_; lean_object* v___f_4357_; uint8_t v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_a_4353_ = lean_ctor_get(v_x_4350_, 0);
lean_inc_n(v_a_4353_, 2);
v___f_4354_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4354_, 0, v_x_4350_);
v___f_4355_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4355_, 0, v_a_4353_);
lean_closure_set(v___f_4355_, 1, v___f_4354_);
v___x_4356_ = lean_unsigned_to_nat(0u);
v___f_4357_ = ((lean_object*)(l_Std_Http_Body_empty___lam__2___closed__2));
v___x_4358_ = 0;
v___x_4359_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4353_, v___f_4357_);
v___x_4360_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4356_, v___x_4358_, v___x_4359_, v___f_4355_);
return v___x_4360_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_x_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Std_Http_Body_empty___lam__2(v_x_4361_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___f_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___f_4366_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_4367_ = lean_unsigned_to_nat(0u);
v___x_4368_ = 0;
v___x_4369_ = l_Std_Http_Body_mkStream();
v___x_4370_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4367_, v___x_4368_, v___x_4369_, v___f_4366_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Std_Http_Body_empty();
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_4395_, lean_object* v_f_4396_){
_start:
{
lean_object* v_line_4397_; lean_object* v_body_4398_; lean_object* v_extensions_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4407_; 
v_line_4397_ = lean_ctor_get(v_f_4396_, 0);
v_body_4398_ = lean_ctor_get(v_f_4396_, 1);
v_extensions_4399_ = lean_ctor_get(v_f_4396_, 2);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_f_4396_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4401_ = v_f_4396_;
v_isShared_4402_ = v_isSharedCheck_4407_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_extensions_4399_);
lean_inc(v_body_4398_);
lean_inc(v_line_4397_);
lean_dec(v_f_4396_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4407_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; lean_object* v___x_4405_; 
v___x_4403_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4395_, v_body_4398_);
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 1, v___x_4403_);
v___x_4405_ = v___x_4401_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_line_4397_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v___x_4403_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v_extensions_4399_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_4411_, lean_object* v_x_4412_){
_start:
{
if (lean_obj_tag(v_x_4412_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4422_; 
lean_dec_ref(v___x_4411_);
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
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4442_; 
v_a_4423_ = lean_ctor_get(v_x_4412_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_x_4412_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4425_ = v_x_4412_;
v_isShared_4426_ = v_isSharedCheck_4442_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v_x_4412_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4442_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v_line_4427_; lean_object* v_body_4428_; lean_object* v_extensions_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4441_; 
v_line_4427_ = lean_ctor_get(v_a_4423_, 0);
v_body_4428_ = lean_ctor_get(v_a_4423_, 1);
v_extensions_4429_ = lean_ctor_get(v_a_4423_, 2);
v_isSharedCheck_4441_ = !lean_is_exclusive(v_a_4423_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4431_ = v_a_4423_;
v_isShared_4432_ = v_isSharedCheck_4441_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_extensions_4429_);
lean_inc(v_body_4428_);
lean_inc(v_line_4427_);
lean_dec(v_a_4423_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4441_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4433_; lean_object* v___x_4435_; 
v___x_4433_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4411_, v_body_4428_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 1, v___x_4433_);
v___x_4435_ = v___x_4431_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_line_4427_);
lean_ctor_set(v_reuseFailAlloc_4440_, 1, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4440_, 2, v_extensions_4429_);
v___x_4435_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
lean_object* v___x_4437_; 
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4435_);
v___x_4437_ = v___x_4425_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4435_);
v___x_4437_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
return v___x_4438_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_4443_, lean_object* v_x_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_4443_, v_x_4444_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_4447_, lean_object* v_action_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; uint8_t v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4451_ = lean_unsigned_to_nat(0u);
v___x_4452_ = 0;
lean_inc_ref(v___y_4449_);
v___x_4453_ = lean_apply_2(v_action_4448_, v___y_4449_, lean_box(0));
v___x_4454_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4451_, v___x_4452_, v___x_4453_, v___f_4447_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_4455_, lean_object* v_action_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_4455_, v_action_4456_, v___y_4457_);
lean_dec_ref(v___y_4457_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_4465_, lean_object* v_action_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v___x_4469_; uint8_t v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4469_ = lean_unsigned_to_nat(0u);
v___x_4470_ = 0;
v___x_4471_ = lean_apply_1(v_action_4466_, lean_box(0));
v___x_4472_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4469_, v___x_4470_, v___x_4471_, v___f_4465_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_4473_, lean_object* v_action_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_4473_, v_action_4474_, v___y_4475_);
lean_dec_ref(v___y_4475_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_4481_, lean_object* v_x_4482_){
_start:
{
if (lean_obj_tag(v_x_4482_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4492_; 
v_a_4484_ = lean_ctor_get(v_x_4482_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v_x_4482_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4486_ = v_x_4482_;
v_isShared_4487_ = v_isSharedCheck_4492_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v_x_4482_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4492_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4490_; 
v___x_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
return v___x_4490_;
}
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4502_; 
v_a_4493_ = lean_ctor_get(v_x_4482_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v_x_4482_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4495_ = v_x_4482_;
v_isShared_4496_ = v_isSharedCheck_4502_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v_x_4482_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4502_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4497_; lean_object* v___x_4499_; 
v___x_4497_ = l_Std_Http_Request_Builder_body___redArg(v_builder_4481_, v_a_4493_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4497_);
v___x_4499_ = v___x_4495_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4497_);
v___x_4499_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
lean_object* v___x_4500_; 
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
return v___x_4500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_4503_, lean_object* v_x_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_4503_, v_x_4504_);
lean_dec_ref(v_builder_4503_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_4507_, lean_object* v_gen_4508_){
_start:
{
lean_object* v___f_4510_; lean_object* v___x_4511_; uint8_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___f_4510_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4510_, 0, v_builder_4507_);
v___x_4511_ = lean_unsigned_to_nat(0u);
v___x_4512_ = 0;
v___x_4513_ = l_Std_Http_Body_stream(v_gen_4508_);
v___x_4514_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4511_, v___x_4512_, v___x_4513_, v___f_4510_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_4515_, lean_object* v_gen_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Std_Http_Request_Builder_stream(v_builder_4515_, v_gen_4516_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_4519_, lean_object* v_x_4520_){
_start:
{
if (lean_obj_tag(v_x_4520_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4530_; 
v_a_4522_ = lean_ctor_get(v_x_4520_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v_x_4520_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4524_ = v_x_4520_;
v_isShared_4525_ = v_isSharedCheck_4530_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v_x_4520_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4530_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4522_);
v___x_4527_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
lean_object* v___x_4528_; 
v___x_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
return v___x_4528_;
}
}
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4540_; 
v_a_4531_ = lean_ctor_get(v_x_4520_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v_x_4520_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4533_ = v_x_4520_;
v_isShared_4534_ = v_isSharedCheck_4540_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v_x_4520_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4540_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4535_; lean_object* v___x_4537_; 
v___x_4535_ = l_Std_Http_Response_Builder_body___redArg(v_builder_4519_, v_a_4531_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 0, v___x_4535_);
v___x_4537_ = v___x_4533_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4535_);
v___x_4537_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
lean_object* v___x_4538_; 
v___x_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4537_);
return v___x_4538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_4541_, lean_object* v_x_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_4541_, v_x_4542_);
lean_dec_ref(v_builder_4541_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_4545_, lean_object* v_gen_4546_){
_start:
{
lean_object* v___f_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___f_4548_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4548_, 0, v_builder_4545_);
v___x_4549_ = lean_unsigned_to_nat(0u);
v___x_4550_ = 0;
v___x_4551_ = l_Std_Http_Body_stream(v_gen_4546_);
v___x_4552_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4549_, v___x_4550_, v___x_4551_, v___f_4548_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_4553_, lean_object* v_gen_4554_, lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Std_Http_Response_Builder_stream(v_builder_4553_, v_gen_4554_);
return v_res_4556_;
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

// Lean compiler output
// Module: Std.Http.Data.Body.Stream
// Imports: public import Std.Sync public import Std.Async public import Std.Http.Data.Request public import Std.Http.Data.Response public import Std.Http.Data.Chunk public import Std.Http.Data.Body.Basic public import Std.Http.Data.Body.Any public import Init.Data.ByteArray.Basic
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_promise_7_; lean_object* v___x_8_; 
v_promise_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_promise_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_promise_7_);
return v___x_8_;
}
else
{
lean_object* v_finished_9_; lean_object* v___x_10_; 
v_finished_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_finished_9_);
lean_dec_ref_known(v_t_5_, 1);
v___x_10_ = lean_apply_1(v_k_6_, v_finished_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim___redArg(lean_object* v_t_23_, lean_object* v_normal_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_23_, v_normal_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_normal_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_27_, v_normal_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim___redArg(lean_object* v_t_31_, lean_object* v_select_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_31_, v_select_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_select_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_35_, v_select_37_);
return v___x_38_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(lean_object* v_x_39_, lean_object* v_w_40_, lean_object* v_lose_41_){
_start:
{
lean_object* v_finished_43_; lean_object* v_promise_44_; lean_object* v___x_45_; uint8_t v___y_47_; uint8_t v___x_54_; 
v_finished_43_ = lean_ctor_get(v_w_40_, 0);
v_promise_44_ = lean_ctor_get(v_w_40_, 1);
v___x_45_ = lean_st_ref_take(v_finished_43_);
v___x_54_ = lean_unbox(v___x_45_);
lean_dec(v___x_45_);
if (v___x_54_ == 0)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
v___y_47_ = v___x_55_;
goto v___jp_46_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
v___y_47_ = v___x_56_;
goto v___jp_46_;
}
v___jp_46_:
{
uint8_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = 1;
v___x_49_ = lean_box(v___x_48_);
v___x_50_ = lean_st_ref_put(v_finished_43_, v___x_49_);
if (v___y_47_ == 0)
{
lean_object* v___x_51_; uint8_t v___x_52_; 
lean_dec_ref(v_x_39_);
v___x_51_ = lean_apply_1(v_lose_41_, lean_box(0));
v___x_52_ = lean_unbox(v___x_51_);
return v___x_52_;
}
else
{
lean_object* v___x_53_; 
lean_dec_ref(v_lose_41_);
v___x_53_ = lean_io_promise_resolve(v_x_39_, v_promise_44_);
return v___y_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0___boxed(lean_object* v_x_57_, lean_object* v_w_58_, lean_object* v_lose_59_, lean_object* v___y_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_57_, v_w_58_, v_lose_59_);
lean_dec_ref(v_w_58_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(uint8_t v___x_63_){
_start:
{
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed(lean_object* v___x_65_, lean_object* v___y_66_){
_start:
{
uint8_t v___x_312__boxed_67_; uint8_t v_res_68_; lean_object* v_r_69_; 
v___x_312__boxed_67_ = lean_unbox(v___x_65_);
v_res_68_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(v___x_312__boxed_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(lean_object* v_c_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_c_73_) == 0)
{
lean_object* v_promise_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_promise_76_ = lean_ctor_get(v_c_73_, 0);
v___x_77_ = lean_io_promise_resolve(v_x_74_, v_promise_76_);
v___x_78_ = 1;
return v___x_78_;
}
else
{
lean_object* v_finished_79_; lean_object* v_lose_80_; uint8_t v___x_81_; 
v_finished_79_ = lean_ctor_get(v_c_73_, 0);
v_lose_80_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_81_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_74_, v_finished_79_, v_lose_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed(lean_object* v_c_82_, lean_object* v_x_83_, lean_object* v_a_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_c_82_, v_x_83_);
lean_dec_ref(v_c_82_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(uint8_t v_x_87_, lean_object* v_w_88_, lean_object* v_lose_89_){
_start:
{
lean_object* v_finished_91_; lean_object* v_promise_92_; lean_object* v___x_93_; uint8_t v___y_95_; uint8_t v___x_104_; 
v_finished_91_ = lean_ctor_get(v_w_88_, 0);
v_promise_92_ = lean_ctor_get(v_w_88_, 1);
v___x_93_ = lean_st_ref_take(v_finished_91_);
v___x_104_ = lean_unbox(v___x_93_);
lean_dec(v___x_93_);
if (v___x_104_ == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 1;
v___y_95_ = v___x_105_;
goto v___jp_94_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 0;
v___y_95_ = v___x_106_;
goto v___jp_94_;
}
v___jp_94_:
{
uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = 1;
v___x_97_ = lean_box(v___x_96_);
v___x_98_ = lean_st_ref_put(v_finished_91_, v___x_97_);
if (v___y_95_ == 0)
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_apply_1(v_lose_89_, lean_box(0));
v___x_100_ = lean_unbox(v___x_99_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec_ref(v_lose_89_);
v___x_101_ = lean_box(v_x_87_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
v___x_103_ = lean_io_promise_resolve(v___x_102_, v_promise_92_);
return v___y_95_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0___boxed(lean_object* v_x_107_, lean_object* v_w_108_, lean_object* v_lose_109_, lean_object* v___y_110_){
_start:
{
uint8_t v_x_boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v_x_boxed_111_ = lean_unbox(v_x_107_);
v_res_112_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_boxed_111_, v_w_108_, v_lose_109_);
lean_dec_ref(v_w_108_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(lean_object* v_waiter_114_, uint8_t v_x_115_){
_start:
{
lean_object* v_lose_117_; uint8_t v___x_118_; 
v_lose_117_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_118_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_115_, v_waiter_114_, v_lose_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed(lean_object* v_waiter_119_, lean_object* v_x_120_, lean_object* v_a_121_){
_start:
{
uint8_t v_x_boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_x_boxed_122_ = lean_unbox(v_x_120_);
v_res_123_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_waiter_119_, v_x_boxed_122_);
lean_dec_ref(v_waiter_119_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0(lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_a_138_ = lean_ctor_get(v_x_136_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_146_ == 0)
{
v___x_140_ = v_x_136_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v_x_136_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_145_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_a_147_ = lean_ctor_get(v_x_136_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_155_ == 0)
{
v___x_149_ = v_x_136_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v_x_136_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_154_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0___boxed(lean_object* v_x_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Std_Http_Body_mkStream___lam__0(v_x_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream(){
_start:
{
lean_object* v___f_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___f_164_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__0));
v___x_165_ = 0;
v___x_166_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__1));
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = l_Std_Mutex_new___redArg(v___x_166_);
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
v___x_171_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_167_, v___x_165_, v___x_170_, v___f_164_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___boxed(lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_Http_Body_mkStream();
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object* v_knownSize_174_, lean_object* v_chunk_175_){
_start:
{
if (lean_obj_tag(v_knownSize_174_) == 1)
{
lean_object* v_val_176_; 
v_val_176_ = lean_ctor_get(v_knownSize_174_, 0);
lean_inc(v_val_176_);
if (lean_obj_tag(v_val_176_) == 1)
{
lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_194_; 
v_isSharedCheck_194_ = !lean_is_exclusive(v_knownSize_174_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v_knownSize_174_, 0);
lean_dec(v_unused_195_);
v___x_178_ = v_knownSize_174_;
v_isShared_179_ = v_isSharedCheck_194_;
goto v_resetjp_177_;
}
else
{
lean_dec(v_knownSize_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_194_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_n_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_193_; 
v_n_180_ = lean_ctor_get(v_val_176_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_val_176_);
if (v_isSharedCheck_193_ == 0)
{
v___x_182_ = v_val_176_;
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_n_180_);
lean_dec(v_val_176_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_data_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v_data_184_ = lean_ctor_get(v_chunk_175_, 0);
v___x_185_ = lean_byte_array_size(v_data_184_);
v___x_186_ = lean_nat_sub(v_n_180_, v___x_185_);
lean_dec(v_n_180_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_186_);
v___x_188_ = v___x_182_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_192_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_188_);
v___x_190_ = v___x_178_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
else
{
lean_dec(v_val_176_);
return v_knownSize_174_;
}
}
else
{
return v_knownSize_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object* v_knownSize_196_, lean_object* v_chunk_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_196_, v_chunk_197_);
lean_dec_ref(v_chunk_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object* v_pendingProducer_199_, lean_object* v_pendingConsumer_200_, uint8_t v_closed_201_, lean_object* v_knownSize_202_, lean_object* v_pendingIncompleteChunk_203_, lean_object* v_closeError_204_, lean_object* v_inst_205_, lean_object* v_interestWaiter_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_208_, 0, v_pendingProducer_199_);
lean_ctor_set(v___x_208_, 1, v_pendingConsumer_200_);
lean_ctor_set(v___x_208_, 2, v_interestWaiter_206_);
lean_ctor_set(v___x_208_, 3, v_knownSize_202_);
lean_ctor_set(v___x_208_, 4, v_pendingIncompleteChunk_203_);
lean_ctor_set(v___x_208_, 5, v_closeError_204_);
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*6, v_closed_201_);
lean_inc(v___y_207_);
v___x_209_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_209_, 0, lean_box(0));
lean_closure_set(v___x_209_, 1, lean_box(0));
lean_closure_set(v___x_209_, 2, v___y_207_);
lean_closure_set(v___x_209_, 3, v___x_208_);
v___x_210_ = lean_apply_2(v_inst_205_, lean_box(0), v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object* v_pendingProducer_211_, lean_object* v_pendingConsumer_212_, lean_object* v_closed_213_, lean_object* v_knownSize_214_, lean_object* v_pendingIncompleteChunk_215_, lean_object* v_closeError_216_, lean_object* v_inst_217_, lean_object* v_interestWaiter_218_, lean_object* v___y_219_){
_start:
{
uint8_t v_closed_boxed_220_; lean_object* v_res_221_; 
v_closed_boxed_220_ = lean_unbox(v_closed_213_);
v_res_221_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(v_pendingProducer_211_, v_pendingConsumer_212_, v_closed_boxed_220_, v_knownSize_214_, v_pendingIncompleteChunk_215_, v_closeError_216_, v_inst_217_, v_interestWaiter_218_, v___y_219_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object* v_pendingProducer_251_, uint8_t v_closed_252_, lean_object* v_knownSize_253_, lean_object* v_pendingIncompleteChunk_254_, lean_object* v_closeError_255_, lean_object* v_inst_256_, lean_object* v_interestWaiter_257_, lean_object* v_toApplicative_258_, lean_object* v_toBind_259_, lean_object* v_pendingConsumer_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___f_263_; 
v___x_262_ = lean_box(v_closed_252_);
lean_inc(v_inst_256_);
v___f_263_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed), 9, 7);
lean_closure_set(v___f_263_, 0, v_pendingProducer_251_);
lean_closure_set(v___f_263_, 1, v_pendingConsumer_260_);
lean_closure_set(v___f_263_, 2, v___x_262_);
lean_closure_set(v___f_263_, 3, v_knownSize_253_);
lean_closure_set(v___f_263_, 4, v_pendingIncompleteChunk_254_);
lean_closure_set(v___f_263_, 5, v_closeError_255_);
lean_closure_set(v___f_263_, 6, v_inst_256_);
if (lean_obj_tag(v_interestWaiter_257_) == 0)
{
lean_object* v_toPure_264_; lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v_inst_256_);
v_toPure_264_ = lean_ctor_get(v_toApplicative_258_, 1);
lean_inc(v_toPure_264_);
lean_dec_ref(v_toApplicative_258_);
lean_inc(v___y_261_);
v___f_265_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_265_, 0, v___f_263_);
lean_closure_set(v___f_265_, 1, v___y_261_);
v___x_266_ = lean_apply_2(v_toPure_264_, lean_box(0), v_interestWaiter_257_);
v___x_267_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_266_, v___f_265_);
return v___x_267_;
}
else
{
lean_object* v_val_268_; lean_object* v_finished_269_; lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_val_268_ = lean_ctor_get(v_interestWaiter_257_, 0);
v_finished_269_ = lean_ctor_get(v_val_268_, 0);
lean_inc(v_finished_269_);
lean_inc(v___y_261_);
v___f_270_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_270_, 0, v___f_263_);
lean_closure_set(v___f_270_, 1, v___y_261_);
lean_inc_ref(v___f_270_);
lean_inc(v_toBind_259_);
v___f_271_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_271_, 0, v_toApplicative_258_);
lean_closure_set(v___f_271_, 1, v_interestWaiter_257_);
lean_closure_set(v___f_271_, 2, v_toBind_259_);
lean_closure_set(v___f_271_, 3, v___f_270_);
lean_closure_set(v___f_271_, 4, v___f_270_);
v___x_272_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_272_, 0, lean_box(0));
lean_closure_set(v___x_272_, 1, lean_box(0));
lean_closure_set(v___x_272_, 2, v_finished_269_);
v___x_273_ = lean_apply_2(v_inst_256_, lean_box(0), v___x_272_);
v___x_274_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_273_, v___f_271_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object* v_pendingProducer_275_, lean_object* v_closed_276_, lean_object* v_knownSize_277_, lean_object* v_pendingIncompleteChunk_278_, lean_object* v_closeError_279_, lean_object* v_inst_280_, lean_object* v_interestWaiter_281_, lean_object* v_toApplicative_282_, lean_object* v_toBind_283_, lean_object* v_pendingConsumer_284_, lean_object* v___y_285_){
_start:
{
uint8_t v_closed_boxed_286_; lean_object* v_res_287_; 
v_closed_boxed_286_ = lean_unbox(v_closed_276_);
v_res_287_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(v_pendingProducer_275_, v_closed_boxed_286_, v_knownSize_277_, v_pendingIncompleteChunk_278_, v_closeError_279_, v_inst_280_, v_interestWaiter_281_, v_toApplicative_282_, v_toBind_283_, v_pendingConsumer_284_, v___y_285_);
lean_dec(v___y_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(lean_object* v___f_288_, lean_object* v___y_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_291_; 
lean_inc(v___y_289_);
v___x_291_ = lean_apply_2(v___f_288_, v_a_290_, v___y_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(lean_object* v___f_292_, lean_object* v___y_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(v___f_292_, v___y_293_, v_a_294_);
lean_dec(v___y_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(lean_object* v___f_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___x_299_; 
lean_inc(v_a_297_);
v___x_299_ = lean_apply_2(v___f_296_, v_a_298_, v_a_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(lean_object* v___f_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(v___f_300_, v_a_301_, v_a_302_);
lean_dec(v_a_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(lean_object* v_toApplicative_304_, lean_object* v_pendingConsumer_305_, lean_object* v_toBind_306_, lean_object* v___f_307_, lean_object* v___f_308_, uint8_t v_a_309_){
_start:
{
if (v_a_309_ == 0)
{
lean_object* v_toPure_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v___f_308_);
v_toPure_310_ = lean_ctor_get(v_toApplicative_304_, 1);
lean_inc(v_toPure_310_);
lean_dec_ref(v_toApplicative_304_);
v___x_311_ = lean_apply_2(v_toPure_310_, lean_box(0), v_pendingConsumer_305_);
v___x_312_ = lean_apply_4(v_toBind_306_, lean_box(0), lean_box(0), v___x_311_, v___f_307_);
return v___x_312_;
}
else
{
lean_object* v_toPure_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v___f_307_);
lean_dec(v_pendingConsumer_305_);
v_toPure_313_ = lean_ctor_get(v_toApplicative_304_, 1);
lean_inc(v_toPure_313_);
lean_dec_ref(v_toApplicative_304_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_apply_2(v_toPure_313_, lean_box(0), v___x_314_);
v___x_316_ = lean_apply_4(v_toBind_306_, lean_box(0), lean_box(0), v___x_315_, v___f_308_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(lean_object* v_toApplicative_317_, lean_object* v_pendingConsumer_318_, lean_object* v_toBind_319_, lean_object* v___f_320_, lean_object* v___f_321_, lean_object* v_a_322_){
_start:
{
uint8_t v_a_boxed_323_; lean_object* v_res_324_; 
v_a_boxed_323_ = lean_unbox(v_a_322_);
v_res_324_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(v_toApplicative_317_, v_pendingConsumer_318_, v_toBind_319_, v___f_320_, v___f_321_, v_a_boxed_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(lean_object* v_inst_325_, lean_object* v_toApplicative_326_, lean_object* v_toBind_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_pendingProducer_330_; lean_object* v_pendingConsumer_331_; lean_object* v_interestWaiter_332_; uint8_t v_closed_333_; lean_object* v_knownSize_334_; lean_object* v_pendingIncompleteChunk_335_; lean_object* v_closeError_336_; lean_object* v___x_337_; lean_object* v___f_338_; lean_object* v___y_340_; 
v_pendingProducer_330_ = lean_ctor_get(v_a_329_, 0);
lean_inc(v_pendingProducer_330_);
v_pendingConsumer_331_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_pendingConsumer_331_);
v_interestWaiter_332_ = lean_ctor_get(v_a_329_, 2);
lean_inc(v_interestWaiter_332_);
v_closed_333_ = lean_ctor_get_uint8(v_a_329_, sizeof(void*)*6);
v_knownSize_334_ = lean_ctor_get(v_a_329_, 3);
lean_inc(v_knownSize_334_);
v_pendingIncompleteChunk_335_ = lean_ctor_get(v_a_329_, 4);
lean_inc(v_pendingIncompleteChunk_335_);
v_closeError_336_ = lean_ctor_get(v_a_329_, 5);
lean_inc(v_closeError_336_);
lean_dec_ref(v_a_329_);
v___x_337_ = lean_box(v_closed_333_);
lean_inc(v_toBind_327_);
lean_inc_ref(v_toApplicative_326_);
lean_inc(v_inst_325_);
v___f_338_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_338_, 0, v_pendingProducer_330_);
lean_closure_set(v___f_338_, 1, v___x_337_);
lean_closure_set(v___f_338_, 2, v_knownSize_334_);
lean_closure_set(v___f_338_, 3, v_pendingIncompleteChunk_335_);
lean_closure_set(v___f_338_, 4, v_closeError_336_);
lean_closure_set(v___f_338_, 5, v_inst_325_);
lean_closure_set(v___f_338_, 6, v_interestWaiter_332_);
lean_closure_set(v___f_338_, 7, v_toApplicative_326_);
lean_closure_set(v___f_338_, 8, v_toBind_327_);
if (lean_obj_tag(v_pendingConsumer_331_) == 1)
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v_pendingConsumer_331_, 0);
if (lean_obj_tag(v_val_345_) == 1)
{
lean_object* v_finished_346_; lean_object* v_finished_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_finished_346_ = lean_ctor_get(v_val_345_, 0);
v_finished_347_ = lean_ctor_get(v_finished_346_, 0);
lean_inc(v_finished_347_);
lean_inc(v_a_328_);
v___f_348_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_348_, 0, v___f_338_);
lean_closure_set(v___f_348_, 1, v_a_328_);
lean_inc_ref(v___f_348_);
lean_inc(v_toBind_327_);
v___f_349_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_349_, 0, v_toApplicative_326_);
lean_closure_set(v___f_349_, 1, v_pendingConsumer_331_);
lean_closure_set(v___f_349_, 2, v_toBind_327_);
lean_closure_set(v___f_349_, 3, v___f_348_);
lean_closure_set(v___f_349_, 4, v___f_348_);
v___x_350_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_350_, 0, lean_box(0));
lean_closure_set(v___x_350_, 1, lean_box(0));
lean_closure_set(v___x_350_, 2, v_finished_347_);
v___x_351_ = lean_apply_2(v_inst_325_, lean_box(0), v___x_350_);
v___x_352_ = lean_apply_4(v_toBind_327_, lean_box(0), lean_box(0), v___x_351_, v___f_349_);
return v___x_352_;
}
else
{
lean_dec(v_inst_325_);
v___y_340_ = v_a_328_;
goto v___jp_339_;
}
}
else
{
lean_dec(v_inst_325_);
v___y_340_ = v_a_328_;
goto v___jp_339_;
}
v___jp_339_:
{
lean_object* v_toPure_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_toPure_341_ = lean_ctor_get(v_toApplicative_326_, 1);
lean_inc(v_toPure_341_);
lean_dec_ref(v_toApplicative_326_);
lean_inc(v___y_340_);
v___f_342_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_342_, 0, v___f_338_);
lean_closure_set(v___f_342_, 1, v___y_340_);
v___x_343_ = lean_apply_2(v_toPure_341_, lean_box(0), v_pendingConsumer_331_);
v___x_344_ = lean_apply_4(v_toBind_327_, lean_box(0), lean_box(0), v___x_343_, v___f_342_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(lean_object* v_inst_353_, lean_object* v_toApplicative_354_, lean_object* v_toBind_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(v_inst_353_, v_toApplicative_354_, v_toBind_355_, v_a_356_, v_a_357_);
lean_dec(v_a_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_toApplicative_362_; lean_object* v_toBind_363_; lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_toApplicative_362_ = lean_ctor_get(v_inst_359_, 0);
lean_inc_ref(v_toApplicative_362_);
v_toBind_363_ = lean_ctor_get(v_inst_359_, 1);
lean_inc_n(v_toBind_363_, 2);
lean_dec_ref(v_inst_359_);
lean_inc_n(v_a_361_, 2);
lean_inc(v_inst_360_);
v___f_364_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_364_, 0, v_inst_360_);
lean_closure_set(v___f_364_, 1, v_toApplicative_362_);
lean_closure_set(v___f_364_, 2, v_toBind_363_);
lean_closure_set(v___f_364_, 3, v_a_361_);
v___x_365_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_365_, 0, lean_box(0));
lean_closure_set(v___x_365_, 1, lean_box(0));
lean_closure_set(v___x_365_, 2, v_a_361_);
v___x_366_ = lean_apply_2(v_inst_360_, lean_box(0), v___x_365_);
v___x_367_ = lean_apply_4(v_toBind_363_, lean_box(0), lean_box(0), v___x_366_, v___f_364_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_368_, v_inst_369_, v_a_370_);
lean_dec(v_a_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(lean_object* v_m_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_373_, v_inst_374_, v_a_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(lean_object* v_m_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(v_m_377_, v_inst_378_, v_inst_379_, v_a_380_);
lean_dec(v_a_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object* v_pendingProducer_382_, lean_object* v_pendingConsumer_383_, uint8_t v_closed_384_, lean_object* v_knownSize_385_, lean_object* v_pendingIncompleteChunk_386_, lean_object* v_closeError_387_, lean_object* v_a_388_, lean_object* v_inst_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_392_, 0, v_pendingProducer_382_);
lean_ctor_set(v___x_392_, 1, v_pendingConsumer_383_);
lean_ctor_set(v___x_392_, 2, v___x_391_);
lean_ctor_set(v___x_392_, 3, v_knownSize_385_);
lean_ctor_set(v___x_392_, 4, v_pendingIncompleteChunk_386_);
lean_ctor_set(v___x_392_, 5, v_closeError_387_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*6, v_closed_384_);
lean_inc(v_a_388_);
v___x_393_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_393_, 0, lean_box(0));
lean_closure_set(v___x_393_, 1, lean_box(0));
lean_closure_set(v___x_393_, 2, v_a_388_);
lean_closure_set(v___x_393_, 3, v___x_392_);
v___x_394_ = lean_apply_2(v_inst_389_, lean_box(0), v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object* v_pendingProducer_395_, lean_object* v_pendingConsumer_396_, lean_object* v_closed_397_, lean_object* v_knownSize_398_, lean_object* v_pendingIncompleteChunk_399_, lean_object* v_closeError_400_, lean_object* v_a_401_, lean_object* v_inst_402_, lean_object* v_a_403_){
_start:
{
uint8_t v_closed_boxed_404_; lean_object* v_res_405_; 
v_closed_boxed_404_ = lean_unbox(v_closed_397_);
v_res_405_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(v_pendingProducer_395_, v_pendingConsumer_396_, v_closed_boxed_404_, v_knownSize_398_, v_pendingIncompleteChunk_399_, v_closeError_400_, v_a_401_, v_inst_402_, v_a_403_);
lean_dec(v_a_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(lean_object* v_toApplicative_406_, lean_object* v_a_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_toBind_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_interestWaiter_412_; 
v_interestWaiter_412_ = lean_ctor_get(v_a_411_, 2);
lean_inc(v_interestWaiter_412_);
if (lean_obj_tag(v_interestWaiter_412_) == 1)
{
lean_object* v_toFunctor_413_; lean_object* v_pendingProducer_414_; lean_object* v_pendingConsumer_415_; uint8_t v_closed_416_; lean_object* v_knownSize_417_; lean_object* v_pendingIncompleteChunk_418_; lean_object* v_closeError_419_; lean_object* v_val_420_; lean_object* v_mapConst_421_; lean_object* v___x_422_; lean_object* v___f_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_toFunctor_413_ = lean_ctor_get(v_toApplicative_406_, 0);
lean_inc_ref(v_toFunctor_413_);
lean_dec_ref(v_toApplicative_406_);
v_pendingProducer_414_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_pendingProducer_414_);
v_pendingConsumer_415_ = lean_ctor_get(v_a_411_, 1);
lean_inc(v_pendingConsumer_415_);
v_closed_416_ = lean_ctor_get_uint8(v_a_411_, sizeof(void*)*6);
v_knownSize_417_ = lean_ctor_get(v_a_411_, 3);
lean_inc(v_knownSize_417_);
v_pendingIncompleteChunk_418_ = lean_ctor_get(v_a_411_, 4);
lean_inc(v_pendingIncompleteChunk_418_);
v_closeError_419_ = lean_ctor_get(v_a_411_, 5);
lean_inc(v_closeError_419_);
lean_dec_ref(v_a_411_);
v_val_420_ = lean_ctor_get(v_interestWaiter_412_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_interestWaiter_412_, 1);
v_mapConst_421_ = lean_ctor_get(v_toFunctor_413_, 1);
lean_inc(v_mapConst_421_);
lean_dec_ref(v_toFunctor_413_);
v___x_422_ = lean_box(v_closed_416_);
lean_inc(v_a_407_);
v___f_423_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_423_, 0, v_pendingProducer_414_);
lean_closure_set(v___f_423_, 1, v_pendingConsumer_415_);
lean_closure_set(v___f_423_, 2, v___x_422_);
lean_closure_set(v___f_423_, 3, v_knownSize_417_);
lean_closure_set(v___f_423_, 4, v_pendingIncompleteChunk_418_);
lean_closure_set(v___f_423_, 5, v_closeError_419_);
lean_closure_set(v___f_423_, 6, v_a_407_);
lean_closure_set(v___f_423_, 7, v_inst_408_);
v___x_424_ = 1;
v___x_425_ = lean_box(v___x_424_);
v___x_426_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_426_, 0, v_val_420_);
lean_closure_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_apply_2(v_inst_409_, lean_box(0), v___x_426_);
v___x_428_ = lean_box(0);
v___x_429_ = lean_apply_4(v_mapConst_421_, lean_box(0), lean_box(0), v___x_428_, v___x_427_);
v___x_430_ = lean_apply_4(v_toBind_410_, lean_box(0), lean_box(0), v___x_429_, v___f_423_);
return v___x_430_;
}
else
{
lean_object* v_toPure_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v_interestWaiter_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_toBind_410_);
lean_dec(v_inst_409_);
lean_dec(v_inst_408_);
v_toPure_431_ = lean_ctor_get(v_toApplicative_406_, 1);
lean_inc(v_toPure_431_);
lean_dec_ref(v_toApplicative_406_);
v___x_432_ = lean_box(0);
v___x_433_ = lean_apply_2(v_toPure_431_, lean_box(0), v___x_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(lean_object* v_toApplicative_434_, lean_object* v_a_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_toBind_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(v_toApplicative_434_, v_a_435_, v_inst_436_, v_inst_437_, v_toBind_438_, v_a_439_);
lean_dec(v_a_435_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_toApplicative_445_; lean_object* v_toBind_446_; lean_object* v___f_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_toApplicative_445_ = lean_ctor_get(v_inst_441_, 0);
lean_inc_ref(v_toApplicative_445_);
v_toBind_446_ = lean_ctor_get(v_inst_441_, 1);
lean_inc_n(v_toBind_446_, 2);
lean_dec_ref(v_inst_441_);
lean_inc(v_inst_442_);
lean_inc_n(v_a_444_, 2);
v___f_447_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_447_, 0, v_toApplicative_445_);
lean_closure_set(v___f_447_, 1, v_a_444_);
lean_closure_set(v___f_447_, 2, v_inst_442_);
lean_closure_set(v___f_447_, 3, v_inst_443_);
lean_closure_set(v___f_447_, 4, v_toBind_446_);
v___x_448_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_448_, 0, lean_box(0));
lean_closure_set(v___x_448_, 1, lean_box(0));
lean_closure_set(v___x_448_, 2, v_a_444_);
v___x_449_ = lean_apply_2(v_inst_442_, lean_box(0), v___x_448_);
v___x_450_ = lean_apply_4(v_toBind_446_, lean_box(0), lean_box(0), v___x_449_, v___f_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_451_, v_inst_452_, v_inst_453_, v_a_454_);
lean_dec(v_a_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(lean_object* v_m_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_457_, v_inst_458_, v_inst_459_, v_a_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(lean_object* v_m_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(v_m_462_, v_inst_463_, v_inst_464_, v_inst_465_, v_a_466_);
lean_dec(v_a_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_468_, lean_object* v_a_469_){
_start:
{
uint8_t v___y_471_; lean_object* v_pendingProducer_475_; 
v_pendingProducer_475_ = lean_ctor_get(v_a_469_, 0);
if (lean_obj_tag(v_pendingProducer_475_) == 0)
{
uint8_t v_closed_476_; 
v_closed_476_ = lean_ctor_get_uint8(v_a_469_, sizeof(void*)*6);
v___y_471_ = v_closed_476_;
goto v___jp_470_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = 1;
v___y_471_ = v___x_477_;
goto v___jp_470_;
}
v___jp_470_:
{
lean_object* v_toPure_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_toPure_472_ = lean_ctor_get(v_toApplicative_468_, 1);
lean_inc(v_toPure_472_);
lean_dec_ref(v_toApplicative_468_);
v___x_473_ = lean_box(v___y_471_);
v___x_474_ = lean_apply_2(v_toPure_472_, lean_box(0), v___x_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(v_toApplicative_478_, v_a_479_);
lean_dec_ref(v_a_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_toApplicative_484_; lean_object* v_toBind_485_; lean_object* v___f_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_toApplicative_484_ = lean_ctor_get(v_inst_481_, 0);
lean_inc_ref(v_toApplicative_484_);
v_toBind_485_ = lean_ctor_get(v_inst_481_, 1);
lean_inc(v_toBind_485_);
lean_dec_ref(v_inst_481_);
v___f_486_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_486_, 0, v_toApplicative_484_);
lean_inc(v_a_483_);
v___x_487_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_487_, 0, lean_box(0));
lean_closure_set(v___x_487_, 1, lean_box(0));
lean_closure_set(v___x_487_, 2, v_a_483_);
v___x_488_ = lean_apply_2(v_inst_482_, lean_box(0), v___x_487_);
v___x_489_ = lean_apply_4(v_toBind_485_, lean_box(0), lean_box(0), v___x_488_, v___f_486_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_490_, v_inst_491_, v_a_492_);
lean_dec(v_a_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(lean_object* v_m_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_495_, v_inst_496_, v_a_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(v_m_499_, v_inst_500_, v_inst_501_, v_a_502_);
lean_dec(v_a_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(lean_object* v_toApplicative_504_, lean_object* v_a_505_){
_start:
{
uint8_t v___y_507_; lean_object* v_pendingConsumer_511_; 
v_pendingConsumer_511_ = lean_ctor_get(v_a_505_, 1);
if (lean_obj_tag(v_pendingConsumer_511_) == 0)
{
uint8_t v___x_512_; 
v___x_512_ = 0;
v___y_507_ = v___x_512_;
goto v___jp_506_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = 1;
v___y_507_ = v___x_513_;
goto v___jp_506_;
}
v___jp_506_:
{
lean_object* v_toPure_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_toPure_508_ = lean_ctor_get(v_toApplicative_504_, 1);
lean_inc(v_toPure_508_);
lean_dec_ref(v_toApplicative_504_);
v___x_509_ = lean_box(v___y_507_);
v___x_510_ = lean_apply_2(v_toPure_508_, lean_box(0), v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(v_toApplicative_514_, v_a_515_);
lean_dec_ref(v_a_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_toApplicative_520_; lean_object* v_toBind_521_; lean_object* v___f_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_toApplicative_520_ = lean_ctor_get(v_inst_517_, 0);
lean_inc_ref(v_toApplicative_520_);
v_toBind_521_ = lean_ctor_get(v_inst_517_, 1);
lean_inc(v_toBind_521_);
lean_dec_ref(v_inst_517_);
v___f_522_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_522_, 0, v_toApplicative_520_);
lean_inc(v_a_519_);
v___x_523_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_523_, 0, lean_box(0));
lean_closure_set(v___x_523_, 1, lean_box(0));
lean_closure_set(v___x_523_, 2, v_a_519_);
v___x_524_ = lean_apply_2(v_inst_518_, lean_box(0), v___x_523_);
v___x_525_ = lean_apply_4(v_toBind_521_, lean_box(0), lean_box(0), v___x_524_, v___f_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_526_, v_inst_527_, v_a_528_);
lean_dec(v_a_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(lean_object* v_m_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_531_, v_inst_532_, v_a_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(lean_object* v_m_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(v_m_535_, v_inst_536_, v_inst_537_, v_a_538_);
lean_dec(v_a_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_540_, lean_object* v_chunk_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_toPure_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_toPure_543_ = lean_ctor_get(v_toApplicative_540_, 1);
lean_inc(v_toPure_543_);
lean_dec_ref(v_toApplicative_540_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_chunk_541_);
v___x_545_ = lean_apply_2(v_toPure_543_, lean_box(0), v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_546_, lean_object* v_done_547_, lean_object* v_inst_548_, lean_object* v_toBind_549_, lean_object* v___f_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_toFunctor_552_; lean_object* v_mapConst_553_; uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_toFunctor_552_ = lean_ctor_get(v_toApplicative_546_, 0);
lean_inc_ref(v_toFunctor_552_);
lean_dec_ref(v_toApplicative_546_);
v_mapConst_553_ = lean_ctor_get(v_toFunctor_552_, 1);
lean_inc(v_mapConst_553_);
lean_dec_ref(v_toFunctor_552_);
v___x_554_ = 1;
v___x_555_ = lean_box(v___x_554_);
v___x_556_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_556_, 0, lean_box(0));
lean_closure_set(v___x_556_, 1, v___x_555_);
lean_closure_set(v___x_556_, 2, v_done_547_);
v___x_557_ = lean_apply_2(v_inst_548_, lean_box(0), v___x_556_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_apply_4(v_mapConst_553_, lean_box(0), lean_box(0), v___x_558_, v___x_557_);
v___x_560_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v___x_559_, v___f_550_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_561_, lean_object* v_inst_562_, lean_object* v_toBind_563_, lean_object* v_a_564_, lean_object* v_inst_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_pendingProducer_567_; 
v_pendingProducer_567_ = lean_ctor_get(v_a_566_, 0);
if (lean_obj_tag(v_pendingProducer_567_) == 1)
{
lean_object* v_val_568_; lean_object* v_pendingConsumer_569_; lean_object* v_interestWaiter_570_; uint8_t v_closed_571_; lean_object* v_knownSize_572_; lean_object* v_pendingIncompleteChunk_573_; lean_object* v_closeError_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_590_; 
v_val_568_ = lean_ctor_get(v_pendingProducer_567_, 0);
lean_inc(v_val_568_);
v_pendingConsumer_569_ = lean_ctor_get(v_a_566_, 1);
v_interestWaiter_570_ = lean_ctor_get(v_a_566_, 2);
v_closed_571_ = lean_ctor_get_uint8(v_a_566_, sizeof(void*)*6);
v_knownSize_572_ = lean_ctor_get(v_a_566_, 3);
v_pendingIncompleteChunk_573_ = lean_ctor_get(v_a_566_, 4);
v_closeError_574_ = lean_ctor_get(v_a_566_, 5);
v_isSharedCheck_590_ = !lean_is_exclusive(v_a_566_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_a_566_, 0);
lean_dec(v_unused_591_);
v___x_576_ = v_a_566_;
v_isShared_577_ = v_isSharedCheck_590_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_closeError_574_);
lean_inc(v_pendingIncompleteChunk_573_);
lean_inc(v_knownSize_572_);
lean_inc(v_interestWaiter_570_);
lean_inc(v_pendingConsumer_569_);
lean_dec(v_a_566_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_590_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_chunk_578_; lean_object* v_done_579_; lean_object* v___x_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v_chunk_578_ = lean_ctor_get(v_val_568_, 0);
lean_inc_ref_n(v_chunk_578_, 2);
v_done_579_ = lean_ctor_get(v_val_568_, 1);
lean_inc(v_done_579_);
lean_dec(v_val_568_);
v___x_580_ = lean_box(0);
lean_inc_ref(v_toApplicative_561_);
v___f_581_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_581_, 0, v_toApplicative_561_);
lean_closure_set(v___f_581_, 1, v_chunk_578_);
lean_inc(v_toBind_563_);
v___f_582_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_582_, 0, v_toApplicative_561_);
lean_closure_set(v___f_582_, 1, v_done_579_);
lean_closure_set(v___f_582_, 2, v_inst_562_);
lean_closure_set(v___f_582_, 3, v_toBind_563_);
lean_closure_set(v___f_582_, 4, v___f_581_);
v___x_583_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_572_, v_chunk_578_);
lean_dec_ref(v_chunk_578_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 3, v___x_583_);
lean_ctor_set(v___x_576_, 0, v___x_580_);
v___x_585_ = v___x_576_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_pendingConsumer_569_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_interestWaiter_570_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_pendingIncompleteChunk_573_);
lean_ctor_set(v_reuseFailAlloc_589_, 5, v_closeError_574_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*6, v_closed_571_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_inc(v_a_564_);
v___x_586_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_586_, 0, lean_box(0));
lean_closure_set(v___x_586_, 1, lean_box(0));
lean_closure_set(v___x_586_, 2, v_a_564_);
lean_closure_set(v___x_586_, 3, v___x_585_);
v___x_587_ = lean_apply_2(v_inst_565_, lean_box(0), v___x_586_);
v___x_588_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_587_, v___f_582_);
return v___x_588_;
}
}
}
else
{
lean_object* v_toPure_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec_ref(v_a_566_);
lean_dec(v_inst_565_);
lean_dec(v_toBind_563_);
lean_dec(v_inst_562_);
v_toPure_592_ = lean_ctor_get(v_toApplicative_561_, 1);
lean_inc(v_toPure_592_);
lean_dec_ref(v_toApplicative_561_);
v___x_593_ = lean_box(0);
v___x_594_ = lean_apply_2(v_toPure_592_, lean_box(0), v___x_593_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_toApplicative_595_, lean_object* v_inst_596_, lean_object* v_toBind_597_, lean_object* v_a_598_, lean_object* v_inst_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(v_toApplicative_595_, v_inst_596_, v_toBind_597_, v_a_598_, v_inst_599_, v_a_600_);
lean_dec(v_a_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_toApplicative_606_; lean_object* v_toBind_607_; lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_toApplicative_606_ = lean_ctor_get(v_inst_602_, 0);
lean_inc_ref(v_toApplicative_606_);
v_toBind_607_ = lean_ctor_get(v_inst_602_, 1);
lean_inc_n(v_toBind_607_, 2);
lean_dec_ref(v_inst_602_);
lean_inc(v_inst_603_);
lean_inc_n(v_a_605_, 2);
v___f_608_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_608_, 0, v_toApplicative_606_);
lean_closure_set(v___f_608_, 1, v_inst_604_);
lean_closure_set(v___f_608_, 2, v_toBind_607_);
lean_closure_set(v___f_608_, 3, v_a_605_);
lean_closure_set(v___f_608_, 4, v_inst_603_);
v___x_609_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_609_, 0, lean_box(0));
lean_closure_set(v___x_609_, 1, lean_box(0));
lean_closure_set(v___x_609_, 2, v_a_605_);
v___x_610_ = lean_apply_2(v_inst_603_, lean_box(0), v___x_609_);
v___x_611_ = lean_apply_4(v_toBind_607_, lean_box(0), lean_box(0), v___x_610_, v___f_608_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_612_, v_inst_613_, v_inst_614_, v_a_615_);
lean_dec(v_a_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(lean_object* v_m_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_618_, v_inst_619_, v_inst_620_, v_a_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(lean_object* v_m_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(v_m_623_, v_inst_624_, v_inst_625_, v_inst_626_, v_a_627_);
lean_dec(v_a_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0(lean_object* v_toApplicative_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_closeError_633_; 
v_closeError_633_ = lean_ctor_get(v_a_632_, 5);
lean_inc(v_closeError_633_);
lean_dec_ref(v_a_632_);
if (lean_obj_tag(v_closeError_633_) == 1)
{
lean_object* v_val_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_643_; 
v_val_634_ = lean_ctor_get(v_closeError_633_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_closeError_633_);
if (v_isSharedCheck_643_ == 0)
{
v___x_636_ = v_closeError_633_;
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_val_634_);
lean_dec(v_closeError_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_toPure_638_; lean_object* v___x_640_; 
v_toPure_638_ = lean_ctor_get(v_toApplicative_631_, 1);
lean_inc(v_toPure_638_);
lean_dec_ref(v_toApplicative_631_);
if (v_isShared_637_ == 0)
{
lean_ctor_set_tag(v___x_636_, 0);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_val_634_);
v___x_640_ = v_reuseFailAlloc_642_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; 
v___x_641_ = lean_apply_2(v_toPure_638_, lean_box(0), v___x_640_);
return v___x_641_;
}
}
}
else
{
lean_object* v_toPure_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_closeError_633_);
v_toPure_644_ = lean_ctor_get(v_toApplicative_631_, 1);
lean_inc(v_toPure_644_);
lean_dec_ref(v_toApplicative_631_);
v___x_645_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_646_ = lean_apply_2(v_toPure_644_, lean_box(0), v___x_645_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(lean_object* v_toApplicative_647_, lean_object* v_a_648_, lean_object* v_inst_649_, lean_object* v_toBind_650_, lean_object* v___f_651_, lean_object* v_a_652_){
_start:
{
if (lean_obj_tag(v_a_652_) == 1)
{
lean_object* v_toPure_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v___f_651_);
lean_dec(v_toBind_650_);
lean_dec(v_inst_649_);
v_toPure_653_ = lean_ctor_get(v_toApplicative_647_, 1);
lean_inc(v_toPure_653_);
lean_dec_ref(v_toApplicative_647_);
v___x_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_654_, 0, v_a_652_);
v___x_655_ = lean_apply_2(v_toPure_653_, lean_box(0), v___x_654_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec(v_a_652_);
lean_dec_ref(v_toApplicative_647_);
lean_inc(v_a_648_);
v___x_656_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_656_, 0, lean_box(0));
lean_closure_set(v___x_656_, 1, lean_box(0));
lean_closure_set(v___x_656_, 2, v_a_648_);
v___x_657_ = lean_apply_2(v_inst_649_, lean_box(0), v___x_656_);
v___x_658_ = lean_apply_4(v_toBind_650_, lean_box(0), lean_box(0), v___x_657_, v___f_651_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_659_, lean_object* v_a_660_, lean_object* v_inst_661_, lean_object* v_toBind_662_, lean_object* v___f_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(v_toApplicative_659_, v_a_660_, v_inst_661_, v_toBind_662_, v___f_663_, v_a_664_);
lean_dec(v_a_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_toApplicative_670_; lean_object* v_toBind_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_toApplicative_670_ = lean_ctor_get(v_inst_666_, 0);
v_toBind_671_ = lean_ctor_get(v_inst_666_, 1);
lean_inc_n(v_toBind_671_, 2);
lean_inc_ref_n(v_toApplicative_670_, 2);
v___f_672_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_672_, 0, v_toApplicative_670_);
lean_inc(v_inst_667_);
lean_inc(v_a_669_);
v___f_673_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_673_, 0, v_toApplicative_670_);
lean_closure_set(v___f_673_, 1, v_a_669_);
lean_closure_set(v___f_673_, 2, v_inst_667_);
lean_closure_set(v___f_673_, 3, v_toBind_671_);
lean_closure_set(v___f_673_, 4, v___f_672_);
v___x_674_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_666_, v_inst_667_, v_inst_668_, v_a_669_);
v___x_675_ = lean_apply_4(v_toBind_671_, lean_box(0), lean_box(0), v___x_674_, v___f_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___boxed(lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_676_, v_inst_677_, v_inst_678_, v_a_679_);
lean_dec(v_a_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(lean_object* v_m_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_682_, v_inst_683_, v_inst_684_, v_a_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___boxed(lean_object* v_m_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(v_m_687_, v_inst_688_, v_inst_689_, v_inst_690_, v_a_691_);
lean_dec(v_a_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(uint8_t v___x_693_, lean_object* v_knownSize_694_, lean_object* v_closeError_695_, lean_object* v_inst_696_, lean_object* v_____r_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
lean_ctor_set(v___x_700_, 2, v___x_699_);
lean_ctor_set(v___x_700_, 3, v_knownSize_694_);
lean_ctor_set(v___x_700_, 4, v___x_699_);
lean_ctor_set(v___x_700_, 5, v_closeError_695_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*6, v___x_693_);
lean_inc(v___y_698_);
v___x_701_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_701_, 0, lean_box(0));
lean_closure_set(v___x_701_, 1, lean_box(0));
lean_closure_set(v___x_701_, 2, v___y_698_);
lean_closure_set(v___x_701_, 3, v___x_700_);
v___x_702_ = lean_apply_2(v_inst_696_, lean_box(0), v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed(lean_object* v___x_703_, lean_object* v_knownSize_704_, lean_object* v_closeError_705_, lean_object* v_inst_706_, lean_object* v_____r_707_, lean_object* v___y_708_){
_start:
{
uint8_t v___x_635__boxed_709_; lean_object* v_res_710_; 
v___x_635__boxed_709_ = lean_unbox(v___x_703_);
v_res_710_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(v___x_635__boxed_709_, v_knownSize_704_, v_closeError_705_, v_inst_706_, v_____r_707_, v___y_708_);
lean_dec(v___y_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(lean_object* v___f_711_, lean_object* v___y_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_714_; 
lean_inc(v___y_712_);
v___x_714_ = lean_apply_2(v___f_711_, v_a_713_, v___y_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object* v___f_715_, lean_object* v___y_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(v___f_715_, v___y_716_, v_a_717_);
lean_dec(v___y_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object* v_pendingProducer_719_, lean_object* v_toApplicative_720_, lean_object* v___f_721_, uint8_t v_closed_722_, lean_object* v_inst_723_, lean_object* v_toBind_724_, lean_object* v_____r_725_, lean_object* v___y_726_){
_start:
{
if (lean_obj_tag(v_pendingProducer_719_) == 1)
{
lean_object* v_val_727_; lean_object* v_toFunctor_728_; lean_object* v_done_729_; lean_object* v_mapConst_730_; lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_val_727_ = lean_ctor_get(v_pendingProducer_719_, 0);
lean_inc(v_val_727_);
lean_dec_ref_known(v_pendingProducer_719_, 1);
v_toFunctor_728_ = lean_ctor_get(v_toApplicative_720_, 0);
lean_inc_ref(v_toFunctor_728_);
lean_dec_ref(v_toApplicative_720_);
v_done_729_ = lean_ctor_get(v_val_727_, 1);
lean_inc(v_done_729_);
lean_dec(v_val_727_);
v_mapConst_730_ = lean_ctor_get(v_toFunctor_728_, 1);
lean_inc(v_mapConst_730_);
lean_dec_ref(v_toFunctor_728_);
lean_inc(v___y_726_);
v___f_731_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_731_, 0, v___f_721_);
lean_closure_set(v___f_731_, 1, v___y_726_);
v___x_732_ = lean_box(v_closed_722_);
v___x_733_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_733_, 0, lean_box(0));
lean_closure_set(v___x_733_, 1, v___x_732_);
lean_closure_set(v___x_733_, 2, v_done_729_);
v___x_734_ = lean_apply_2(v_inst_723_, lean_box(0), v___x_733_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_apply_4(v_mapConst_730_, lean_box(0), lean_box(0), v___x_735_, v___x_734_);
v___x_737_ = lean_apply_4(v_toBind_724_, lean_box(0), lean_box(0), v___x_736_, v___f_731_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_toBind_724_);
lean_dec(v_inst_723_);
lean_dec_ref(v_toApplicative_720_);
lean_dec(v_pendingProducer_719_);
v___x_738_ = lean_box(0);
lean_inc(v___y_726_);
v___x_739_ = lean_apply_2(v___f_721_, v___x_738_, v___y_726_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed(lean_object* v_pendingProducer_740_, lean_object* v_toApplicative_741_, lean_object* v___f_742_, lean_object* v_closed_743_, lean_object* v_inst_744_, lean_object* v_toBind_745_, lean_object* v_____r_746_, lean_object* v___y_747_){
_start:
{
uint8_t v_closed_boxed_748_; lean_object* v_res_749_; 
v_closed_boxed_748_ = lean_unbox(v_closed_743_);
v_res_749_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(v_pendingProducer_740_, v_toApplicative_741_, v___f_742_, v_closed_boxed_748_, v_inst_744_, v_toBind_745_, v_____r_746_, v___y_747_);
lean_dec(v___y_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object* v_interestWaiter_750_, lean_object* v_toApplicative_751_, lean_object* v___f_752_, uint8_t v_closed_753_, lean_object* v_inst_754_, lean_object* v_toBind_755_, lean_object* v_____r_756_, lean_object* v___y_757_){
_start:
{
if (lean_obj_tag(v_interestWaiter_750_) == 1)
{
lean_object* v_toFunctor_758_; lean_object* v_val_759_; lean_object* v_mapConst_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_toFunctor_758_ = lean_ctor_get(v_toApplicative_751_, 0);
lean_inc_ref(v_toFunctor_758_);
lean_dec_ref(v_toApplicative_751_);
v_val_759_ = lean_ctor_get(v_interestWaiter_750_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v_interestWaiter_750_, 1);
v_mapConst_760_ = lean_ctor_get(v_toFunctor_758_, 1);
lean_inc(v_mapConst_760_);
lean_dec_ref(v_toFunctor_758_);
lean_inc(v___y_757_);
v___f_761_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_761_, 0, v___f_752_);
lean_closure_set(v___f_761_, 1, v___y_757_);
v___x_762_ = lean_box(v_closed_753_);
v___x_763_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_763_, 0, v_val_759_);
lean_closure_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_apply_2(v_inst_754_, lean_box(0), v___x_763_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_apply_4(v_mapConst_760_, lean_box(0), lean_box(0), v___x_765_, v___x_764_);
v___x_767_ = lean_apply_4(v_toBind_755_, lean_box(0), lean_box(0), v___x_766_, v___f_761_);
return v___x_767_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v_toBind_755_);
lean_dec(v_inst_754_);
lean_dec_ref(v_toApplicative_751_);
lean_dec(v_interestWaiter_750_);
v___x_768_ = lean_box(0);
lean_inc(v___y_757_);
v___x_769_ = lean_apply_2(v___f_752_, v___x_768_, v___y_757_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object* v_interestWaiter_770_, lean_object* v_toApplicative_771_, lean_object* v___f_772_, lean_object* v_closed_773_, lean_object* v_inst_774_, lean_object* v_toBind_775_, lean_object* v_____r_776_, lean_object* v___y_777_){
_start:
{
uint8_t v_closed_boxed_778_; lean_object* v_res_779_; 
v_closed_boxed_778_ = lean_unbox(v_closed_773_);
v_res_779_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_770_, v_toApplicative_771_, v___f_772_, v_closed_boxed_778_, v_inst_774_, v_toBind_775_, v_____r_776_, v___y_777_);
lean_dec(v___y_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(lean_object* v___f_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_783_; 
lean_inc(v_a_781_);
v___x_783_ = lean_apply_2(v___f_780_, v_a_782_, v_a_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object* v___f_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(v___f_784_, v_a_785_, v_a_786_);
lean_dec(v_a_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object* v_inst_788_, lean_object* v_toApplicative_789_, lean_object* v_inst_790_, lean_object* v_toBind_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
uint8_t v_closed_794_; 
v_closed_794_ = lean_ctor_get_uint8(v_a_793_, sizeof(void*)*6);
if (v_closed_794_ == 0)
{
lean_object* v_pendingProducer_795_; lean_object* v_pendingConsumer_796_; lean_object* v_interestWaiter_797_; lean_object* v_knownSize_798_; lean_object* v_closeError_799_; uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___f_806_; 
v_pendingProducer_795_ = lean_ctor_get(v_a_793_, 0);
lean_inc(v_pendingProducer_795_);
v_pendingConsumer_796_ = lean_ctor_get(v_a_793_, 1);
lean_inc(v_pendingConsumer_796_);
v_interestWaiter_797_ = lean_ctor_get(v_a_793_, 2);
lean_inc_n(v_interestWaiter_797_, 2);
v_knownSize_798_ = lean_ctor_get(v_a_793_, 3);
lean_inc(v_knownSize_798_);
v_closeError_799_ = lean_ctor_get(v_a_793_, 5);
lean_inc_n(v_closeError_799_, 2);
lean_dec_ref(v_a_793_);
v___x_800_ = 1;
v___x_801_ = lean_box(v___x_800_);
v___f_802_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_802_, 0, v___x_801_);
lean_closure_set(v___f_802_, 1, v_knownSize_798_);
lean_closure_set(v___f_802_, 2, v_closeError_799_);
lean_closure_set(v___f_802_, 3, v_inst_788_);
v___x_803_ = lean_box(v_closed_794_);
lean_inc_n(v_toBind_791_, 2);
lean_inc_n(v_inst_790_, 2);
lean_inc_ref_n(v_toApplicative_789_, 2);
v___f_804_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_804_, 0, v_pendingProducer_795_);
lean_closure_set(v___f_804_, 1, v_toApplicative_789_);
lean_closure_set(v___f_804_, 2, v___f_802_);
lean_closure_set(v___f_804_, 3, v___x_803_);
lean_closure_set(v___f_804_, 4, v_inst_790_);
lean_closure_set(v___f_804_, 5, v_toBind_791_);
v___x_805_ = lean_box(v_closed_794_);
lean_inc_ref(v___f_804_);
v___f_806_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_806_, 0, v_interestWaiter_797_);
lean_closure_set(v___f_806_, 1, v_toApplicative_789_);
lean_closure_set(v___f_806_, 2, v___f_804_);
lean_closure_set(v___f_806_, 3, v___x_805_);
lean_closure_set(v___f_806_, 4, v_inst_790_);
lean_closure_set(v___f_806_, 5, v_toBind_791_);
if (lean_obj_tag(v_pendingConsumer_796_) == 1)
{
lean_object* v_val_807_; lean_object* v___f_808_; lean_object* v___y_810_; 
lean_dec_ref(v___f_804_);
lean_dec(v_interestWaiter_797_);
v_val_807_ = lean_ctor_get(v_pendingConsumer_796_, 0);
lean_inc(v_val_807_);
lean_dec_ref_known(v_pendingConsumer_796_, 1);
lean_inc(v_a_792_);
v___f_808_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_808_, 0, v___f_806_);
lean_closure_set(v___f_808_, 1, v_a_792_);
if (lean_obj_tag(v_closeError_799_) == 0)
{
lean_object* v___x_818_; 
v___x_818_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___y_810_ = v___x_818_;
goto v___jp_809_;
}
else
{
lean_object* v_val_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v_val_819_ = lean_ctor_get(v_closeError_799_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_closeError_799_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v_closeError_799_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_val_819_);
lean_dec(v_closeError_799_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_val_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
v___y_810_ = v___x_824_;
goto v___jp_809_;
}
}
}
v___jp_809_:
{
lean_object* v_toFunctor_811_; lean_object* v_mapConst_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_toFunctor_811_ = lean_ctor_get(v_toApplicative_789_, 0);
lean_inc_ref(v_toFunctor_811_);
lean_dec_ref(v_toApplicative_789_);
v_mapConst_812_ = lean_ctor_get(v_toFunctor_811_, 1);
lean_inc(v_mapConst_812_);
lean_dec_ref(v_toFunctor_811_);
v___x_813_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed), 3, 2);
lean_closure_set(v___x_813_, 0, v_val_807_);
lean_closure_set(v___x_813_, 1, v___y_810_);
v___x_814_ = lean_apply_2(v_inst_790_, lean_box(0), v___x_813_);
v___x_815_ = lean_box(0);
v___x_816_ = lean_apply_4(v_mapConst_812_, lean_box(0), lean_box(0), v___x_815_, v___x_814_);
v___x_817_ = lean_apply_4(v_toBind_791_, lean_box(0), lean_box(0), v___x_816_, v___f_808_);
return v___x_817_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec_ref(v___f_806_);
lean_dec(v_closeError_799_);
lean_dec(v_pendingConsumer_796_);
v___x_827_ = lean_box(0);
v___x_828_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_797_, v_toApplicative_789_, v___f_804_, v_closed_794_, v_inst_790_, v_toBind_791_, v___x_827_, v_a_792_);
return v___x_828_;
}
}
else
{
lean_object* v_toPure_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v_a_793_);
lean_dec(v_toBind_791_);
lean_dec(v_inst_790_);
lean_dec(v_inst_788_);
v_toPure_829_ = lean_ctor_get(v_toApplicative_789_, 1);
lean_inc(v_toPure_829_);
lean_dec_ref(v_toApplicative_789_);
v___x_830_ = lean_box(0);
v___x_831_ = lean_apply_2(v_toPure_829_, lean_box(0), v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object* v_inst_832_, lean_object* v_toApplicative_833_, lean_object* v_inst_834_, lean_object* v_toBind_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(v_inst_832_, v_toApplicative_833_, v_inst_834_, v_toBind_835_, v_a_836_, v_a_837_);
lean_dec(v_a_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_toApplicative_843_; lean_object* v_toBind_844_; lean_object* v___f_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_toApplicative_843_ = lean_ctor_get(v_inst_839_, 0);
lean_inc_ref(v_toApplicative_843_);
v_toBind_844_ = lean_ctor_get(v_inst_839_, 1);
lean_inc_n(v_toBind_844_, 2);
lean_dec_ref(v_inst_839_);
lean_inc_n(v_a_842_, 2);
lean_inc(v_inst_840_);
v___f_845_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_845_, 0, v_inst_840_);
lean_closure_set(v___f_845_, 1, v_toApplicative_843_);
lean_closure_set(v___f_845_, 2, v_inst_841_);
lean_closure_set(v___f_845_, 3, v_toBind_844_);
lean_closure_set(v___f_845_, 4, v_a_842_);
v___x_846_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_846_, 0, lean_box(0));
lean_closure_set(v___x_846_, 1, lean_box(0));
lean_closure_set(v___x_846_, 2, v_a_842_);
v___x_847_ = lean_apply_2(v_inst_840_, lean_box(0), v___x_846_);
v___x_848_ = lean_apply_4(v_toBind_844_, lean_box(0), lean_box(0), v___x_847_, v___f_845_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_849_, v_inst_850_, v_inst_851_, v_a_852_);
lean_dec(v_a_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object* v_m_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_855_, v_inst_856_, v_inst_857_, v_a_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object* v_m_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(v_m_860_, v_inst_861_, v_inst_862_, v_inst_863_, v_a_864_);
lean_dec(v_a_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object* v_pendingProducer_870_, lean_object* v_pendingConsumer_871_, uint8_t v_closed_872_, lean_object* v_knownSize_873_, lean_object* v_pendingIncompleteChunk_874_, lean_object* v_closeError_875_, lean_object* v_interestWaiter_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_879_, 0, v_pendingProducer_870_);
lean_ctor_set(v___x_879_, 1, v_pendingConsumer_871_);
lean_ctor_set(v___x_879_, 2, v_interestWaiter_876_);
lean_ctor_set(v___x_879_, 3, v_knownSize_873_);
lean_ctor_set(v___x_879_, 4, v_pendingIncompleteChunk_874_);
lean_ctor_set(v___x_879_, 5, v_closeError_875_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*6, v_closed_872_);
v___x_880_ = lean_st_ref_swap(v___y_877_, v___x_879_);
lean_dec(v___x_880_);
v___x_881_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object* v_pendingProducer_882_, lean_object* v_pendingConsumer_883_, lean_object* v_closed_884_, lean_object* v_knownSize_885_, lean_object* v_pendingIncompleteChunk_886_, lean_object* v_closeError_887_, lean_object* v_interestWaiter_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v_closed_boxed_891_; lean_object* v_res_892_; 
v_closed_boxed_891_ = lean_unbox(v_closed_884_);
v_res_892_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_882_, v_pendingConsumer_883_, v_closed_boxed_891_, v_knownSize_885_, v_pendingIncompleteChunk_886_, v_closeError_887_, v_interestWaiter_888_, v___y_889_);
lean_dec(v___y_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object* v___f_893_, lean_object* v___y_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_895_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref(v___f_893_);
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
lean_object* v_a_906_; lean_object* v___x_907_; 
v_a_906_ = lean_ctor_get(v_x_895_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v_x_895_, 1);
lean_inc(v___y_894_);
v___x_907_ = lean_apply_3(v___f_893_, v_a_906_, v___y_894_, lean_box(0));
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object* v___f_908_, lean_object* v___y_909_, lean_object* v_x_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_908_, v___y_909_, v_x_910_);
lean_dec(v___y_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object* v_interestWaiter_917_, lean_object* v___f_918_, lean_object* v___f_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v___f_919_);
lean_dec_ref(v___f_918_);
lean_dec(v_interestWaiter_917_);
v_a_922_ = lean_ctor_get(v_x_920_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_920_);
if (v_isSharedCheck_930_ == 0)
{
v___x_924_ = v_x_920_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v_x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_929_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; 
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_947_; 
v_a_931_ = lean_ctor_get(v_x_920_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_920_);
if (v_isSharedCheck_947_ == 0)
{
v___x_933_ = v_x_920_;
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v_x_920_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
uint8_t v___x_935_; 
v___x_935_ = lean_unbox(v_a_931_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec_ref(v___f_919_);
v___x_936_ = lean_unsigned_to_nat(0u);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_interestWaiter_917_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_interestWaiter_917_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v___x_940_ = lean_unbox(v_a_931_);
lean_dec(v_a_931_);
v___x_941_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_936_, v___x_940_, v___x_939_, v___f_918_);
return v___x_941_;
}
}
else
{
lean_object* v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_del_object(v___x_933_);
lean_dec(v_a_931_);
lean_dec_ref(v___f_918_);
lean_dec(v_interestWaiter_917_);
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = 0;
v___x_945_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1));
v___x_946_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_943_, v___x_944_, v___x_945_, v___f_919_);
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object* v_interestWaiter_948_, lean_object* v___f_949_, lean_object* v___f_950_, lean_object* v_x_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_948_, v___f_949_, v___f_950_, v_x_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object* v_pendingProducer_954_, uint8_t v_closed_955_, lean_object* v_knownSize_956_, lean_object* v_pendingIncompleteChunk_957_, lean_object* v_closeError_958_, lean_object* v_interestWaiter_959_, lean_object* v_pendingConsumer_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; lean_object* v___f_964_; 
v___x_963_ = lean_box(v_closed_955_);
v___f_964_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed), 9, 6);
lean_closure_set(v___f_964_, 0, v_pendingProducer_954_);
lean_closure_set(v___f_964_, 1, v_pendingConsumer_960_);
lean_closure_set(v___f_964_, 2, v___x_963_);
lean_closure_set(v___f_964_, 3, v_knownSize_956_);
lean_closure_set(v___f_964_, 4, v_pendingIncompleteChunk_957_);
lean_closure_set(v___f_964_, 5, v_closeError_958_);
if (lean_obj_tag(v_interestWaiter_959_) == 0)
{
lean_object* v___f_965_; lean_object* v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_inc(v___y_961_);
v___f_965_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_965_, 0, v___f_964_);
lean_closure_set(v___f_965_, 1, v___y_961_);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = 0;
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v_interestWaiter_959_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_966_, v___x_967_, v___x_969_, v___f_965_);
return v___x_970_;
}
else
{
lean_object* v_val_971_; lean_object* v_finished_972_; lean_object* v___f_973_; lean_object* v___f_974_; lean_object* v___x_975_; uint8_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_val_971_ = lean_ctor_get(v_interestWaiter_959_, 0);
v_finished_972_ = lean_ctor_get(v_val_971_, 0);
lean_inc(v_finished_972_);
lean_inc(v___y_961_);
v___f_973_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_973_, 0, v___f_964_);
lean_closure_set(v___f_973_, 1, v___y_961_);
lean_inc_ref(v___f_973_);
v___f_974_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed), 5, 3);
lean_closure_set(v___f_974_, 0, v_interestWaiter_959_);
lean_closure_set(v___f_974_, 1, v___f_973_);
lean_closure_set(v___f_974_, 2, v___f_973_);
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = 0;
v___x_977_ = lean_st_ref_get(v_finished_972_);
lean_dec(v_finished_972_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
v___x_980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_975_, v___x_976_, v___x_979_, v___f_974_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object* v_pendingProducer_981_, lean_object* v_closed_982_, lean_object* v_knownSize_983_, lean_object* v_pendingIncompleteChunk_984_, lean_object* v_closeError_985_, lean_object* v_interestWaiter_986_, lean_object* v_pendingConsumer_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
uint8_t v_closed_boxed_990_; lean_object* v_res_991_; 
v_closed_boxed_990_ = lean_unbox(v_closed_982_);
v_res_991_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_981_, v_closed_boxed_990_, v_knownSize_983_, v_pendingIncompleteChunk_984_, v_closeError_985_, v_interestWaiter_986_, v_pendingConsumer_987_, v___y_988_);
lean_dec(v___y_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object* v___f_992_, lean_object* v___y_993_, lean_object* v_x_994_){
_start:
{
if (lean_obj_tag(v_x_994_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref(v___f_992_);
v_a_996_ = lean_ctor_get(v_x_994_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_x_994_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_998_ = v_x_994_;
v_isShared_999_ = v_isSharedCheck_1004_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v_x_994_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1004_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1006_; 
v_a_1005_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v_x_994_, 1);
lean_inc(v___y_993_);
v___x_1006_ = lean_apply_3(v___f_992_, v_a_1005_, v___y_993_, lean_box(0));
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object* v___f_1007_, lean_object* v___y_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_1007_, v___y_1008_, v_x_1009_);
lean_dec(v___y_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object* v___f_1012_, lean_object* v_a_1013_, lean_object* v_x_1014_){
_start:
{
if (lean_obj_tag(v_x_1014_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v___f_1012_);
v_a_1016_ = lean_ctor_get(v_x_1014_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_x_1014_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1018_ = v_x_1014_;
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v_x_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
v_a_1025_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v_x_1014_, 1);
lean_inc(v_a_1013_);
v___x_1026_ = lean_apply_3(v___f_1012_, v_a_1025_, v_a_1013_, lean_box(0));
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object* v___f_1027_, lean_object* v_a_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_1027_, v_a_1028_, v_x_1029_);
lean_dec(v_a_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object* v_pendingConsumer_1036_, lean_object* v___f_1037_, lean_object* v___f_1038_, lean_object* v_x_1039_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v___f_1038_);
lean_dec_ref(v___f_1037_);
lean_dec(v_pendingConsumer_1036_);
v_a_1041_ = lean_ctor_get(v_x_1039_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_x_1039_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1043_ = v_x_1039_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v_x_1039_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1066_; 
v_a_1050_ = lean_ctor_get(v_x_1039_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1039_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1052_ = v_x_1039_;
v_isShared_1053_ = v_isSharedCheck_1066_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v_x_1039_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1066_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
uint8_t v___x_1054_; 
v___x_1054_ = lean_unbox(v_a_1050_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_dec_ref(v___f_1038_);
v___x_1055_ = lean_unsigned_to_nat(0u);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_pendingConsumer_1036_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_pendingConsumer_1036_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
v___x_1059_ = lean_unbox(v_a_1050_);
lean_dec(v_a_1050_);
v___x_1060_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1055_, v___x_1059_, v___x_1058_, v___f_1037_);
return v___x_1060_;
}
}
else
{
lean_object* v___x_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_del_object(v___x_1052_);
lean_dec(v_a_1050_);
lean_dec_ref(v___f_1037_);
lean_dec(v_pendingConsumer_1036_);
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = 0;
v___x_1064_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1));
v___x_1065_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1062_, v___x_1063_, v___x_1064_, v___f_1038_);
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object* v_pendingConsumer_1067_, lean_object* v___f_1068_, lean_object* v___f_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_1067_, v___f_1068_, v___f_1069_, v_x_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object* v_a_1073_, lean_object* v_x_1074_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_a_1076_ = lean_ctor_get(v_x_1074_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_x_1074_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1078_ = v_x_1074_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v_x_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1125_; 
v_a_1085_ = lean_ctor_get(v_x_1074_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1074_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1087_ = v_x_1074_;
v_isShared_1088_ = v_isSharedCheck_1125_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v_x_1074_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1125_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_pendingProducer_1089_; lean_object* v_pendingConsumer_1090_; lean_object* v_interestWaiter_1091_; uint8_t v_closed_1092_; lean_object* v_knownSize_1093_; lean_object* v_pendingIncompleteChunk_1094_; lean_object* v_closeError_1095_; lean_object* v___x_1096_; lean_object* v___f_1097_; lean_object* v___y_1099_; 
v_pendingProducer_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_pendingProducer_1089_);
v_pendingConsumer_1090_ = lean_ctor_get(v_a_1085_, 1);
lean_inc(v_pendingConsumer_1090_);
v_interestWaiter_1091_ = lean_ctor_get(v_a_1085_, 2);
lean_inc(v_interestWaiter_1091_);
v_closed_1092_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*6);
v_knownSize_1093_ = lean_ctor_get(v_a_1085_, 3);
lean_inc(v_knownSize_1093_);
v_pendingIncompleteChunk_1094_ = lean_ctor_get(v_a_1085_, 4);
lean_inc(v_pendingIncompleteChunk_1094_);
v_closeError_1095_ = lean_ctor_get(v_a_1085_, 5);
lean_inc(v_closeError_1095_);
lean_dec(v_a_1085_);
v___x_1096_ = lean_box(v_closed_1092_);
v___f_1097_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed), 9, 6);
lean_closure_set(v___f_1097_, 0, v_pendingProducer_1089_);
lean_closure_set(v___f_1097_, 1, v___x_1096_);
lean_closure_set(v___f_1097_, 2, v_knownSize_1093_);
lean_closure_set(v___f_1097_, 3, v_pendingIncompleteChunk_1094_);
lean_closure_set(v___f_1097_, 4, v_closeError_1095_);
lean_closure_set(v___f_1097_, 5, v_interestWaiter_1091_);
if (lean_obj_tag(v_pendingConsumer_1090_) == 1)
{
lean_object* v_val_1108_; 
v_val_1108_ = lean_ctor_get(v_pendingConsumer_1090_, 0);
lean_inc(v_val_1108_);
if (lean_obj_tag(v_val_1108_) == 1)
{
lean_object* v_finished_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1087_);
v_finished_1109_ = lean_ctor_get(v_val_1108_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_val_1108_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1111_ = v_val_1108_;
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_finished_1109_);
lean_dec(v_val_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v_finished_1113_; lean_object* v___f_1114_; lean_object* v___f_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_finished_1113_ = lean_ctor_get(v_finished_1109_, 0);
lean_inc(v_finished_1113_);
lean_dec_ref(v_finished_1109_);
lean_inc(v_a_1073_);
v___f_1114_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1114_, 0, v___f_1097_);
lean_closure_set(v___f_1114_, 1, v_a_1073_);
lean_inc_ref(v___f_1114_);
v___f_1115_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1115_, 0, v_pendingConsumer_1090_);
lean_closure_set(v___f_1115_, 1, v___f_1114_);
lean_closure_set(v___f_1115_, 2, v___f_1114_);
v___x_1116_ = lean_unsigned_to_nat(0u);
v___x_1117_ = 0;
v___x_1118_ = lean_st_ref_get(v_finished_1113_);
lean_dec(v_finished_1113_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1118_);
v___x_1120_ = v___x_1111_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
v___x_1122_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1116_, v___x_1117_, v___x_1121_, v___f_1115_);
return v___x_1122_;
}
}
}
else
{
lean_dec(v_val_1108_);
v___y_1099_ = v_a_1073_;
goto v___jp_1098_;
}
}
else
{
v___y_1099_ = v_a_1073_;
goto v___jp_1098_;
}
v___jp_1098_:
{
lean_object* v___f_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1104_; 
lean_inc(v___y_1099_);
v___f_1100_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1100_, 0, v___f_1097_);
lean_closure_set(v___f_1100_, 1, v___y_1099_);
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = 0;
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_pendingConsumer_1090_);
v___x_1104_ = v___x_1087_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_pendingConsumer_1090_);
v___x_1104_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___x_1106_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1101_, v___x_1102_, v___x_1105_, v___f_1100_);
return v___x_1106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object* v_a_1126_, lean_object* v_x_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_1126_, v_x_1127_);
lean_dec(v_a_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object* v_a_1130_){
_start:
{
lean_object* v___f_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_inc(v_a_1130_);
v___f_1132_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1132_, 0, v_a_1130_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = 0;
v___x_1135_ = lean_st_ref_get(v_a_1130_);
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
v___x_1138_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1133_, v___x_1134_, v___x_1137_, v___f_1132_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object* v_a_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_1139_);
lean_dec(v_a_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object* v___y_1142_){
_start:
{
if (lean_obj_tag(v___y_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_a_1143_ = lean_ctor_get(v___y_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___y_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___y_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___y_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
v_a_1151_ = lean_ctor_get(v___y_1142_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___y_1142_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1153_ = v___y_1142_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___y_1142_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_fst_1155_; lean_object* v___x_1157_; 
v_fst_1155_ = lean_ctor_get(v_a_1151_, 0);
lean_inc(v_fst_1155_);
lean_dec(v_a_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_fst_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_fst_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object* v_mutex_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_io_basemutex_unlock(v_mutex_1160_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_1166_, lean_object* v_x_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(v_mutex_1166_, v_x_1167_);
lean_dec(v_x_1167_);
lean_dec(v_mutex_1166_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object* v_k_1170_, lean_object* v_ref_1171_, lean_object* v_x_1172_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_ref_1171_);
lean_dec_ref(v_k_1170_);
v_a_1174_ = lean_ctor_get(v_x_1172_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_x_1172_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1176_ = v_x_1172_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v_x_1172_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
else
{
lean_object* v___x_1183_; 
lean_dec_ref_known(v_x_1172_, 1);
v___x_1183_ = lean_apply_2(v_k_1170_, v_ref_1171_, lean_box(0));
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object* v_k_1184_, lean_object* v_ref_1185_, lean_object* v_x_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(v_k_1184_, v_ref_1185_, v_x_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object* v_mutex_1189_, lean_object* v___f_1190_){
_start:
{
lean_object* v___x_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = 0;
v___x_1194_ = lean_io_basemutex_lock(v_mutex_1189_);
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
v___x_1197_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1192_, v___x_1193_, v___x_1196_, v___f_1190_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_1198_, lean_object* v___f_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(v_mutex_1198_, v___f_1199_);
lean_dec(v_mutex_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(lean_object* v_mutex_1203_, lean_object* v_k_1204_){
_start:
{
lean_object* v_ref_1206_; lean_object* v_mutex_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___y_1216_; 
v_ref_1206_ = lean_ctor_get(v_mutex_1203_, 0);
lean_inc(v_ref_1206_);
v_mutex_1207_ = lean_ctor_get(v_mutex_1203_, 1);
lean_inc_n(v_mutex_1207_, 2);
lean_dec_ref(v_mutex_1203_);
v___f_1208_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0));
v___f_1209_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1209_, 0, v_mutex_1207_);
v___f_1210_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1210_, 0, v_k_1204_);
lean_closure_set(v___f_1210_, 1, v_ref_1206_);
v___f_1211_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1211_, 0, v_mutex_1207_);
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
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1244_; 
v_a_1236_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1238_ = v___x_1214_;
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1214_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = lean_task_map(v___f_1208_, v_a_1236_, v___x_1212_, v___x_1213_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___boxed(lean_object* v_mutex_1245_, lean_object* v_k_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1245_, v_k_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_mutex_1251_, lean_object* v_k_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1251_, v_k_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed(lean_object* v_00_u03b1_1255_, lean_object* v_00_u03b2_1256_, lean_object* v_mutex_1257_, lean_object* v_k_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(v_00_u03b1_1255_, v_00_u03b2_1256_, v_mutex_1257_, v_k_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0(lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_a_1263_ = lean_ctor_get(v_x_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v_x_1261_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v_x_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1273_; 
v_a_1272_ = lean_ctor_get(v_x_1261_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v_x_1261_, 1);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v_a_1272_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(lean_object* v_x_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_Http_Body_Stream_tryRecv___lam__0(v_x_1274_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object* v_a_1277_, lean_object* v___f_1278_, lean_object* v_x_1279_){
_start:
{
if (lean_obj_tag(v_x_1279_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v___f_1278_);
v_a_1281_ = lean_ctor_get(v_x_1279_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_x_1279_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1283_ = v_x_1279_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v_x_1279_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
}
else
{
lean_object* v_a_1290_; 
v_a_1290_ = lean_ctor_get(v_x_1279_, 0);
lean_inc(v_a_1290_);
if (lean_obj_tag(v_a_1290_) == 1)
{
lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v___f_1278_);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_a_1290_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_a_1290_, 0);
lean_dec(v_unused_1299_);
v___x_1292_ = v_a_1290_;
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
else
{
lean_dec(v_a_1290_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v_x_1279_);
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_x_1279_);
v___x_1295_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
return v___x_1296_;
}
}
}
else
{
lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_a_1290_);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_x_1279_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v_x_1279_, 0);
lean_dec(v_unused_1312_);
v___x_1301_ = v_x_1279_;
v_isShared_1302_ = v_isSharedCheck_1311_;
goto v_resetjp_1300_;
}
else
{
lean_dec(v_x_1279_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1311_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = 0;
v___x_1305_ = lean_st_ref_get(v_a_1277_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1305_);
v___x_1307_ = v___x_1301_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
v___x_1309_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1303_, v___x_1304_, v___x_1308_, v___f_1278_);
return v___x_1309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object* v_a_1313_, lean_object* v___f_1314_, lean_object* v_x_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_a_1313_, v___f_1314_, v_x_1315_);
lean_dec(v_a_1313_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1332_; 
v_a_1324_ = lean_ctor_get(v_x_1322_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1326_ = v_x_1322_;
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v_x_1322_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1351_; 
v_a_1333_ = lean_ctor_get(v_x_1322_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1335_ = v_x_1322_;
v_isShared_1336_ = v_isSharedCheck_1351_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v_x_1322_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1351_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_closeError_1337_; 
v_closeError_1337_ = lean_ctor_get(v_a_1333_, 5);
lean_inc(v_closeError_1337_);
lean_dec(v_a_1333_);
if (lean_obj_tag(v_closeError_1337_) == 1)
{
lean_object* v_val_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1349_; 
v_val_1338_ = lean_ctor_get(v_closeError_1337_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_closeError_1337_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1340_ = v_closeError_1337_;
v_isShared_1341_ = v_isSharedCheck_1349_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_val_1338_);
lean_dec(v_closeError_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1349_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 0);
lean_ctor_set(v___x_1335_, 0, v_val_1338_);
v___x_1343_ = v___x_1335_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_val_1338_);
v___x_1343_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1345_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1343_);
v___x_1345_ = v___x_1340_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
}
}
else
{
lean_object* v___x_1350_; 
lean_dec(v_closeError_1337_);
lean_del_object(v___x_1335_);
v___x_1350_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__1));
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object* v_x_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_x_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(lean_object* v_done_1355_, lean_object* v___f_1356_, lean_object* v_x_1357_){
_start:
{
if (lean_obj_tag(v_x_1357_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v___f_1356_);
v_a_1359_ = lean_ctor_get(v_x_1357_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1357_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1361_ = v_x_1357_;
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v_x_1357_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
}
else
{
uint8_t v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec_ref_known(v_x_1357_, 1);
v___x_1368_ = 1;
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = 0;
v___x_1371_ = lean_box(v___x_1368_);
v___x_1372_ = lean_io_promise_resolve(v___x_1371_, v_done_1355_);
v___x_1373_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1374_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1369_, v___x_1370_, v___x_1373_, v___f_1356_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed(lean_object* v_done_1375_, lean_object* v___f_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(v_done_1375_, v___f_1376_, v_x_1377_);
lean_dec(v_done_1375_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(lean_object* v_chunk_1380_, lean_object* v_x_1381_){
_start:
{
if (lean_obj_tag(v_x_1381_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v_chunk_1380_);
v_a_1383_ = lean_ctor_get(v_x_1381_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1385_ = v_x_1381_;
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v_x_1381_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
else
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v_x_1381_, 0);
lean_dec(v_unused_1401_);
v___x_1393_ = v_x_1381_;
v_isShared_1394_ = v_isSharedCheck_1400_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v_x_1381_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1400_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_chunk_1380_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1395_);
v___x_1397_ = v___x_1393_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed(lean_object* v_chunk_1402_, lean_object* v_x_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(v_chunk_1402_, v_x_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(lean_object* v_a_1408_, lean_object* v_x_1409_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1419_; 
v_a_1411_ = lean_ctor_get(v_x_1409_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_x_1409_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1413_ = v_x_1409_;
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v_x_1409_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v_pendingProducer_1421_; 
v_a_1420_ = lean_ctor_get(v_x_1409_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v_x_1409_, 1);
v_pendingProducer_1421_ = lean_ctor_get(v_a_1420_, 0);
if (lean_obj_tag(v_pendingProducer_1421_) == 1)
{
lean_object* v_val_1422_; lean_object* v_pendingConsumer_1423_; lean_object* v_interestWaiter_1424_; uint8_t v_closed_1425_; lean_object* v_knownSize_1426_; lean_object* v_pendingIncompleteChunk_1427_; lean_object* v_closeError_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1446_; 
v_val_1422_ = lean_ctor_get(v_pendingProducer_1421_, 0);
lean_inc(v_val_1422_);
v_pendingConsumer_1423_ = lean_ctor_get(v_a_1420_, 1);
v_interestWaiter_1424_ = lean_ctor_get(v_a_1420_, 2);
v_closed_1425_ = lean_ctor_get_uint8(v_a_1420_, sizeof(void*)*6);
v_knownSize_1426_ = lean_ctor_get(v_a_1420_, 3);
v_pendingIncompleteChunk_1427_ = lean_ctor_get(v_a_1420_, 4);
v_closeError_1428_ = lean_ctor_get(v_a_1420_, 5);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_a_1420_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_a_1420_, 0);
lean_dec(v_unused_1447_);
v___x_1430_ = v_a_1420_;
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_closeError_1428_);
lean_inc(v_pendingIncompleteChunk_1427_);
lean_inc(v_knownSize_1426_);
lean_inc(v_interestWaiter_1424_);
lean_inc(v_pendingConsumer_1423_);
lean_dec(v_a_1420_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_chunk_1432_; lean_object* v_done_1433_; lean_object* v___x_1434_; lean_object* v___f_1435_; lean_object* v___f_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v_chunk_1432_ = lean_ctor_get(v_val_1422_, 0);
lean_inc_ref_n(v_chunk_1432_, 2);
v_done_1433_ = lean_ctor_get(v_val_1422_, 1);
lean_inc(v_done_1433_);
lean_dec(v_val_1422_);
v___x_1434_ = lean_box(0);
v___f_1435_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1435_, 0, v_chunk_1432_);
v___f_1436_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1436_, 0, v_done_1433_);
lean_closure_set(v___f_1436_, 1, v___f_1435_);
v___x_1437_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1426_, v_chunk_1432_);
lean_dec_ref(v_chunk_1432_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 3, v___x_1437_);
lean_ctor_set(v___x_1430_, 0, v___x_1434_);
v___x_1439_ = v___x_1430_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_pendingConsumer_1423_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_interestWaiter_1424_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_pendingIncompleteChunk_1427_);
lean_ctor_set(v_reuseFailAlloc_1445_, 5, v_closeError_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1445_, sizeof(void*)*6, v_closed_1425_);
v___x_1439_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = 0;
v___x_1442_ = lean_st_ref_swap(v_a_1408_, v___x_1439_);
lean_dec(v___x_1442_);
v___x_1443_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1444_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1440_, v___x_1441_, v___x_1443_, v___f_1436_);
return v___x_1444_;
}
}
}
else
{
lean_object* v___x_1448_; 
lean_dec(v_a_1420_);
v___x_1448_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_1448_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1449_, lean_object* v_x_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(v_a_1449_, v_x_1450_);
lean_dec(v_a_1449_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(lean_object* v_a_1453_){
_start:
{
lean_object* v___f_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_inc(v_a_1453_);
v___f_1455_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1455_, 0, v_a_1453_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = 0;
v___x_1458_ = lean_st_ref_get(v_a_1453_);
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
v___x_1461_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1456_, v___x_1457_, v___x_1460_, v___f_1455_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___boxed(lean_object* v_a_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1462_);
lean_dec(v_a_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object* v_a_1466_){
_start:
{
lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___f_1468_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0));
lean_inc(v_a_1466_);
v___f_1469_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1469_, 0, v_a_1466_);
lean_closure_set(v___f_1469_, 1, v___f_1468_);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = 0;
v___x_1472_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1466_);
v___x_1473_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1470_, v___x_1471_, v___x_1472_, v___f_1469_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object* v_a_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_1474_);
lean_dec(v_a_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1(lean_object* v___y_1477_, lean_object* v___f_1478_, lean_object* v_x_1479_){
_start:
{
if (lean_obj_tag(v_x_1479_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v___f_1478_);
v_a_1481_ = lean_ctor_get(v_x_1479_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_x_1479_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1483_ = v_x_1479_;
v_isShared_1484_ = v_isSharedCheck_1489_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v_x_1479_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1489_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
}
else
{
lean_object* v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec_ref_known(v_x_1479_, 1);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = 0;
v___x_1492_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1477_);
v___x_1493_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1490_, v___x_1491_, v___x_1492_, v___f_1478_);
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(lean_object* v___y_1494_, lean_object* v___f_1495_, lean_object* v_x_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Std_Http_Body_Stream_tryRecv___lam__1(v___y_1494_, v___f_1495_, v_x_1496_);
lean_dec(v___y_1494_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2(lean_object* v___f_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___f_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_inc(v___y_1500_);
v___f_1502_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecv___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1502_, 0, v___y_1500_);
lean_closure_set(v___f_1502_, 1, v___f_1499_);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = 0;
v___x_1505_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1500_);
v___x_1506_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1503_, v___x_1504_, v___x_1505_, v___f_1502_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2___boxed(lean_object* v___f_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Std_Http_Body_Stream_tryRecv___lam__2(v___f_1507_, v___y_1508_);
lean_dec(v___y_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv(lean_object* v_stream_1514_){
_start:
{
lean_object* v___f_1516_; lean_object* v___x_1517_; 
v___f_1516_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecv___closed__1));
v___x_1517_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1514_, v___f_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___boxed(lean_object* v_stream_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Std_Http_Body_Stream_tryRecv(v_stream_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(lean_object* v_x_1521_){
_start:
{
uint8_t v___y_1524_; 
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1536_; 
v_a_1528_ = lean_ctor_get(v_x_1521_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1530_ = v_x_1521_;
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v_x_1521_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v_pendingProducer_1538_; 
v_a_1537_ = lean_ctor_get(v_x_1521_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v_x_1521_, 1);
v_pendingProducer_1538_ = lean_ctor_get(v_a_1537_, 0);
if (lean_obj_tag(v_pendingProducer_1538_) == 0)
{
uint8_t v_closed_1539_; 
v_closed_1539_ = lean_ctor_get_uint8(v_a_1537_, sizeof(void*)*6);
lean_dec(v_a_1537_);
v___y_1524_ = v_closed_1539_;
goto v___jp_1523_;
}
else
{
uint8_t v___x_1540_; 
lean_dec(v_a_1537_);
v___x_1540_ = 1;
v___y_1524_ = v___x_1540_;
goto v___jp_1523_;
}
}
v___jp_1523_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = lean_box(v___y_1524_);
v___x_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed(lean_object* v_x_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(v_x_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(lean_object* v_a_1545_){
_start:
{
lean_object* v___f_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___f_1547_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0));
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = 0;
v___x_1550_ = lean_st_ref_get(v_a_1545_);
v___x_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
v___x_1553_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1548_, v___x_1549_, v___x_1552_, v___f_1547_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___boxed(lean_object* v_a_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v_a_1554_);
lean_dec(v_a_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0(lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
v_a_1559_ = lean_ctor_get(v_x_1557_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1561_ = v_x_1557_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v_x_1557_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1568_; 
v_a_1568_ = lean_ctor_get(v_x_1557_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v_x_1557_, 1);
if (lean_obj_tag(v_a_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1577_; 
v_a_1569_ = lean_ctor_get(v_a_1568_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_a_1568_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1571_ = v_a_1568_;
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v_a_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1587_; 
v_a_1578_ = lean_ctor_get(v_a_1568_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_a_1568_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1580_ = v_a_1568_;
v_isShared_1581_ = v_isSharedCheck_1587_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v_a_1568_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1587_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_a_1578_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1582_);
v___x_1584_ = v___x_1580_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed(lean_object* v_x_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_Http_Body_Stream_tryRecvBody___lam__0(v_x_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1(lean_object* v___y_1595_, lean_object* v___f_1596_, lean_object* v_x_1597_){
_start:
{
if (lean_obj_tag(v_x_1597_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v___f_1596_);
v_a_1599_ = lean_ctor_get(v_x_1597_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1597_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1601_ = v_x_1597_;
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v_x_1597_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
}
else
{
lean_object* v_a_1608_; uint8_t v___x_1609_; 
v_a_1608_ = lean_ctor_get(v_x_1597_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v_x_1597_, 1);
v___x_1609_ = lean_unbox(v_a_1608_);
lean_dec(v_a_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_dec_ref(v___f_1596_);
v___x_1610_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1));
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = 0;
v___x_1613_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1595_);
v___x_1614_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1611_, v___x_1612_, v___x_1613_, v___f_1596_);
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed(lean_object* v___y_1615_, lean_object* v___f_1616_, lean_object* v_x_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1(v___y_1615_, v___f_1616_, v_x_1617_);
lean_dec(v___y_1615_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2(lean_object* v___y_1620_, lean_object* v___f_1621_, lean_object* v_x_1622_){
_start:
{
if (lean_obj_tag(v_x_1622_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v___f_1621_);
v_a_1624_ = lean_ctor_get(v_x_1622_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_x_1622_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1626_ = v_x_1622_;
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v_x_1622_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
}
}
else
{
lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref_known(v_x_1622_, 1);
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = 0;
v___x_1635_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_1620_);
v___x_1636_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1633_, v___x_1634_, v___x_1635_, v___f_1621_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed(lean_object* v___y_1637_, lean_object* v___f_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Std_Http_Body_Stream_tryRecvBody___lam__2(v___y_1637_, v___f_1638_, v_x_1639_);
lean_dec(v___y_1637_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3(lean_object* v___f_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_inc_n(v___y_1643_, 2);
v___f_1645_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1645_, 0, v___y_1643_);
lean_closure_set(v___f_1645_, 1, v___f_1642_);
v___f_1646_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1646_, 0, v___y_1643_);
lean_closure_set(v___f_1646_, 1, v___f_1645_);
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = 0;
v___x_1649_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1643_);
v___x_1650_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1647_, v___x_1648_, v___x_1649_, v___f_1646_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed(lean_object* v___f_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Std_Http_Body_Stream_tryRecvBody___lam__3(v___f_1651_, v___y_1652_);
lean_dec(v___y_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody(lean_object* v_stream_1658_){
_start:
{
lean_object* v___f_1660_; lean_object* v___x_1661_; 
v___f_1660_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_1661_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1658_, v___f_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___boxed(lean_object* v_stream_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_1662_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object* v_a_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v_pendingProducer_1668_; lean_object* v_pendingConsumer_1669_; lean_object* v_interestWaiter_1670_; uint8_t v_closed_1671_; lean_object* v_knownSize_1672_; lean_object* v_pendingIncompleteChunk_1673_; lean_object* v_closeError_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1701_; 
v___x_1667_ = lean_st_ref_get(v_a_1665_);
v_pendingProducer_1668_ = lean_ctor_get(v___x_1667_, 0);
v_pendingConsumer_1669_ = lean_ctor_get(v___x_1667_, 1);
v_interestWaiter_1670_ = lean_ctor_get(v___x_1667_, 2);
v_closed_1671_ = lean_ctor_get_uint8(v___x_1667_, sizeof(void*)*6);
v_knownSize_1672_ = lean_ctor_get(v___x_1667_, 3);
v_pendingIncompleteChunk_1673_ = lean_ctor_get(v___x_1667_, 4);
v_closeError_1674_ = lean_ctor_get(v___x_1667_, 5);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1676_ = v___x_1667_;
v_isShared_1677_ = v_isSharedCheck_1701_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_closeError_1674_);
lean_inc(v_pendingIncompleteChunk_1673_);
lean_inc(v_knownSize_1672_);
lean_inc(v_interestWaiter_1670_);
lean_inc(v_pendingConsumer_1669_);
lean_inc(v_pendingProducer_1668_);
lean_dec(v___x_1667_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1701_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___y_1679_; lean_object* v_interestWaiter_1680_; lean_object* v___y_1681_; lean_object* v_pendingConsumer_1688_; lean_object* v___y_1689_; 
if (lean_obj_tag(v_pendingConsumer_1669_) == 1)
{
lean_object* v_val_1695_; 
v_val_1695_ = lean_ctor_get(v_pendingConsumer_1669_, 0);
if (lean_obj_tag(v_val_1695_) == 1)
{
lean_object* v_finished_1696_; lean_object* v_finished_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_finished_1696_ = lean_ctor_get(v_val_1695_, 0);
v_finished_1697_ = lean_ctor_get(v_finished_1696_, 0);
v___x_1698_ = lean_st_ref_get(v_finished_1697_);
v___x_1699_ = lean_unbox(v___x_1698_);
lean_dec(v___x_1698_);
if (v___x_1699_ == 0)
{
v_pendingConsumer_1688_ = v_pendingConsumer_1669_;
v___y_1689_ = v_a_1665_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1700_; 
lean_dec_ref_known(v_pendingConsumer_1669_, 1);
v___x_1700_ = lean_box(0);
v_pendingConsumer_1688_ = v___x_1700_;
v___y_1689_ = v_a_1665_;
goto v___jp_1687_;
}
}
else
{
v_pendingConsumer_1688_ = v_pendingConsumer_1669_;
v___y_1689_ = v_a_1665_;
goto v___jp_1687_;
}
}
else
{
v_pendingConsumer_1688_ = v_pendingConsumer_1669_;
v___y_1689_ = v_a_1665_;
goto v___jp_1687_;
}
v___jp_1678_:
{
lean_object* v___x_1683_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 2, v_interestWaiter_1680_);
lean_ctor_set(v___x_1676_, 1, v___y_1679_);
v___x_1683_ = v___x_1676_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_pendingProducer_1668_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v___y_1679_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_interestWaiter_1680_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_knownSize_1672_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_pendingIncompleteChunk_1673_);
lean_ctor_set(v_reuseFailAlloc_1686_, 5, v_closeError_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*6, v_closed_1671_);
v___x_1683_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_st_ref_swap(v___y_1681_, v___x_1683_);
lean_dec(v___x_1685_);
return v___x_1684_;
}
}
v___jp_1687_:
{
if (lean_obj_tag(v_interestWaiter_1670_) == 0)
{
v___y_1679_ = v_pendingConsumer_1688_;
v_interestWaiter_1680_ = v_interestWaiter_1670_;
v___y_1681_ = v___y_1689_;
goto v___jp_1678_;
}
else
{
lean_object* v_val_1690_; lean_object* v_finished_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v_val_1690_ = lean_ctor_get(v_interestWaiter_1670_, 0);
v_finished_1691_ = lean_ctor_get(v_val_1690_, 0);
v___x_1692_ = lean_st_ref_get(v_finished_1691_);
v___x_1693_ = lean_unbox(v___x_1692_);
lean_dec(v___x_1692_);
if (v___x_1693_ == 0)
{
v___y_1679_ = v_pendingConsumer_1688_;
v_interestWaiter_1680_ = v_interestWaiter_1670_;
v___y_1681_ = v___y_1689_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1694_; 
lean_dec_ref_known(v_interestWaiter_1670_, 1);
v___x_1694_ = lean_box(0);
v___y_1679_ = v_pendingConsumer_1688_;
v_interestWaiter_1680_ = v___x_1694_;
v___y_1681_ = v___y_1689_;
goto v___jp_1678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object* v_a_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_1702_);
lean_dec(v_a_1702_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; lean_object* v_pendingProducer_1708_; 
v___x_1707_ = lean_st_ref_get(v_a_1705_);
v_pendingProducer_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_pendingProducer_1708_);
if (lean_obj_tag(v_pendingProducer_1708_) == 1)
{
lean_object* v_val_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1738_; 
v_val_1709_ = lean_ctor_get(v_pendingProducer_1708_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_pendingProducer_1708_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1711_ = v_pendingProducer_1708_;
v_isShared_1712_ = v_isSharedCheck_1738_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_val_1709_);
lean_dec(v_pendingProducer_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1738_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_pendingConsumer_1713_; lean_object* v_interestWaiter_1714_; uint8_t v_closed_1715_; lean_object* v_knownSize_1716_; lean_object* v_pendingIncompleteChunk_1717_; lean_object* v_closeError_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1736_; 
v_pendingConsumer_1713_ = lean_ctor_get(v___x_1707_, 1);
v_interestWaiter_1714_ = lean_ctor_get(v___x_1707_, 2);
v_closed_1715_ = lean_ctor_get_uint8(v___x_1707_, sizeof(void*)*6);
v_knownSize_1716_ = lean_ctor_get(v___x_1707_, 3);
v_pendingIncompleteChunk_1717_ = lean_ctor_get(v___x_1707_, 4);
v_closeError_1718_ = lean_ctor_get(v___x_1707_, 5);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v___x_1707_, 0);
lean_dec(v_unused_1737_);
v___x_1720_ = v___x_1707_;
v_isShared_1721_ = v_isSharedCheck_1736_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_closeError_1718_);
lean_inc(v_pendingIncompleteChunk_1717_);
lean_inc(v_knownSize_1716_);
lean_inc(v_interestWaiter_1714_);
lean_inc(v_pendingConsumer_1713_);
lean_dec(v___x_1707_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1736_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v_chunk_1722_; lean_object* v_done_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
v_chunk_1722_ = lean_ctor_get(v_val_1709_, 0);
lean_inc_ref(v_chunk_1722_);
v_done_1723_ = lean_ctor_get(v_val_1709_, 1);
lean_inc(v_done_1723_);
lean_dec(v_val_1709_);
v___x_1724_ = lean_box(0);
v___x_1725_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1716_, v_chunk_1722_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 3, v___x_1725_);
lean_ctor_set(v___x_1720_, 0, v___x_1724_);
v___x_1727_ = v___x_1720_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_pendingConsumer_1713_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_interestWaiter_1714_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_pendingIncompleteChunk_1717_);
lean_ctor_set(v_reuseFailAlloc_1735_, 5, v_closeError_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*6, v_closed_1715_);
v___x_1727_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1728_ = lean_st_ref_swap(v_a_1705_, v___x_1727_);
lean_dec(v___x_1728_);
v___x_1729_ = 1;
v___x_1730_ = lean_box(v___x_1729_);
v___x_1731_ = lean_io_promise_resolve(v___x_1730_, v_done_1723_);
lean_dec(v_done_1723_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v_chunk_1722_);
v___x_1733_ = v___x_1711_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_chunk_1722_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
else
{
lean_object* v___x_1739_; 
lean_dec(v_pendingProducer_1708_);
lean_dec(v___x_1707_);
v___x_1739_ = lean_box(0);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object* v_a_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_1740_);
lean_dec(v_a_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v_interestWaiter_1746_; 
v___x_1745_ = lean_st_ref_get(v_a_1743_);
v_interestWaiter_1746_ = lean_ctor_get(v___x_1745_, 2);
lean_inc(v_interestWaiter_1746_);
if (lean_obj_tag(v_interestWaiter_1746_) == 1)
{
lean_object* v_pendingProducer_1747_; lean_object* v_pendingConsumer_1748_; uint8_t v_closed_1749_; lean_object* v_knownSize_1750_; lean_object* v_pendingIncompleteChunk_1751_; lean_object* v_closeError_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1765_; 
v_pendingProducer_1747_ = lean_ctor_get(v___x_1745_, 0);
v_pendingConsumer_1748_ = lean_ctor_get(v___x_1745_, 1);
v_closed_1749_ = lean_ctor_get_uint8(v___x_1745_, sizeof(void*)*6);
v_knownSize_1750_ = lean_ctor_get(v___x_1745_, 3);
v_pendingIncompleteChunk_1751_ = lean_ctor_get(v___x_1745_, 4);
v_closeError_1752_ = lean_ctor_get(v___x_1745_, 5);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1745_, 2);
lean_dec(v_unused_1766_);
v___x_1754_ = v___x_1745_;
v_isShared_1755_ = v_isSharedCheck_1765_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_closeError_1752_);
lean_inc(v_pendingIncompleteChunk_1751_);
lean_inc(v_knownSize_1750_);
lean_inc(v_pendingConsumer_1748_);
lean_inc(v_pendingProducer_1747_);
lean_dec(v___x_1745_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1765_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_val_1756_; uint8_t v___x_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v_val_1756_ = lean_ctor_get(v_interestWaiter_1746_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v_interestWaiter_1746_, 1);
v___x_1757_ = 1;
v___x_1758_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1756_, v___x_1757_);
lean_dec(v_val_1756_);
v___x_1759_ = lean_box(0);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 2, v___x_1759_);
v___x_1761_ = v___x_1754_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_pendingProducer_1747_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_pendingConsumer_1748_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_knownSize_1750_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_pendingIncompleteChunk_1751_);
lean_ctor_set(v_reuseFailAlloc_1764_, 5, v_closeError_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1764_, sizeof(void*)*6, v_closed_1749_);
v___x_1761_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_st_ref_swap(v_a_1743_, v___x_1761_);
lean_dec(v___x_1763_);
return v___x_1762_;
}
}
}
else
{
lean_object* v___x_1767_; 
lean_dec(v_interestWaiter_1746_);
lean_dec(v___x_1745_);
v___x_1767_ = lean_box(0);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object* v_a_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_1768_);
lean_dec(v_a_1768_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object* v_mutex_1771_, lean_object* v_k_1772_){
_start:
{
lean_object* v_ref_1774_; lean_object* v_mutex_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_ref_1774_ = lean_ctor_get(v_mutex_1771_, 0);
lean_inc(v_ref_1774_);
v_mutex_1775_ = lean_ctor_get(v_mutex_1771_, 1);
lean_inc(v_mutex_1775_);
lean_dec_ref(v_mutex_1771_);
v___x_1776_ = lean_io_basemutex_lock(v_mutex_1775_);
v___x_1777_ = lean_apply_2(v_k_1772_, v_ref_1774_, lean_box(0));
v___x_1778_ = lean_io_basemutex_unlock(v_mutex_1775_);
lean_dec(v_mutex_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object* v_mutex_1779_, lean_object* v_k_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1779_, v_k_1780_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object* v_00_u03b1_1783_, lean_object* v_00_u03b2_1784_, lean_object* v_mutex_1785_, lean_object* v_k_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1785_, v_k_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object* v_00_u03b1_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_mutex_1791_, lean_object* v_k_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(v_00_u03b1_1789_, v_00_u03b2_1790_, v_mutex_1791_, v_k_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object* v_x_1800_){
_start:
{
if (lean_obj_tag(v_x_1800_) == 0)
{
lean_object* v___x_1801_; 
v___x_1801_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2));
return v___x_1801_;
}
else
{
lean_object* v_val_1802_; 
v_val_1802_ = lean_ctor_get(v_x_1800_, 0);
lean_inc(v_val_1802_);
return v_val_1802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___boxed(lean_object* v_x_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(v_x_1803_);
lean_dec(v_x_1803_);
return v_res_1804_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2));
v___x_1811_ = lean_task_pure(v___x_1810_);
return v___x_1811_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_1813_ = lean_task_pure(v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object* v___f_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v_closed_1819_; 
v___x_1817_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_1815_);
v___x_1818_ = lean_st_ref_get(v___y_1815_);
v_closed_1819_ = lean_ctor_get_uint8(v___x_1818_, sizeof(void*)*6);
if (v_closed_1819_ == 0)
{
uint8_t v___x_1820_; lean_object* v___x_1821_; 
lean_dec(v___x_1818_);
v___x_1820_ = 1;
v___x_1821_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_1815_);
if (lean_obj_tag(v___x_1821_) == 1)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v___f_1814_);
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
v___x_1823_ = lean_task_pure(v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; lean_object* v_pendingConsumer_1825_; 
lean_dec(v___x_1821_);
v___x_1824_ = lean_st_ref_get(v___y_1815_);
v_pendingConsumer_1825_ = lean_ctor_get(v___x_1824_, 1);
if (lean_obj_tag(v_pendingConsumer_1825_) == 0)
{
lean_object* v_pendingProducer_1826_; lean_object* v_interestWaiter_1827_; uint8_t v_closed_1828_; lean_object* v_knownSize_1829_; lean_object* v_pendingIncompleteChunk_1830_; lean_object* v_closeError_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1846_; 
v_pendingProducer_1826_ = lean_ctor_get(v___x_1824_, 0);
v_interestWaiter_1827_ = lean_ctor_get(v___x_1824_, 2);
v_closed_1828_ = lean_ctor_get_uint8(v___x_1824_, sizeof(void*)*6);
v_knownSize_1829_ = lean_ctor_get(v___x_1824_, 3);
v_pendingIncompleteChunk_1830_ = lean_ctor_get(v___x_1824_, 4);
v_closeError_1831_ = lean_ctor_get(v___x_1824_, 5);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; 
v_unused_1847_ = lean_ctor_get(v___x_1824_, 1);
lean_dec(v_unused_1847_);
v___x_1833_ = v___x_1824_;
v_isShared_1834_ = v_isSharedCheck_1846_;
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
v_isShared_1834_ = v_isSharedCheck_1846_;
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
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_pendingProducer_1826_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_interestWaiter_1827_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_knownSize_1829_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_pendingIncompleteChunk_1830_);
lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_closeError_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1845_, sizeof(void*)*6, v_closed_1828_);
v___x_1839_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1840_ = lean_st_ref_swap(v___y_1815_, v___x_1839_);
lean_dec(v___x_1840_);
v___x_1841_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_1815_);
v___x_1842_ = lean_io_promise_result_opt(v___x_1835_);
lean_dec(v___x_1835_);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = lean_task_map(v___f_1814_, v___x_1842_, v___x_1843_, v___x_1820_);
return v___x_1844_;
}
}
}
else
{
lean_object* v___x_1848_; 
lean_dec(v___x_1824_);
lean_dec_ref(v___f_1814_);
v___x_1848_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3);
return v___x_1848_;
}
}
}
else
{
lean_object* v_closeError_1849_; 
lean_dec_ref(v___f_1814_);
v_closeError_1849_ = lean_ctor_get(v___x_1818_, 5);
lean_inc(v_closeError_1849_);
lean_dec(v___x_1818_);
if (lean_obj_tag(v_closeError_1849_) == 0)
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4);
return v___x_1850_;
}
else
{
lean_object* v_val_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_val_1851_ = lean_ctor_get(v_closeError_1849_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_closeError_1849_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v_closeError_1849_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_val_1851_);
lean_dec(v_closeError_1849_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 0);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_val_1851_);
v___x_1856_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_task_pure(v___x_1856_);
return v___x_1857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object* v___f_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(v___f_1860_, v___y_1861_);
lean_dec(v___y_1861_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object* v_stream_1867_){
_start:
{
lean_object* v___f_1869_; lean_object* v___x_1870_; 
v___f_1869_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1));
v___x_1870_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_1867_, v___f_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object* v_stream_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1871_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object* v_x_1874_){
_start:
{
if (lean_obj_tag(v_x_1874_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1884_; 
v_a_1876_ = lean_ctor_get(v_x_1874_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_x_1874_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1878_ = v_x_1874_;
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v_x_1874_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1886_; 
v_a_1885_ = lean_ctor_get(v_x_1874_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v_x_1874_, 1);
v___x_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1886_, 0, v_a_1885_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object* v_x_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv(lean_object* v_stream_1891_){
_start:
{
lean_object* v___f_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___f_1893_ = ((lean_object*)(l_Std_Http_Body_Stream_recv___closed__0));
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = 0;
v___x_1896_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1891_);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
v___x_1899_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1894_, v___x_1895_, v___x_1898_, v___f_1893_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object* v_stream_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Std_Http_Body_Stream_recv(v_stream_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(uint8_t v___x_1903_, lean_object* v_knownSize_1904_, lean_object* v_closeError_1905_, lean_object* v_____r_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
lean_ctor_set(v___x_1910_, 2, v___x_1909_);
lean_ctor_set(v___x_1910_, 3, v_knownSize_1904_);
lean_ctor_set(v___x_1910_, 4, v___x_1909_);
lean_ctor_set(v___x_1910_, 5, v_closeError_1905_);
lean_ctor_set_uint8(v___x_1910_, sizeof(void*)*6, v___x_1903_);
v___x_1911_ = lean_st_ref_swap(v___y_1907_, v___x_1910_);
lean_dec(v___x_1911_);
v___x_1912_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(lean_object* v___x_1913_, lean_object* v_knownSize_1914_, lean_object* v_closeError_1915_, lean_object* v_____r_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
uint8_t v___x_2195__boxed_1919_; lean_object* v_res_1920_; 
v___x_2195__boxed_1919_ = lean_unbox(v___x_1913_);
v_res_1920_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(v___x_2195__boxed_1919_, v_knownSize_1914_, v_closeError_1915_, v_____r_1916_, v___y_1917_);
lean_dec(v___y_1917_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(lean_object* v___f_1921_, lean_object* v___y_1922_, lean_object* v_x_1923_){
_start:
{
if (lean_obj_tag(v_x_1923_) == 0)
{
lean_object* v___x_1925_; 
lean_dec_ref(v___f_1921_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_x_1923_);
return v___x_1925_;
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v_x_1923_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v_x_1923_, 1);
lean_inc(v___y_1922_);
v___x_1927_ = lean_apply_3(v___f_1921_, v_a_1926_, v___y_1922_, lean_box(0));
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed(lean_object* v___f_1928_, lean_object* v___y_1929_, lean_object* v_x_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(v___f_1928_, v___y_1929_, v_x_1930_);
lean_dec(v___y_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object* v_pendingProducer_1933_, lean_object* v___f_1934_, uint8_t v_closed_1935_, lean_object* v_____r_1936_, lean_object* v___y_1937_){
_start:
{
if (lean_obj_tag(v_pendingProducer_1933_) == 1)
{
lean_object* v_val_1939_; lean_object* v_done_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_val_1939_ = lean_ctor_get(v_pendingProducer_1933_, 0);
v_done_1940_ = lean_ctor_get(v_val_1939_, 1);
lean_inc(v___y_1937_);
v___f_1941_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1941_, 0, v___f_1934_);
lean_closure_set(v___f_1941_, 1, v___y_1937_);
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_box(v_closed_1935_);
v___x_1944_ = lean_io_promise_resolve(v___x_1943_, v_done_1940_);
v___x_1945_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1946_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1942_, v_closed_1935_, v___x_1945_, v___f_1941_);
return v___x_1946_;
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_box(0);
lean_inc(v___y_1937_);
v___x_1948_ = lean_apply_3(v___f_1934_, v___x_1947_, v___y_1937_, lean_box(0));
return v___x_1948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object* v_pendingProducer_1949_, lean_object* v___f_1950_, lean_object* v_closed_1951_, lean_object* v_____r_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
uint8_t v_closed_boxed_1955_; lean_object* v_res_1956_; 
v_closed_boxed_1955_ = lean_unbox(v_closed_1951_);
v_res_1956_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(v_pendingProducer_1949_, v___f_1950_, v_closed_boxed_1955_, v_____r_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec(v_pendingProducer_1949_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object* v_interestWaiter_1957_, lean_object* v___f_1958_, uint8_t v_closed_1959_, lean_object* v_____r_1960_, lean_object* v___y_1961_){
_start:
{
if (lean_obj_tag(v_interestWaiter_1957_) == 1)
{
lean_object* v_val_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_val_1963_ = lean_ctor_get(v_interestWaiter_1957_, 0);
lean_inc(v___y_1961_);
v___f_1964_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1964_, 0, v___f_1958_);
lean_closure_set(v___f_1964_, 1, v___y_1961_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1963_, v_closed_1959_);
v___x_1967_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1968_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1965_, v_closed_1959_, v___x_1967_, v___f_1964_);
return v___x_1968_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_box(0);
lean_inc(v___y_1961_);
v___x_1970_ = lean_apply_3(v___f_1958_, v___x_1969_, v___y_1961_, lean_box(0));
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(lean_object* v_interestWaiter_1971_, lean_object* v___f_1972_, lean_object* v_closed_1973_, lean_object* v_____r_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
uint8_t v_closed_boxed_1977_; lean_object* v_res_1978_; 
v_closed_boxed_1977_ = lean_unbox(v_closed_1973_);
v_res_1978_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_1971_, v___f_1972_, v_closed_boxed_1977_, v_____r_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec(v_interestWaiter_1971_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(lean_object* v___f_1979_, lean_object* v_a_1980_, lean_object* v_x_1981_){
_start:
{
if (lean_obj_tag(v_x_1981_) == 0)
{
lean_object* v___x_1983_; 
lean_dec_ref(v___f_1979_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_x_1981_);
return v___x_1983_;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1985_; 
v_a_1984_ = lean_ctor_get(v_x_1981_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v_x_1981_, 1);
lean_inc(v_a_1980_);
v___x_1985_ = lean_apply_3(v___f_1979_, v_a_1984_, v_a_1980_, lean_box(0));
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed(lean_object* v___f_1986_, lean_object* v_a_1987_, lean_object* v_x_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(v___f_1986_, v_a_1987_, v_x_1988_);
lean_dec(v_a_1987_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(lean_object* v_a_1991_, lean_object* v_x_1992_){
_start:
{
if (lean_obj_tag(v_x_1992_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2002_; 
v_a_1994_ = lean_ctor_get(v_x_1992_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1996_ = v_x_1992_;
v_isShared_1997_ = v_isSharedCheck_2002_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v_x_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2002_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
return v___x_2000_;
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2036_; 
v_a_2003_ = lean_ctor_get(v_x_1992_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2005_ = v_x_1992_;
v_isShared_2006_ = v_isSharedCheck_2036_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v_x_1992_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2036_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
uint8_t v_closed_2007_; 
v_closed_2007_ = lean_ctor_get_uint8(v_a_2003_, sizeof(void*)*6);
if (v_closed_2007_ == 0)
{
lean_object* v_pendingProducer_2008_; lean_object* v_pendingConsumer_2009_; lean_object* v_interestWaiter_2010_; lean_object* v_knownSize_2011_; lean_object* v_closeError_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; lean_object* v___f_2019_; 
v_pendingProducer_2008_ = lean_ctor_get(v_a_2003_, 0);
lean_inc(v_pendingProducer_2008_);
v_pendingConsumer_2009_ = lean_ctor_get(v_a_2003_, 1);
lean_inc(v_pendingConsumer_2009_);
v_interestWaiter_2010_ = lean_ctor_get(v_a_2003_, 2);
lean_inc_n(v_interestWaiter_2010_, 2);
v_knownSize_2011_ = lean_ctor_get(v_a_2003_, 3);
lean_inc(v_knownSize_2011_);
v_closeError_2012_ = lean_ctor_get(v_a_2003_, 5);
lean_inc_n(v_closeError_2012_, 2);
lean_dec(v_a_2003_);
v___x_2013_ = 1;
v___x_2014_ = lean_box(v___x_2013_);
v___f_2015_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2015_, 0, v___x_2014_);
lean_closure_set(v___f_2015_, 1, v_knownSize_2011_);
lean_closure_set(v___f_2015_, 2, v_closeError_2012_);
v___x_2016_ = lean_box(v_closed_2007_);
v___f_2017_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2017_, 0, v_pendingProducer_2008_);
lean_closure_set(v___f_2017_, 1, v___f_2015_);
lean_closure_set(v___f_2017_, 2, v___x_2016_);
v___x_2018_ = lean_box(v_closed_2007_);
lean_inc_ref(v___f_2017_);
v___f_2019_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2019_, 0, v_interestWaiter_2010_);
lean_closure_set(v___f_2019_, 1, v___f_2017_);
lean_closure_set(v___f_2019_, 2, v___x_2018_);
if (lean_obj_tag(v_pendingConsumer_2009_) == 1)
{
lean_object* v_val_2020_; lean_object* v___f_2021_; lean_object* v___y_2023_; 
lean_dec_ref(v___f_2017_);
lean_dec(v_interestWaiter_2010_);
v_val_2020_ = lean_ctor_get(v_pendingConsumer_2009_, 0);
lean_inc(v_val_2020_);
lean_dec_ref_known(v_pendingConsumer_2009_, 1);
lean_inc(v_a_1991_);
v___f_2021_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2021_, 0, v___f_2019_);
lean_closure_set(v___f_2021_, 1, v_a_1991_);
if (lean_obj_tag(v_closeError_2012_) == 0)
{
lean_object* v___x_2028_; 
lean_del_object(v___x_2005_);
v___x_2028_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___y_2023_ = v___x_2028_;
goto v___jp_2022_;
}
else
{
lean_object* v_val_2029_; lean_object* v___x_2031_; 
v_val_2029_ = lean_ctor_get(v_closeError_2012_, 0);
lean_inc(v_val_2029_);
lean_dec_ref_known(v_closeError_2012_, 1);
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 0);
lean_ctor_set(v___x_2005_, 0, v_val_2029_);
v___x_2031_ = v___x_2005_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_val_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
v___y_2023_ = v___x_2031_;
goto v___jp_2022_;
}
}
v___jp_2022_:
{
lean_object* v___x_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_2020_, v___y_2023_);
lean_dec(v_val_2020_);
v___x_2026_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2027_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2024_, v_closed_2007_, v___x_2026_, v___f_2021_);
return v___x_2027_;
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec_ref(v___f_2019_);
lean_dec(v_closeError_2012_);
lean_dec(v_pendingConsumer_2009_);
lean_del_object(v___x_2005_);
v___x_2033_ = lean_box(0);
v___x_2034_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_2010_, v___f_2017_, v_closed_2007_, v___x_2033_, v_a_1991_);
lean_dec(v_interestWaiter_2010_);
return v___x_2034_;
}
}
else
{
lean_object* v___x_2035_; 
lean_del_object(v___x_2005_);
lean_dec(v_a_2003_);
v___x_2035_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed(lean_object* v_a_2037_, lean_object* v_x_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(v_a_2037_, v_x_2038_);
lean_dec(v_a_2037_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(lean_object* v_a_2041_){
_start:
{
lean_object* v___f_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_inc(v_a_2041_);
v___f_2043_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed), 3, 1);
lean_closure_set(v___f_2043_, 0, v_a_2041_);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = 0;
v___x_2046_ = lean_st_ref_get(v_a_2041_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
v___x_2049_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2044_, v___x_2045_, v___x_2048_, v___f_2043_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed(lean_object* v_a_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v_a_2050_);
lean_dec(v_a_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close(lean_object* v_stream_2054_){
_start:
{
lean_object* v___f_2056_; lean_object* v___x_2057_; 
v___f_2056_ = ((lean_object*)(l_Std_Http_Body_Stream_close___closed__0));
v___x_2057_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2054_, v___f_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object* v_stream_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Std_Http_Body_Stream_close(v_stream_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(uint8_t v___x_2061_, lean_object* v_x_2062_){
_start:
{
if (lean_obj_tag(v_x_2062_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2072_; 
v_a_2064_ = lean_ctor_get(v_x_2062_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_x_2062_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2066_ = v_x_2062_;
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v_x_2062_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
}
}
else
{
lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2081_; 
v_isSharedCheck_2081_ = !lean_is_exclusive(v_x_2062_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v_x_2062_, 0);
lean_dec(v_unused_2082_);
v___x_2074_ = v_x_2062_;
v_isShared_2075_ = v_isSharedCheck_2081_;
goto v_resetjp_2073_;
}
else
{
lean_dec(v_x_2062_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2081_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_box(v___x_2061_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0___boxed(lean_object* v___x_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_){
_start:
{
uint8_t v___x_1415__boxed_2086_; lean_object* v_res_2087_; 
v___x_1415__boxed_2086_ = lean_unbox(v___x_2083_);
v_res_2087_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(v___x_1415__boxed_2086_, v_x_2084_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(lean_object* v___y_2091_, lean_object* v_x_2092_){
_start:
{
uint8_t v___y_2095_; 
if (lean_obj_tag(v_x_2092_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2107_; 
v_a_2099_ = lean_ctor_get(v_x_2092_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_x_2092_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2101_ = v_x_2092_;
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v_x_2092_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
}
}
else
{
lean_object* v_a_2108_; uint8_t v_closed_2109_; 
v_a_2108_ = lean_ctor_get(v_x_2092_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v_x_2092_, 1);
v_closed_2109_ = lean_ctor_get_uint8(v_a_2108_, sizeof(void*)*6);
if (v_closed_2109_ == 0)
{
lean_object* v_pendingConsumer_2110_; 
v_pendingConsumer_2110_ = lean_ctor_get(v_a_2108_, 1);
lean_inc(v_pendingConsumer_2110_);
lean_dec(v_a_2108_);
if (lean_obj_tag(v_pendingConsumer_2110_) == 0)
{
lean_object* v___f_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___f_2111_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0));
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2113_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v___y_2091_);
v___x_2114_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2112_, v_closed_2109_, v___x_2113_, v___f_2111_);
return v___x_2114_;
}
else
{
lean_dec_ref_known(v_pendingConsumer_2110_, 1);
v___y_2095_ = v_closed_2109_;
goto v___jp_2094_;
}
}
else
{
uint8_t v___x_2115_; 
lean_dec(v_a_2108_);
v___x_2115_ = 0;
v___y_2095_ = v___x_2115_;
goto v___jp_2094_;
}
}
v___jp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_box(v___y_2095_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed(lean_object* v___y_2116_, lean_object* v_x_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(v___y_2116_, v_x_2117_);
lean_dec(v___y_2116_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(lean_object* v___y_2120_, lean_object* v___f_2121_, lean_object* v_x_2122_){
_start:
{
if (lean_obj_tag(v_x_2122_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v___f_2121_);
v_a_2124_ = lean_ctor_get(v_x_2122_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_2122_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2126_ = v_x_2122_;
v_isShared_2127_ = v_isSharedCheck_2132_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v_x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2132_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
return v___x_2130_;
}
}
}
else
{
lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2144_; 
v_isSharedCheck_2144_ = !lean_is_exclusive(v_x_2122_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v_x_2122_, 0);
lean_dec(v_unused_2145_);
v___x_2134_ = v_x_2122_;
v_isShared_2135_ = v_isSharedCheck_2144_;
goto v_resetjp_2133_;
}
else
{
lean_dec(v_x_2122_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2144_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = 0;
v___x_2138_ = lean_st_ref_get(v___y_2120_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2138_);
v___x_2140_ = v___x_2134_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
v___x_2142_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2136_, v___x_2137_, v___x_2141_, v___f_2121_);
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed(lean_object* v___y_2146_, lean_object* v___f_2147_, lean_object* v_x_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(v___y_2146_, v___f_2147_, v_x_2148_);
lean_dec(v___y_2146_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(lean_object* v___y_2151_){
_start:
{
lean_object* v___f_2153_; lean_object* v___f_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_inc_n(v___y_2151_, 2);
v___f_2153_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2153_, 0, v___y_2151_);
v___f_2154_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2154_, 0, v___y_2151_);
lean_closure_set(v___f_2154_, 1, v___f_2153_);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = 0;
v___x_2157_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2151_);
v___x_2158_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2155_, v___x_2156_, v___x_2157_, v___f_2154_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3___boxed(lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(v___y_2159_);
lean_dec(v___y_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned(lean_object* v_stream_2163_){
_start:
{
lean_object* v___f_2165_; lean_object* v___x_2166_; 
v___f_2165_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___closed__0));
v___x_2166_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2163_, v___f_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___boxed(lean_object* v_stream_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Std_Http_Body_Stream_closeIfAbandoned(v_stream_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0(lean_object* v___y_2170_, lean_object* v_x_2171_){
_start:
{
if (lean_obj_tag(v_x_2171_) == 0)
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_x_2171_);
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; 
lean_dec_ref_known(v_x_2171_, 1);
v___x_2174_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v___y_2170_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0___boxed(lean_object* v___y_2175_, lean_object* v_x_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Std_Http_Body_Stream_closeWithError___lam__0(v___y_2175_, v_x_2176_);
lean_dec(v___y_2175_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1(lean_object* v_err_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___f_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v_fst_2187_; lean_object* v_snd_2188_; lean_object* v_pendingProducer_2193_; lean_object* v_pendingConsumer_2194_; lean_object* v_interestWaiter_2195_; uint8_t v_closed_2196_; lean_object* v_knownSize_2197_; lean_object* v_pendingIncompleteChunk_2198_; lean_object* v_closeError_2199_; lean_object* v___x_2200_; 
lean_inc(v___y_2180_);
v___f_2182_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2182_, 0, v___y_2180_);
v___x_2183_ = lean_unsigned_to_nat(0u);
v___x_2184_ = 0;
v___x_2185_ = lean_st_ref_take(v___y_2180_);
v_pendingProducer_2193_ = lean_ctor_get(v___x_2185_, 0);
v_pendingConsumer_2194_ = lean_ctor_get(v___x_2185_, 1);
v_interestWaiter_2195_ = lean_ctor_get(v___x_2185_, 2);
v_closed_2196_ = lean_ctor_get_uint8(v___x_2185_, sizeof(void*)*6);
v_knownSize_2197_ = lean_ctor_get(v___x_2185_, 3);
v_pendingIncompleteChunk_2198_ = lean_ctor_get(v___x_2185_, 4);
v_closeError_2199_ = lean_ctor_get(v___x_2185_, 5);
v___x_2200_ = lean_box(0);
if (lean_obj_tag(v_closeError_2199_) == 0)
{
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2208_; 
lean_inc(v_pendingIncompleteChunk_2198_);
lean_inc(v_knownSize_2197_);
lean_inc(v_interestWaiter_2195_);
lean_inc(v_pendingConsumer_2194_);
lean_inc(v_pendingProducer_2193_);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; lean_object* v_unused_2210_; lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; 
v_unused_2209_ = lean_ctor_get(v___x_2185_, 5);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v___x_2185_, 4);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v___x_2185_, 3);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v___x_2185_, 2);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v___x_2185_, 1);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v___x_2185_, 0);
lean_dec(v_unused_2214_);
v___x_2202_ = v___x_2185_;
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v___x_2185_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v_err_2179_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 5, v___x_2204_);
v___x_2206_ = v___x_2202_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_pendingProducer_2193_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_pendingConsumer_2194_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_interestWaiter_2195_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v_knownSize_2197_);
lean_ctor_set(v_reuseFailAlloc_2207_, 4, v_pendingIncompleteChunk_2198_);
lean_ctor_set(v_reuseFailAlloc_2207_, 5, v___x_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2207_, sizeof(void*)*6, v_closed_2196_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
v_fst_2187_ = v___x_2200_;
v_snd_2188_ = v___x_2206_;
goto v___jp_2186_;
}
}
}
else
{
lean_dec(v_err_2179_);
v_fst_2187_ = v___x_2200_;
v_snd_2188_ = v___x_2185_;
goto v___jp_2186_;
}
v___jp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2189_ = lean_st_ref_put(v___y_2180_, v_snd_2188_);
v___x_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2190_, 0, v_fst_2187_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
v___x_2192_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2183_, v___x_2184_, v___x_2191_, v___f_2182_);
return v___x_2192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1___boxed(lean_object* v_err_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Std_Http_Body_Stream_closeWithError___lam__1(v_err_2215_, v___y_2216_);
lean_dec(v___y_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError(lean_object* v_stream_2219_, lean_object* v_err_2220_){
_start:
{
lean_object* v___f_2222_; lean_object* v___x_2223_; 
v___f_2222_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2222_, 0, v_err_2220_);
v___x_2223_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2219_, v___f_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___boxed(lean_object* v_stream_2224_, lean_object* v_err_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Std_Http_Body_Stream_closeWithError(v_stream_2224_, v_err_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object* v_____do__lift_2228_, lean_object* v___y_2229_){
_start:
{
uint8_t v_closed_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_closed_2231_ = lean_ctor_get_uint8(v_____do__lift_2228_, sizeof(void*)*6);
v___x_2232_ = lean_box(v_closed_2231_);
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object* v_____do__lift_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v_____do__lift_2235_);
return v_res_2238_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__1(void){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_2240_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__2(void){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_2241_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__6(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___f_2248_; lean_object* v___f_2249_; 
v___x_2247_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2248_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___f_2249_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2249_, 0, v___f_2248_);
lean_closure_set(v___f_2249_, 1, v___x_2247_);
return v___f_2249_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__11(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___f_2259_; lean_object* v___f_2260_; 
v___x_2258_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2259_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__10));
v___f_2260_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2260_, 0, v___f_2259_);
lean_closure_set(v___f_2260_, 1, v___x_2258_);
return v___f_2260_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__12(void){
_start:
{
lean_object* v___f_2261_; lean_object* v___x_2262_; 
v___f_2261_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__11, &l_Std_Http_Body_Stream_isClosed___closed__11_once, _init_l_Std_Http_Body_Stream_isClosed___closed__11);
v___x_2262_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2262_, 0, lean_box(0));
lean_closure_set(v___x_2262_, 1, lean_box(0));
lean_closure_set(v___x_2262_, 2, lean_box(0));
lean_closure_set(v___x_2262_, 3, v___f_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__13(void){
_start:
{
lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___f_2263_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__0));
v___x_2264_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2265_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2266_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2266_, 0, lean_box(0));
lean_closure_set(v___x_2266_, 1, lean_box(0));
lean_closure_set(v___x_2266_, 2, v___x_2265_);
lean_closure_set(v___x_2266_, 3, lean_box(0));
lean_closure_set(v___x_2266_, 4, lean_box(0));
lean_closure_set(v___x_2266_, 5, v___x_2264_);
lean_closure_set(v___x_2266_, 6, v___f_2263_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed(lean_object* v_stream_2267_){
_start:
{
lean_object* v___x_2269_; lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; lean_object* v___x_214__overap_2273_; lean_object* v___x_2274_; 
v___x_2269_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2270_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2271_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2272_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__13, &l_Std_Http_Body_Stream_isClosed___closed__13_once, _init_l_Std_Http_Body_Stream_isClosed___closed__13);
v___x_214__overap_2273_ = l_Std_Mutex_atomically___redArg(v___x_2269_, v___f_2270_, v___f_2271_, v_stream_2267_, v___x_2272_);
v___x_2274_ = lean_apply_1(v___x_214__overap_2273_, lean_box(0));
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___boxed(lean_object* v_stream_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Std_Http_Body_Stream_isClosed(v_stream_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0(lean_object* v_____do__lift_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_knownSize_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_knownSize_2281_ = lean_ctor_get(v_____do__lift_2278_, 3);
lean_inc(v_knownSize_2281_);
v___x_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_knownSize_2281_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(lean_object* v_____do__lift_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v_____do__lift_2284_);
return v_res_2287_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_getKnownSize___closed__1(void){
_start:
{
lean_object* v___f_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___f_2289_ = ((lean_object*)(l_Std_Http_Body_Stream_getKnownSize___closed__0));
v___x_2290_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2291_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2292_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2292_, 0, lean_box(0));
lean_closure_set(v___x_2292_, 1, lean_box(0));
lean_closure_set(v___x_2292_, 2, v___x_2291_);
lean_closure_set(v___x_2292_, 3, lean_box(0));
lean_closure_set(v___x_2292_, 4, lean_box(0));
lean_closure_set(v___x_2292_, 5, v___x_2290_);
lean_closure_set(v___x_2292_, 6, v___f_2289_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize(lean_object* v_stream_2293_){
_start:
{
lean_object* v___x_2295_; lean_object* v___f_2296_; lean_object* v___f_2297_; lean_object* v___x_2298_; lean_object* v___x_214__overap_2299_; lean_object* v___x_2300_; 
v___x_2295_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2296_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2297_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2298_ = lean_obj_once(&l_Std_Http_Body_Stream_getKnownSize___closed__1, &l_Std_Http_Body_Stream_getKnownSize___closed__1_once, _init_l_Std_Http_Body_Stream_getKnownSize___closed__1);
v___x_214__overap_2299_ = l_Std_Mutex_atomically___redArg(v___x_2295_, v___f_2296_, v___f_2297_, v_stream_2293_, v___x_2298_);
v___x_2300_ = lean_apply_1(v___x_214__overap_2299_, lean_box(0));
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___boxed(lean_object* v_stream_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0(lean_object* v_size_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v_pendingProducer_2308_; lean_object* v_pendingConsumer_2309_; lean_object* v_interestWaiter_2310_; uint8_t v_closed_2311_; lean_object* v_pendingIncompleteChunk_2312_; lean_object* v_closeError_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2322_; 
v___x_2307_ = lean_st_ref_take(v___y_2305_);
v_pendingProducer_2308_ = lean_ctor_get(v___x_2307_, 0);
v_pendingConsumer_2309_ = lean_ctor_get(v___x_2307_, 1);
v_interestWaiter_2310_ = lean_ctor_get(v___x_2307_, 2);
v_closed_2311_ = lean_ctor_get_uint8(v___x_2307_, sizeof(void*)*6);
v_pendingIncompleteChunk_2312_ = lean_ctor_get(v___x_2307_, 4);
v_closeError_2313_ = lean_ctor_get(v___x_2307_, 5);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2307_, 3);
lean_dec(v_unused_2323_);
v___x_2315_ = v___x_2307_;
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_closeError_2313_);
lean_inc(v_pendingIncompleteChunk_2312_);
lean_inc(v_interestWaiter_2310_);
lean_inc(v_pendingConsumer_2309_);
lean_inc(v_pendingProducer_2308_);
lean_dec(v___x_2307_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 3, v_size_2304_);
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_pendingProducer_2308_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_pendingConsumer_2309_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_interestWaiter_2310_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_size_2304_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_pendingIncompleteChunk_2312_);
lean_ctor_set(v_reuseFailAlloc_2321_, 5, v_closeError_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2321_, sizeof(void*)*6, v_closed_2311_);
v___x_2318_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_st_ref_put(v___y_2305_, v___x_2318_);
v___x_2320_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(lean_object* v_size_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_2324_, v___y_2325_);
lean_dec(v___y_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize(lean_object* v_stream_2328_, lean_object* v_size_2329_){
_start:
{
lean_object* v___f_2331_; lean_object* v___x_2332_; lean_object* v___f_2333_; lean_object* v___f_2334_; lean_object* v___x_207__overap_2335_; lean_object* v___x_2336_; 
v___f_2331_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2331_, 0, v_size_2329_);
v___x_2332_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2333_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2334_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_207__overap_2335_ = l_Std_Mutex_atomically___redArg(v___x_2332_, v___f_2333_, v___f_2334_, v_stream_2328_, v___f_2331_);
v___x_2336_ = lean_apply_1(v___x_207__overap_2335_, lean_box(0));
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___boxed(lean_object* v_stream_2337_, lean_object* v_size_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_2337_, v_size_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object* v_pendingProducer_2341_, lean_object* v_pendingConsumer_2342_, uint8_t v_closed_2343_, lean_object* v_knownSize_2344_, lean_object* v_pendingIncompleteChunk_2345_, lean_object* v_closeError_2346_, lean_object* v_a_2347_, lean_object* v___x_2348_, lean_object* v_x_2349_){
_start:
{
if (lean_obj_tag(v_x_2349_) == 0)
{
lean_object* v___x_2351_; 
lean_dec(v_closeError_2346_);
lean_dec(v_pendingIncompleteChunk_2345_);
lean_dec(v_knownSize_2344_);
lean_dec(v_pendingConsumer_2342_);
lean_dec(v_pendingProducer_2341_);
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v_x_2349_);
return v___x_2351_;
}
else
{
lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2362_; 
v_isSharedCheck_2362_ = !lean_is_exclusive(v_x_2349_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v_x_2349_, 0);
lean_dec(v_unused_2363_);
v___x_2353_ = v_x_2349_;
v_isShared_2354_ = v_isSharedCheck_2362_;
goto v_resetjp_2352_;
}
else
{
lean_dec(v_x_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2362_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2356_, 0, v_pendingProducer_2341_);
lean_ctor_set(v___x_2356_, 1, v_pendingConsumer_2342_);
lean_ctor_set(v___x_2356_, 2, v___x_2355_);
lean_ctor_set(v___x_2356_, 3, v_knownSize_2344_);
lean_ctor_set(v___x_2356_, 4, v_pendingIncompleteChunk_2345_);
lean_ctor_set(v___x_2356_, 5, v_closeError_2346_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*6, v_closed_2343_);
v___x_2357_ = lean_st_ref_swap(v_a_2347_, v___x_2356_);
lean_dec(v___x_2357_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2348_);
v___x_2359_ = v___x_2353_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2348_);
v___x_2359_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object* v_pendingProducer_2364_, lean_object* v_pendingConsumer_2365_, lean_object* v_closed_2366_, lean_object* v_knownSize_2367_, lean_object* v_pendingIncompleteChunk_2368_, lean_object* v_closeError_2369_, lean_object* v_a_2370_, lean_object* v___x_2371_, lean_object* v_x_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v_closed_boxed_2374_; lean_object* v_res_2375_; 
v_closed_boxed_2374_ = lean_unbox(v_closed_2366_);
v_res_2375_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_2364_, v_pendingConsumer_2365_, v_closed_boxed_2374_, v_knownSize_2367_, v_pendingIncompleteChunk_2368_, v_closeError_2369_, v_a_2370_, v___x_2371_, v_x_2372_);
lean_dec(v_a_2370_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object* v_a_2376_, lean_object* v_x_2377_){
_start:
{
if (lean_obj_tag(v_x_2377_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2387_; 
v_a_2379_ = lean_ctor_get(v_x_2377_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_x_2377_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2381_ = v_x_2377_;
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v_x_2377_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v_interestWaiter_2389_; 
v_a_2388_ = lean_ctor_get(v_x_2377_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v_x_2377_, 1);
v_interestWaiter_2389_ = lean_ctor_get(v_a_2388_, 2);
lean_inc(v_interestWaiter_2389_);
if (lean_obj_tag(v_interestWaiter_2389_) == 1)
{
lean_object* v_pendingProducer_2390_; lean_object* v_pendingConsumer_2391_; uint8_t v_closed_2392_; lean_object* v_knownSize_2393_; lean_object* v_pendingIncompleteChunk_2394_; lean_object* v_closeError_2395_; lean_object* v_val_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___f_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_pendingProducer_2390_ = lean_ctor_get(v_a_2388_, 0);
lean_inc(v_pendingProducer_2390_);
v_pendingConsumer_2391_ = lean_ctor_get(v_a_2388_, 1);
lean_inc(v_pendingConsumer_2391_);
v_closed_2392_ = lean_ctor_get_uint8(v_a_2388_, sizeof(void*)*6);
v_knownSize_2393_ = lean_ctor_get(v_a_2388_, 3);
lean_inc(v_knownSize_2393_);
v_pendingIncompleteChunk_2394_ = lean_ctor_get(v_a_2388_, 4);
lean_inc(v_pendingIncompleteChunk_2394_);
v_closeError_2395_ = lean_ctor_get(v_a_2388_, 5);
lean_inc(v_closeError_2395_);
lean_dec(v_a_2388_);
v_val_2396_ = lean_ctor_get(v_interestWaiter_2389_, 0);
lean_inc(v_val_2396_);
lean_dec_ref_known(v_interestWaiter_2389_, 1);
v___x_2397_ = 1;
v___x_2398_ = lean_box(0);
v___x_2399_ = lean_box(v_closed_2392_);
lean_inc(v_a_2376_);
v___f_2400_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed), 10, 8);
lean_closure_set(v___f_2400_, 0, v_pendingProducer_2390_);
lean_closure_set(v___f_2400_, 1, v_pendingConsumer_2391_);
lean_closure_set(v___f_2400_, 2, v___x_2399_);
lean_closure_set(v___f_2400_, 3, v_knownSize_2393_);
lean_closure_set(v___f_2400_, 4, v_pendingIncompleteChunk_2394_);
lean_closure_set(v___f_2400_, 5, v_closeError_2395_);
lean_closure_set(v___f_2400_, 6, v_a_2376_);
lean_closure_set(v___f_2400_, 7, v___x_2398_);
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2402_ = 0;
v___x_2403_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2396_, v___x_2397_);
lean_dec(v_val_2396_);
v___x_2404_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2405_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2401_, v___x_2402_, v___x_2404_, v___f_2400_);
return v___x_2405_;
}
else
{
lean_object* v___x_2406_; 
lean_dec(v_interestWaiter_2389_);
lean_dec(v_a_2388_);
v___x_2406_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object* v_a_2407_, lean_object* v_x_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_2407_, v_x_2408_);
lean_dec(v_a_2407_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object* v_a_2411_){
_start:
{
lean_object* v___f_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_inc(v_a_2411_);
v___f_2413_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2413_, 0, v_a_2411_);
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = 0;
v___x_2416_ = lean_st_ref_get(v_a_2411_);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
v___x_2419_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2414_, v___x_2415_, v___x_2418_, v___f_2413_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object* v_a_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_2420_);
lean_dec(v_a_2420_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object* v_promise_2423_, lean_object* v_x_2424_){
_start:
{
if (lean_obj_tag(v_x_2424_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2434_; 
v_a_2426_ = lean_ctor_get(v_x_2424_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_x_2424_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2428_ = v_x_2424_;
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v_x_2424_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2432_; 
v___x_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2444_; 
v_a_2435_ = lean_ctor_get(v_x_2424_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_x_2424_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2437_ = v_x_2424_;
v_isShared_2438_ = v_isSharedCheck_2444_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v_x_2424_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2444_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2439_ = lean_io_promise_resolve(v_a_2435_, v_promise_2423_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2439_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_2445_, lean_object* v_x_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(v_promise_2445_, v_x_2446_);
lean_dec(v_promise_2445_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object* v_lose_2449_, lean_object* v___y_2450_, lean_object* v___f_2451_, lean_object* v_x_2452_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v___f_2451_);
lean_dec_ref(v_lose_2449_);
v_a_2454_ = lean_ctor_get(v_x_2452_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_x_2452_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2456_ = v_x_2452_;
v_isShared_2457_ = v_isSharedCheck_2462_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v_x_2452_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2462_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
}
}
else
{
lean_object* v_a_2463_; uint8_t v___x_2464_; 
v_a_2463_ = lean_ctor_get(v_x_2452_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v_x_2452_, 1);
v___x_2464_ = lean_unbox(v_a_2463_);
lean_dec(v_a_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; 
lean_dec_ref(v___f_2451_);
lean_inc(v___y_2450_);
v___x_2465_ = lean_apply_2(v_lose_2449_, v___y_2450_, lean_box(0));
return v___x_2465_;
}
else
{
lean_object* v___x_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_dec_ref(v_lose_2449_);
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = 0;
v___x_2468_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2450_);
v___x_2469_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2466_, v___x_2467_, v___x_2468_, v___f_2451_);
return v___x_2469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object* v_lose_2470_, lean_object* v___y_2471_, lean_object* v___f_2472_, lean_object* v_x_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(v_lose_2470_, v___y_2471_, v___f_2472_, v_x_2473_);
lean_dec(v___y_2471_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object* v_w_2476_, lean_object* v_lose_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_finished_2480_; lean_object* v_promise_2481_; lean_object* v___f_2482_; lean_object* v___f_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; uint8_t v___y_2488_; uint8_t v___x_2496_; 
v_finished_2480_ = lean_ctor_get(v_w_2476_, 0);
lean_inc(v_finished_2480_);
v_promise_2481_ = lean_ctor_get(v_w_2476_, 1);
lean_inc(v_promise_2481_);
lean_dec_ref(v_w_2476_);
v___f_2482_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2482_, 0, v_promise_2481_);
lean_inc(v___y_2478_);
v___f_2483_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2483_, 0, v_lose_2477_);
lean_closure_set(v___f_2483_, 1, v___y_2478_);
lean_closure_set(v___f_2483_, 2, v___f_2482_);
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = 0;
v___x_2486_ = lean_st_ref_take(v_finished_2480_);
v___x_2496_ = lean_unbox(v___x_2486_);
lean_dec(v___x_2486_);
if (v___x_2496_ == 0)
{
uint8_t v___x_2497_; 
v___x_2497_ = 1;
v___y_2488_ = v___x_2497_;
goto v___jp_2487_;
}
else
{
v___y_2488_ = v___x_2485_;
goto v___jp_2487_;
}
v___jp_2487_:
{
uint8_t v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2489_ = 1;
v___x_2490_ = lean_box(v___x_2489_);
v___x_2491_ = lean_st_ref_put(v_finished_2480_, v___x_2490_);
lean_dec(v_finished_2480_);
v___x_2492_ = lean_box(v___y_2488_);
v___x_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
v___x_2495_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2484_, v___x_2485_, v___x_2494_, v___f_2483_);
return v___x_2495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object* v_w_2498_, lean_object* v_lose_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_2498_, v_lose_2499_, v___y_2500_);
lean_dec(v___y_2500_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object* v___y_2503_, lean_object* v_x_2504_){
_start:
{
if (lean_obj_tag(v_x_2504_) == 0)
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_x_2504_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; 
lean_dec_ref_known(v_x_2504_, 1);
v___x_2507_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_2503_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object* v___y_2508_, lean_object* v_x_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_2508_, v_x_2509_);
lean_dec(v___y_2508_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object* v_waiter_2512_, lean_object* v_pendingProducer_2513_, lean_object* v_interestWaiter_2514_, uint8_t v_closed_2515_, lean_object* v_knownSize_2516_, lean_object* v_pendingIncompleteChunk_2517_, lean_object* v_closeError_2518_, uint8_t v_a_2519_, lean_object* v_____r_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___f_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_inc(v___y_2521_);
v___f_2523_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2523_, 0, v___y_2521_);
v___x_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_waiter_2512_);
v___x_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
v___x_2526_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2526_, 0, v_pendingProducer_2513_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
lean_ctor_set(v___x_2526_, 2, v_interestWaiter_2514_);
lean_ctor_set(v___x_2526_, 3, v_knownSize_2516_);
lean_ctor_set(v___x_2526_, 4, v_pendingIncompleteChunk_2517_);
lean_ctor_set(v___x_2526_, 5, v_closeError_2518_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*6, v_closed_2515_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v___x_2528_ = lean_st_ref_swap(v___y_2521_, v___x_2526_);
lean_dec(v___x_2528_);
v___x_2529_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2530_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2527_, v_a_2519_, v___x_2529_, v___f_2523_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object* v_waiter_2531_, lean_object* v_pendingProducer_2532_, lean_object* v_interestWaiter_2533_, lean_object* v_closed_2534_, lean_object* v_knownSize_2535_, lean_object* v_pendingIncompleteChunk_2536_, lean_object* v_closeError_2537_, lean_object* v_a_2538_, lean_object* v_____r_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
uint8_t v_closed_boxed_2542_; uint8_t v_a_5670__boxed_2543_; lean_object* v_res_2544_; 
v_closed_boxed_2542_ = lean_unbox(v_closed_2534_);
v_a_5670__boxed_2543_ = lean_unbox(v_a_2538_);
v_res_2544_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2531_, v_pendingProducer_2532_, v_interestWaiter_2533_, v_closed_boxed_2542_, v_knownSize_2535_, v_pendingIncompleteChunk_2536_, v_closeError_2537_, v_a_5670__boxed_2543_, v_____r_2539_, v___y_2540_);
lean_dec(v___y_2540_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object* v_waiter_2549_, uint8_t v_a_2550_, lean_object* v___y_2551_, lean_object* v_x_2552_){
_start:
{
if (lean_obj_tag(v_x_2552_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_waiter_2549_);
v_a_2554_ = lean_ctor_get(v_x_2552_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_x_2552_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2556_ = v_x_2552_;
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v_x_2552_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v_pendingProducer_2564_; lean_object* v_pendingConsumer_2565_; lean_object* v_interestWaiter_2566_; uint8_t v_closed_2567_; lean_object* v_knownSize_2568_; lean_object* v_pendingIncompleteChunk_2569_; lean_object* v_closeError_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___f_2573_; 
v_a_2563_ = lean_ctor_get(v_x_2552_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v_x_2552_, 1);
v_pendingProducer_2564_ = lean_ctor_get(v_a_2563_, 0);
lean_inc_n(v_pendingProducer_2564_, 2);
v_pendingConsumer_2565_ = lean_ctor_get(v_a_2563_, 1);
lean_inc(v_pendingConsumer_2565_);
v_interestWaiter_2566_ = lean_ctor_get(v_a_2563_, 2);
lean_inc_n(v_interestWaiter_2566_, 2);
v_closed_2567_ = lean_ctor_get_uint8(v_a_2563_, sizeof(void*)*6);
v_knownSize_2568_ = lean_ctor_get(v_a_2563_, 3);
lean_inc_n(v_knownSize_2568_, 2);
v_pendingIncompleteChunk_2569_ = lean_ctor_get(v_a_2563_, 4);
lean_inc_n(v_pendingIncompleteChunk_2569_, 2);
v_closeError_2570_ = lean_ctor_get(v_a_2563_, 5);
lean_inc_n(v_closeError_2570_, 2);
lean_dec(v_a_2563_);
v___x_2571_ = lean_box(v_closed_2567_);
v___x_2572_ = lean_box(v_a_2550_);
lean_inc_ref(v_waiter_2549_);
v___f_2573_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__0___boxed), 11, 8);
lean_closure_set(v___f_2573_, 0, v_waiter_2549_);
lean_closure_set(v___f_2573_, 1, v_pendingProducer_2564_);
lean_closure_set(v___f_2573_, 2, v_interestWaiter_2566_);
lean_closure_set(v___f_2573_, 3, v___x_2571_);
lean_closure_set(v___f_2573_, 4, v_knownSize_2568_);
lean_closure_set(v___f_2573_, 5, v_pendingIncompleteChunk_2569_);
lean_closure_set(v___f_2573_, 6, v_closeError_2570_);
lean_closure_set(v___f_2573_, 7, v___x_2572_);
if (lean_obj_tag(v_pendingConsumer_2565_) == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec_ref(v___f_2573_);
v___x_2574_ = lean_box(0);
v___x_2575_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2549_, v_pendingProducer_2564_, v_interestWaiter_2566_, v_closed_2567_, v_knownSize_2568_, v_pendingIncompleteChunk_2569_, v_closeError_2570_, v_a_2550_, v___x_2574_, v___y_2551_);
return v___x_2575_;
}
else
{
lean_object* v___f_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec_ref_known(v_pendingConsumer_2565_, 1);
lean_dec(v_closeError_2570_);
lean_dec(v_pendingIncompleteChunk_2569_);
lean_dec(v_knownSize_2568_);
lean_dec(v_interestWaiter_2566_);
lean_dec(v_pendingProducer_2564_);
lean_dec_ref(v_waiter_2549_);
lean_inc(v___y_2551_);
v___f_2576_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2576_, 0, v___f_2573_);
lean_closure_set(v___f_2576_, 1, v___y_2551_);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1));
v___x_2579_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2577_, v_a_2550_, v___x_2578_, v___f_2576_);
return v___x_2579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object* v_waiter_2580_, lean_object* v_a_2581_, lean_object* v___y_2582_, lean_object* v_x_2583_, lean_object* v___y_2584_){
_start:
{
uint8_t v_a_5711__boxed_2585_; lean_object* v_res_2586_; 
v_a_5711__boxed_2585_ = lean_unbox(v_a_2581_);
v_res_2586_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v_waiter_2580_, v_a_5711__boxed_2585_, v___y_2582_, v_x_2583_);
lean_dec(v___y_2582_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object* v___x_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2587_);
v___x_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object* v___x_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_2592_, v___y_2593_);
lean_dec(v___y_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object* v_waiter_2598_, lean_object* v___y_2599_, lean_object* v_x_2600_){
_start:
{
if (lean_obj_tag(v_x_2600_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2610_; 
lean_dec_ref(v_waiter_2598_);
v_a_2602_ = lean_ctor_get(v_x_2600_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_x_2600_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2604_ = v_x_2600_;
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v_x_2600_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; 
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
return v___x_2608_;
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2627_; 
v_a_2611_ = lean_ctor_get(v_x_2600_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_x_2600_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2613_ = v_x_2600_;
v_isShared_2614_ = v_isSharedCheck_2627_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v_x_2600_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2627_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_unbox(v_a_2611_);
if (v___x_2615_ == 0)
{
lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2620_; 
lean_inc(v___y_2599_);
lean_inc(v_a_2611_);
v___f_2616_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2616_, 0, v_waiter_2598_);
lean_closure_set(v___f_2616_, 1, v_a_2611_);
lean_closure_set(v___f_2616_, 2, v___y_2599_);
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2618_ = lean_st_ref_get(v___y_2599_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2618_);
v___x_2620_ = v___x_2613_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
v___x_2622_ = lean_unbox(v_a_2611_);
lean_dec(v_a_2611_);
v___x_2623_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2617_, v___x_2622_, v___x_2621_, v___f_2616_);
return v___x_2623_;
}
}
else
{
lean_object* v___f_2625_; lean_object* v___x_2626_; 
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
v___f_2625_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_2626_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_waiter_2598_, v___f_2625_, v___y_2599_);
return v___x_2626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object* v_waiter_2628_, lean_object* v___y_2629_, lean_object* v_x_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v_waiter_2628_, v___y_2629_, v_x_2630_);
lean_dec(v___y_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object* v___y_2633_, lean_object* v___f_2634_, lean_object* v_x_2635_){
_start:
{
if (lean_obj_tag(v_x_2635_) == 0)
{
lean_object* v___x_2637_; 
lean_dec_ref(v___f_2634_);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_x_2635_);
return v___x_2637_;
}
else
{
lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec_ref_known(v_x_2635_, 1);
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = 0;
v___x_2640_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_2633_);
v___x_2641_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2638_, v___x_2639_, v___x_2640_, v___f_2634_);
return v___x_2641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object* v___y_2642_, lean_object* v___f_2643_, lean_object* v_x_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_2642_, v___f_2643_, v_x_2644_);
lean_dec(v___y_2642_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object* v_waiter_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___f_2650_; lean_object* v___f_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_inc_n(v___y_2648_, 2);
v___f_2650_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__4___boxed), 4, 2);
lean_closure_set(v___f_2650_, 0, v_waiter_2647_);
lean_closure_set(v___f_2650_, 1, v___y_2648_);
v___f_2651_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2651_, 0, v___y_2648_);
lean_closure_set(v___f_2651_, 1, v___f_2650_);
v___x_2652_ = lean_unsigned_to_nat(0u);
v___x_2653_ = 0;
v___x_2654_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2648_);
v___x_2655_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2652_, v___x_2653_, v___x_2654_, v___f_2651_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object* v_waiter_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_2656_, v___y_2657_);
lean_dec(v___y_2657_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object* v_stream_2660_, lean_object* v_waiter_2661_){
_start:
{
lean_object* v___f_2663_; lean_object* v___x_2664_; 
v___f_2663_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2663_, 0, v_waiter_2661_);
v___x_2664_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2660_, v___f_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object* v_stream_2665_, lean_object* v_waiter_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_2665_, v_waiter_2666_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object* v_stream_2670_){
_start:
{
lean_object* v___f_2671_; lean_object* v___f_2672_; lean_object* v___f_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___f_2671_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_2670_, 2);
v___f_2672_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2672_, 0, v_stream_2670_);
v___f_2673_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_2674_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2674_, 0, lean_box(0));
lean_closure_set(v___x_2674_, 1, lean_box(0));
lean_closure_set(v___x_2674_, 2, v_stream_2670_);
lean_closure_set(v___x_2674_, 3, v___f_2673_);
v___x_2675_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2675_, 0, lean_box(0));
lean_closure_set(v___x_2675_, 1, lean_box(0));
lean_closure_set(v___x_2675_, 2, v_stream_2670_);
lean_closure_set(v___x_2675_, 3, v___f_2671_);
v___x_2676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___f_2672_);
lean_ctor_set(v___x_2676_, 2, v___x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0(lean_object* v_step_2677_, lean_object* v_acc_2678_, lean_object* v_x_2679_){
_start:
{
if (lean_obj_tag(v_x_2679_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_acc_2678_);
lean_dec_ref(v_step_2677_);
v_a_2681_ = lean_ctor_get(v_x_2679_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_x_2679_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2683_ = v_x_2679_;
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v_x_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
return v___x_2687_;
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2701_; 
v_a_2690_ = lean_ctor_get(v_x_2679_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_x_2679_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2692_ = v_x_2679_;
v_isShared_2693_ = v_isSharedCheck_2701_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v_x_2679_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2701_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
if (lean_obj_tag(v_a_2690_) == 1)
{
lean_object* v_val_2694_; lean_object* v___x_2695_; 
lean_del_object(v___x_2692_);
v_val_2694_ = lean_ctor_get(v_a_2690_, 0);
lean_inc(v_val_2694_);
lean_dec_ref_known(v_a_2690_, 1);
v___x_2695_ = lean_apply_3(v_step_2677_, v_val_2694_, v_acc_2678_, lean_box(0));
return v___x_2695_;
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
lean_dec(v_a_2690_);
lean_dec_ref(v_step_2677_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_acc_2678_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2696_);
v___x_2698_ = v___x_2692_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
return v___x_2699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed(lean_object* v_step_2702_, lean_object* v_acc_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Std_Http_Body_Stream_forIn___redArg___lam__0(v_step_2702_, v_acc_2703_, v_x_2704_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1(lean_object* v_step_2707_, lean_object* v_stream_2708_, lean_object* v_x_2709_, lean_object* v_acc_2710_){
_start:
{
lean_object* v___f_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___f_2712_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2712_, 0, v_step_2707_);
lean_closure_set(v___f_2712_, 1, v_acc_2710_);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = 0;
v___x_2715_ = l_Std_Http_Body_Stream_recv(v_stream_2708_);
v___x_2716_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2713_, v___x_2714_, v___x_2715_, v___f_2712_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed(lean_object* v_step_2717_, lean_object* v_stream_2718_, lean_object* v_x_2719_, lean_object* v_acc_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Std_Http_Body_Stream_forIn___redArg___lam__1(v_step_2717_, v_stream_2718_, v_x_2719_, v_acc_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2(lean_object* v_a_2723_, lean_object* v_x_2724_){
_start:
{
if (lean_obj_tag(v_x_2724_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2734_; 
v_a_2726_ = lean_ctor_get(v_x_2724_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_x_2724_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2728_ = v_x_2724_;
v_isShared_2729_ = v_isSharedCheck_2734_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v_x_2724_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2734_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
return v___x_2732_;
}
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec_ref_known(v_x_2724_, 1);
v___x_2735_ = l_IO_Promise_result_x21___redArg(v_a_2723_);
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed(lean_object* v_a_2737_, lean_object* v_x_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Std_Http_Body_Stream_forIn___redArg___lam__2(v_a_2737_, v_x_2738_);
lean_dec(v_a_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3(lean_object* v___f_2741_, lean_object* v___x_2742_, lean_object* v_acc_2743_, lean_object* v_x_2744_){
_start:
{
if (lean_obj_tag(v_x_2744_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_acc_2743_);
lean_dec(v___x_2742_);
lean_dec_ref(v___f_2741_);
v_a_2746_ = lean_ctor_get(v_x_2744_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_x_2744_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2748_ = v_x_2744_;
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v_x_2744_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2767_; 
v_a_2755_ = lean_ctor_get(v_x_2744_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_x_2744_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2757_ = v_x_2744_;
v_isShared_2758_ = v_isSharedCheck_2767_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v_x_2744_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2767_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___f_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
lean_inc(v_a_2755_);
v___f_2759_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2759_, 0, v_a_2755_);
v___x_2760_ = 0;
lean_inc(v___x_2742_);
v___x_2761_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_2741_, v___x_2742_, v_a_2755_, v_acc_2743_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2761_);
v___x_2763_ = v___x_2757_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
v___x_2765_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2742_, v___x_2760_, v___x_2764_, v___f_2759_);
return v___x_2765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed(lean_object* v___f_2768_, lean_object* v___x_2769_, lean_object* v_acc_2770_, lean_object* v_x_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Std_Http_Body_Stream_forIn___redArg___lam__3(v___f_2768_, v___x_2769_, v_acc_2770_, v_x_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_2774_, lean_object* v_acc_2775_, lean_object* v_step_2776_){
_start:
{
lean_object* v___f_2778_; lean_object* v___x_2779_; lean_object* v___f_2780_; uint8_t v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___f_2778_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2778_, 0, v_step_2776_);
lean_closure_set(v___f_2778_, 1, v_stream_2774_);
v___x_2779_ = lean_unsigned_to_nat(0u);
v___f_2780_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2780_, 0, v___f_2778_);
lean_closure_set(v___f_2780_, 1, v___x_2779_);
lean_closure_set(v___f_2780_, 2, v_acc_2775_);
v___x_2781_ = 0;
v___x_2782_ = lean_io_promise_new();
v___x_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
v___x_2785_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2779_, v___x_2781_, v___x_2784_, v___f_2780_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_2786_, lean_object* v_acc_2787_, lean_object* v_step_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_2786_, v_acc_2787_, v_step_2788_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_2791_, lean_object* v_stream_2792_, lean_object* v_acc_2793_, lean_object* v_step_2794_){
_start:
{
lean_object* v___f_2796_; lean_object* v___x_2797_; lean_object* v___f_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___f_2796_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2796_, 0, v_step_2794_);
lean_closure_set(v___f_2796_, 1, v_stream_2792_);
v___x_2797_ = lean_unsigned_to_nat(0u);
v___f_2798_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2798_, 0, v___f_2796_);
lean_closure_set(v___f_2798_, 1, v___x_2797_);
lean_closure_set(v___f_2798_, 2, v_acc_2793_);
v___x_2799_ = 0;
v___x_2800_ = lean_io_promise_new();
v___x_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
v___x_2803_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2797_, v___x_2799_, v___x_2802_, v___f_2798_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_2804_, lean_object* v_stream_2805_, lean_object* v_acc_2806_, lean_object* v_step_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_2804_, v_stream_2805_, v_acc_2806_, v_step_2807_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___y_2810_);
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0___boxed(lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(v___y_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(lean_object* v_x_2817_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1___boxed(lean_object* v_x_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(v_x_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(lean_object* v_x_2823_){
_start:
{
if (lean_obj_tag(v_x_2823_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2833_; 
v_a_2825_ = lean_ctor_get(v_x_2823_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_x_2823_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2827_ = v_x_2823_;
v_isShared_2828_ = v_isSharedCheck_2833_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v_x_2823_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2833_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; 
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
return v___x_2831_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2844_; 
v_a_2834_ = lean_ctor_get(v_x_2823_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_x_2823_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2836_ = v_x_2823_;
v_isShared_2837_ = v_isSharedCheck_2844_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v_x_2823_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2844_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v_token_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v_token_2838_ = lean_ctor_get(v_a_2834_, 1);
lean_inc_ref(v_token_2838_);
lean_dec(v_a_2834_);
v___x_2839_ = l_Std_CancellationToken_selector(v_token_2838_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2839_);
v___x_2841_ = v___x_2836_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
return v___x_2842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2___boxed(lean_object* v_x_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(v_x_2845_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(lean_object* v_step_2848_, lean_object* v_b_2849_, lean_object* v_a_2850_, lean_object* v_x_2851_){
_start:
{
if (lean_obj_tag(v_x_2851_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v_b_2849_);
lean_dec_ref(v_step_2848_);
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
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2873_; 
v_a_2862_ = lean_ctor_get(v_x_2851_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2864_ = v_x_2851_;
v_isShared_2865_ = v_isSharedCheck_2873_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v_x_2851_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2873_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
if (lean_obj_tag(v_a_2862_) == 1)
{
lean_object* v_val_2866_; lean_object* v___x_2867_; 
lean_del_object(v___x_2864_);
v_val_2866_ = lean_ctor_get(v_a_2862_, 0);
lean_inc(v_val_2866_);
lean_dec_ref_known(v_a_2862_, 1);
lean_inc_ref(v_a_2850_);
v___x_2867_ = lean_apply_4(v_step_2848_, v_val_2866_, v_b_2849_, v_a_2850_, lean_box(0));
return v___x_2867_;
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
lean_dec(v_a_2862_);
lean_dec_ref(v_step_2848_);
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_b_2849_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2868_);
v___x_2870_ = v___x_2864_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; 
v___x_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
return v___x_2871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed(lean_object* v_step_2874_, lean_object* v_b_2875_, lean_object* v_a_2876_, lean_object* v_x_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(v_step_2874_, v_b_2875_, v_a_2876_, v_x_2877_);
lean_dec_ref(v_a_2876_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(lean_object* v_stream_2880_, lean_object* v___f_2881_, lean_object* v___f_2882_, lean_object* v___f_2883_, lean_object* v_x_2884_){
_start:
{
if (lean_obj_tag(v_x_2884_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v___f_2883_);
lean_dec_ref(v___f_2882_);
lean_dec_ref(v___f_2881_);
lean_dec_ref(v_stream_2880_);
v_a_2886_ = lean_ctor_get(v_x_2884_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_x_2884_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2888_ = v_x_2884_;
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v_x_2884_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; 
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
return v___x_2892_;
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_a_2895_ = lean_ctor_get(v_x_2884_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v_x_2884_, 1);
v___x_2896_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2880_);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___f_2881_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v_a_2895_);
lean_ctor_set(v___x_2898_, 1, v___f_2882_);
v___x_2899_ = lean_unsigned_to_nat(2u);
v___x_2900_ = lean_mk_empty_array_with_capacity(v___x_2899_);
v___x_2901_ = lean_array_push(v___x_2900_, v___x_2897_);
v___x_2902_ = lean_array_push(v___x_2901_, v___x_2898_);
v___x_2903_ = lean_unsigned_to_nat(0u);
v___x_2904_ = 0;
v___x_2905_ = l_Std_Async_Selectable_one___redArg(v___x_2902_);
v___x_2906_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2903_, v___x_2904_, v___x_2905_, v___f_2883_);
return v___x_2906_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed(lean_object* v_stream_2907_, lean_object* v___f_2908_, lean_object* v___f_2909_, lean_object* v___f_2910_, lean_object* v_x_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(v_stream_2907_, v___f_2908_, v___f_2909_, v___f_2910_, v_x_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(lean_object* v_step_2914_, lean_object* v_a_2915_, lean_object* v_stream_2916_, lean_object* v___f_2917_, lean_object* v___f_2918_, lean_object* v___f_2919_, lean_object* v_u_2920_, lean_object* v_b_2921_){
_start:
{
lean_object* v___f_2923_; lean_object* v___f_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_inc_ref_n(v_a_2915_, 2);
v___f_2923_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2923_, 0, v_step_2914_);
lean_closure_set(v___f_2923_, 1, v_b_2921_);
lean_closure_set(v___f_2923_, 2, v_a_2915_);
v___f_2924_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_2924_, 0, v_stream_2916_);
lean_closure_set(v___f_2924_, 1, v___f_2917_);
lean_closure_set(v___f_2924_, 2, v___f_2918_);
lean_closure_set(v___f_2924_, 3, v___f_2923_);
v___x_2925_ = lean_unsigned_to_nat(0u);
v___x_2926_ = 0;
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v_a_2915_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
v___x_2929_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2925_, v___x_2926_, v___x_2928_, v___f_2919_);
v___x_2930_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2925_, v___x_2926_, v___x_2929_, v___f_2924_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed(lean_object* v_step_2931_, lean_object* v_a_2932_, lean_object* v_stream_2933_, lean_object* v___f_2934_, lean_object* v___f_2935_, lean_object* v___f_2936_, lean_object* v_u_2937_, lean_object* v_b_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(v_step_2931_, v_a_2932_, v_stream_2933_, v___f_2934_, v___f_2935_, v___f_2936_, v_u_2937_, v_b_2938_);
lean_dec_ref(v_a_2932_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_2944_, lean_object* v_acc_2945_, lean_object* v_step_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v___f_2949_; lean_object* v___f_2950_; lean_object* v___f_2951_; lean_object* v___f_2952_; lean_object* v___x_2953_; lean_object* v___f_2954_; uint8_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___f_2949_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_2950_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_2951_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_2947_);
v___f_2952_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_2952_, 0, v_step_2946_);
lean_closure_set(v___f_2952_, 1, v_a_2947_);
lean_closure_set(v___f_2952_, 2, v_stream_2944_);
lean_closure_set(v___f_2952_, 3, v___f_2949_);
lean_closure_set(v___f_2952_, 4, v___f_2950_);
lean_closure_set(v___f_2952_, 5, v___f_2951_);
v___x_2953_ = lean_unsigned_to_nat(0u);
v___f_2954_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2954_, 0, v___f_2952_);
lean_closure_set(v___f_2954_, 1, v___x_2953_);
lean_closure_set(v___f_2954_, 2, v_acc_2945_);
v___x_2955_ = 0;
v___x_2956_ = lean_io_promise_new();
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
v___x_2959_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2953_, v___x_2955_, v___x_2958_, v___f_2954_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_2960_, lean_object* v_acc_2961_, lean_object* v_step_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_2960_, v_acc_2961_, v_step_2962_, v_a_2963_);
lean_dec_ref(v_a_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_2966_, lean_object* v_stream_2967_, lean_object* v_acc_2968_, lean_object* v_step_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___f_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___f_2977_; uint8_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___f_2972_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_2973_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_2974_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_2970_);
v___f_2975_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_2975_, 0, v_step_2969_);
lean_closure_set(v___f_2975_, 1, v_a_2970_);
lean_closure_set(v___f_2975_, 2, v_stream_2967_);
lean_closure_set(v___f_2975_, 3, v___f_2972_);
lean_closure_set(v___f_2975_, 4, v___f_2973_);
lean_closure_set(v___f_2975_, 5, v___f_2974_);
v___x_2976_ = lean_unsigned_to_nat(0u);
v___f_2977_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2977_, 0, v___f_2975_);
lean_closure_set(v___f_2977_, 1, v___x_2976_);
lean_closure_set(v___f_2977_, 2, v_acc_2968_);
v___x_2978_ = 0;
v___x_2979_ = lean_io_promise_new();
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
v___x_2982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2976_, v___x_2978_, v___x_2981_, v___f_2977_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_2983_, lean_object* v_stream_2984_, lean_object* v_acc_2985_, lean_object* v_step_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_2983_, v_stream_2984_, v_acc_2985_, v_step_2986_, v_a_2987_);
lean_dec_ref(v_a_2987_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v_stream_2992_, lean_object* v___f_2993_, lean_object* v___f_2994_, lean_object* v_x_2995_){
_start:
{
if (lean_obj_tag(v_x_2995_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v___f_2994_);
lean_dec_ref(v___f_2993_);
lean_dec_ref(v_stream_2992_);
v_a_2997_ = lean_ctor_get(v_x_2995_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_x_2995_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2999_ = v_x_2995_;
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v_x_2995_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_a_3006_ = lean_ctor_get(v_x_2995_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v_x_2995_, 1);
v___x_3007_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2992_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v___f_2993_);
v___x_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3009_, 0, v_a_3006_);
lean_ctor_set(v___x_3009_, 1, v___f_2994_);
v___x_3010_ = lean_unsigned_to_nat(2u);
v___x_3011_ = lean_mk_empty_array_with_capacity(v___x_3010_);
v___x_3012_ = lean_array_push(v___x_3011_, v___x_3008_);
v___x_3013_ = lean_array_push(v___x_3012_, v___x_3009_);
v___x_3014_ = l_Std_Async_Selectable_one___redArg(v___x_3013_);
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v_stream_3015_, lean_object* v___f_3016_, lean_object* v___f_3017_, lean_object* v_x_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_3015_, v___f_3016_, v___f_3017_, v_x_3018_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v___f_3021_, lean_object* v___f_3022_, lean_object* v___f_3023_, lean_object* v_stream_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___f_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___f_3027_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3027_, 0, v_stream_3024_);
lean_closure_set(v___f_3027_, 1, v___f_3021_);
lean_closure_set(v___f_3027_, 2, v___f_3022_);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = 0;
lean_inc_ref(v___y_3025_);
v___x_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___y_3025_);
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
v___x_3032_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3028_, v___x_3029_, v___x_3031_, v___f_3023_);
v___x_3033_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3028_, v___x_3029_, v___x_3032_, v___f_3027_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v___f_3034_, lean_object* v___f_3035_, lean_object* v___f_3036_, lean_object* v_stream_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v___f_3034_, v___f_3035_, v___f_3036_, v_stream_3037_, v___y_3038_);
lean_dec_ref(v___y_3038_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v_toPure_3048_, lean_object* v_result_3049_, lean_object* v_maximumSize_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_stream_3054_, lean_object* v_toBind_3055_, lean_object* v_____do__lift_3056_){
_start:
{
if (lean_obj_tag(v_____do__lift_3056_) == 0)
{
lean_object* v___x_3057_; 
lean_dec(v_toBind_3055_);
lean_dec_ref(v_stream_3054_);
lean_dec(v_inst_3053_);
lean_dec_ref(v_inst_3052_);
lean_dec_ref(v_inst_3051_);
lean_dec(v_maximumSize_3050_);
v___x_3057_ = lean_apply_2(v_toPure_3048_, lean_box(0), v_result_3049_);
return v___x_3057_;
}
else
{
lean_object* v_val_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_toPure_3048_);
v_val_3058_ = lean_ctor_get(v_____do__lift_3056_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_____do__lift_3056_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3060_ = v_____do__lift_3056_;
v_isShared_3061_ = v_isSharedCheck_3089_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_val_3058_);
lean_dec(v_____do__lift_3056_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3089_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v_data_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; lean_object* v_result_3067_; 
v_data_3062_ = lean_ctor_get(v_val_3058_, 0);
lean_inc_ref(v_data_3062_);
lean_dec(v_val_3058_);
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = lean_byte_array_size(v_result_3049_);
v___x_3065_ = lean_byte_array_size(v_data_3062_);
v___x_3066_ = 0;
v_result_3067_ = lean_byte_array_copy_slice(v_data_3062_, v___x_3063_, v_result_3049_, v___x_3064_, v___x_3065_, v___x_3066_);
lean_dec_ref(v_data_3062_);
if (lean_obj_tag(v_maximumSize_3050_) == 1)
{
lean_object* v_val_3068_; lean_object* v___x_3069_; uint64_t v___x_3070_; uint64_t v___x_3071_; uint8_t v___x_3072_; 
v_val_3068_ = lean_ctor_get(v_maximumSize_3050_, 0);
v___x_3069_ = lean_byte_array_size(v_result_3067_);
v___x_3070_ = lean_uint64_of_nat(v___x_3069_);
v___x_3071_ = lean_unbox_uint64(v_val_3068_);
v___x_3072_ = lean_uint64_dec_lt(v___x_3071_, v___x_3070_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; 
lean_del_object(v___x_3060_);
lean_dec(v_toBind_3055_);
v___x_3073_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3051_, v_inst_3052_, v_inst_3053_, v_stream_3054_, v_maximumSize_3050_, v_result_3067_);
return v___x_3073_;
}
else
{
lean_object* v_throw_3074_; lean_object* v___f_3075_; lean_object* v___x_3076_; uint64_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3084_; 
lean_inc(v_val_3068_);
v_throw_3074_ = lean_ctor_get(v_inst_3052_, 0);
lean_inc(v_throw_3074_);
v___f_3075_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0), 7, 6);
lean_closure_set(v___f_3075_, 0, v_inst_3051_);
lean_closure_set(v___f_3075_, 1, v_inst_3052_);
lean_closure_set(v___f_3075_, 2, v_inst_3053_);
lean_closure_set(v___f_3075_, 3, v_stream_3054_);
lean_closure_set(v___f_3075_, 4, v_maximumSize_3050_);
lean_closure_set(v___f_3075_, 5, v_result_3067_);
v___x_3076_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0));
v___x_3077_ = lean_unbox_uint64(v_val_3068_);
lean_dec(v_val_3068_);
v___x_3078_ = lean_uint64_to_nat(v___x_3077_);
v___x_3079_ = l_Nat_reprFast(v___x_3078_);
v___x_3080_ = lean_string_append(v___x_3076_, v___x_3079_);
lean_dec_ref(v___x_3079_);
v___x_3081_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1));
v___x_3082_ = lean_string_append(v___x_3080_, v___x_3081_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set_tag(v___x_3060_, 18);
lean_ctor_set(v___x_3060_, 0, v___x_3082_);
v___x_3084_ = v___x_3060_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = lean_apply_2(v_throw_3074_, lean_box(0), v___x_3084_);
v___x_3086_ = lean_apply_4(v_toBind_3055_, lean_box(0), lean_box(0), v___x_3085_, v___f_3075_);
return v___x_3086_;
}
}
}
else
{
lean_object* v___x_3088_; 
lean_del_object(v___x_3060_);
lean_dec(v_toBind_3055_);
v___x_3088_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3051_, v_inst_3052_, v_inst_3053_, v_stream_3054_, v_maximumSize_3050_, v_result_3067_);
return v___x_3088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_3090_, lean_object* v_inst_3091_, lean_object* v_inst_3092_, lean_object* v_stream_3093_, lean_object* v_maximumSize_3094_, lean_object* v_result_3095_){
_start:
{
lean_object* v_toApplicative_3096_; lean_object* v_toBind_3097_; lean_object* v_toPure_3098_; lean_object* v___x_3099_; lean_object* v___f_3100_; lean_object* v___x_3101_; 
v_toApplicative_3096_ = lean_ctor_get(v_inst_3090_, 0);
v_toBind_3097_ = lean_ctor_get(v_inst_3090_, 1);
lean_inc_n(v_toBind_3097_, 2);
v_toPure_3098_ = lean_ctor_get(v_toApplicative_3096_, 1);
lean_inc(v_toPure_3098_);
lean_inc(v_inst_3092_);
lean_inc_ref(v_stream_3093_);
v___x_3099_ = lean_apply_1(v_inst_3092_, v_stream_3093_);
v___f_3100_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 9, 8);
lean_closure_set(v___f_3100_, 0, v_toPure_3098_);
lean_closure_set(v___f_3100_, 1, v_result_3095_);
lean_closure_set(v___f_3100_, 2, v_maximumSize_3094_);
lean_closure_set(v___f_3100_, 3, v_inst_3090_);
lean_closure_set(v___f_3100_, 4, v_inst_3091_);
lean_closure_set(v___f_3100_, 5, v_inst_3092_);
lean_closure_set(v___f_3100_, 6, v_stream_3093_);
lean_closure_set(v___f_3100_, 7, v_toBind_3097_);
v___x_3101_ = lean_apply_4(v_toBind_3097_, lean_box(0), lean_box(0), v___x_3099_, v___f_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_inst_3104_, lean_object* v_stream_3105_, lean_object* v_maximumSize_3106_, lean_object* v_result_3107_, lean_object* v_____r_3108_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3102_, v_inst_3103_, v_inst_3104_, v_stream_3105_, v_maximumSize_3106_, v_result_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_3110_, lean_object* v_inst_3111_, lean_object* v_inst_3112_, lean_object* v_inst_3113_, lean_object* v_stream_3114_, lean_object* v_maximumSize_3115_, lean_object* v_result_3116_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3111_, v_inst_3112_, v_inst_3113_, v_stream_3114_, v_maximumSize_3115_, v_result_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_toPure_3120_, lean_object* v_result_3121_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_apply_1(v_inst_3118_, v_result_3121_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3132_; 
lean_dec(v_toPure_3120_);
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3132_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3132_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v_throw_3127_; lean_object* v___x_3129_; 
v_throw_3127_ = lean_ctor_get(v_inst_3119_, 0);
lean_inc(v_throw_3127_);
lean_dec_ref(v_inst_3119_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set_tag(v___x_3125_, 18);
v___x_3129_ = v___x_3125_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3123_);
v___x_3129_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_apply_2(v_throw_3127_, lean_box(0), v___x_3129_);
return v___x_3130_;
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3134_; 
lean_dec_ref(v_inst_3119_);
v_a_3133_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3122_, 1);
v___x_3134_ = lean_apply_2(v_toPure_3120_, lean_box(0), v_a_3133_);
return v___x_3134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_3135_, lean_object* v_inst_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_stream_3139_, lean_object* v_maximumSize_3140_){
_start:
{
lean_object* v_toApplicative_3141_; lean_object* v_toBind_3142_; lean_object* v_toPure_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___f_3146_; lean_object* v___x_3147_; 
v_toApplicative_3141_ = lean_ctor_get(v_inst_3136_, 0);
v_toBind_3142_ = lean_ctor_get(v_inst_3136_, 1);
lean_inc(v_toBind_3142_);
v_toPure_3143_ = lean_ctor_get(v_toApplicative_3141_, 1);
lean_inc(v_toPure_3143_);
v___x_3144_ = l_ByteArray_empty;
lean_inc_ref(v_inst_3137_);
v___x_3145_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3136_, v_inst_3137_, v_inst_3138_, v_stream_3139_, v_maximumSize_3140_, v___x_3144_);
v___f_3146_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3146_, 0, v_inst_3135_);
lean_closure_set(v___f_3146_, 1, v_inst_3137_);
lean_closure_set(v___f_3146_, 2, v_toPure_3143_);
v___x_3147_ = lean_apply_4(v_toBind_3142_, lean_box(0), lean_box(0), v___x_3145_, v___f_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_3148_, lean_object* v_m_3149_, lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_stream_3154_, lean_object* v_maximumSize_3155_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_3150_, v_inst_3151_, v_inst_3152_, v_inst_3153_, v_stream_3154_, v_maximumSize_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0(lean_object* v_toPure_3157_, lean_object* v_____r_3158_){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_box(0);
v___x_3160_ = lean_apply_2(v_toPure_3157_, lean_box(0), v___x_3159_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(lean_object* v_toPure_3161_, uint64_t v_consumed_3162_, lean_object* v_drainLimit_3163_, lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_stream_3166_, lean_object* v_closeStream_3167_, lean_object* v_toBind_3168_, lean_object* v___f_3169_, lean_object* v_____do__lift_3170_){
_start:
{
if (lean_obj_tag(v_____do__lift_3170_) == 0)
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_dec(v___f_3169_);
lean_dec(v_toBind_3168_);
lean_dec(v_closeStream_3167_);
lean_dec_ref(v_stream_3166_);
lean_dec(v_inst_3165_);
lean_dec_ref(v_inst_3164_);
lean_dec(v_drainLimit_3163_);
v___x_3171_ = lean_box(0);
v___x_3172_ = lean_apply_2(v_toPure_3161_, lean_box(0), v___x_3171_);
return v___x_3172_;
}
else
{
lean_object* v_val_3173_; lean_object* v_data_3174_; lean_object* v___x_3175_; uint64_t v___x_3176_; uint64_t v_consumed_3177_; 
lean_dec(v_toPure_3161_);
v_val_3173_ = lean_ctor_get(v_____do__lift_3170_, 0);
v_data_3174_ = lean_ctor_get(v_val_3173_, 0);
v___x_3175_ = lean_byte_array_size(v_data_3174_);
v___x_3176_ = lean_uint64_of_nat(v___x_3175_);
v_consumed_3177_ = lean_uint64_add(v_consumed_3162_, v___x_3176_);
if (lean_obj_tag(v_drainLimit_3163_) == 1)
{
lean_object* v_val_3178_; uint64_t v___x_3179_; uint8_t v___x_3180_; 
v_val_3178_ = lean_ctor_get(v_drainLimit_3163_, 0);
v___x_3179_ = lean_unbox_uint64(v_val_3178_);
v___x_3180_ = lean_uint64_dec_lt(v___x_3179_, v_consumed_3177_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
lean_dec(v___f_3169_);
lean_dec(v_toBind_3168_);
v___x_3181_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3164_, v_inst_3165_, v_stream_3166_, v_drainLimit_3163_, v_closeStream_3167_, v_consumed_3177_);
return v___x_3181_;
}
else
{
lean_object* v___x_3182_; 
lean_dec_ref_known(v_drainLimit_3163_, 1);
lean_dec_ref(v_stream_3166_);
lean_dec(v_inst_3165_);
lean_dec_ref(v_inst_3164_);
v___x_3182_ = lean_apply_4(v_toBind_3168_, lean_box(0), lean_box(0), v_closeStream_3167_, v___f_3169_);
return v___x_3182_;
}
}
else
{
lean_object* v___x_3183_; 
lean_dec(v___f_3169_);
lean_dec(v_toBind_3168_);
v___x_3183_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3164_, v_inst_3165_, v_stream_3166_, v_drainLimit_3163_, v_closeStream_3167_, v_consumed_3177_);
return v___x_3183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed(lean_object* v_toPure_3184_, lean_object* v_consumed_3185_, lean_object* v_drainLimit_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_stream_3189_, lean_object* v_closeStream_3190_, lean_object* v_toBind_3191_, lean_object* v___f_3192_, lean_object* v_____do__lift_3193_){
_start:
{
uint64_t v_consumed_boxed_3194_; lean_object* v_res_3195_; 
v_consumed_boxed_3194_ = lean_unbox_uint64(v_consumed_3185_);
lean_dec_ref(v_consumed_3185_);
v_res_3195_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(v_toPure_3184_, v_consumed_boxed_3194_, v_drainLimit_3186_, v_inst_3187_, v_inst_3188_, v_stream_3189_, v_closeStream_3190_, v_toBind_3191_, v___f_3192_, v_____do__lift_3193_);
lean_dec(v_____do__lift_3193_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_stream_3198_, lean_object* v_drainLimit_3199_, lean_object* v_closeStream_3200_, uint64_t v_consumed_3201_){
_start:
{
lean_object* v_toApplicative_3202_; lean_object* v_toBind_3203_; lean_object* v_toPure_3204_; lean_object* v___x_3205_; lean_object* v___f_3206_; lean_object* v___x_3207_; lean_object* v___f_3208_; lean_object* v___x_3209_; 
v_toApplicative_3202_ = lean_ctor_get(v_inst_3196_, 0);
v_toBind_3203_ = lean_ctor_get(v_inst_3196_, 1);
lean_inc_n(v_toBind_3203_, 2);
v_toPure_3204_ = lean_ctor_get(v_toApplicative_3202_, 1);
lean_inc_n(v_toPure_3204_, 2);
lean_inc(v_inst_3197_);
lean_inc_ref(v_stream_3198_);
v___x_3205_ = lean_apply_1(v_inst_3197_, v_stream_3198_);
v___f_3206_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3206_, 0, v_toPure_3204_);
v___x_3207_ = lean_box_uint64(v_consumed_3201_);
v___f_3208_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3208_, 0, v_toPure_3204_);
lean_closure_set(v___f_3208_, 1, v___x_3207_);
lean_closure_set(v___f_3208_, 2, v_drainLimit_3199_);
lean_closure_set(v___f_3208_, 3, v_inst_3196_);
lean_closure_set(v___f_3208_, 4, v_inst_3197_);
lean_closure_set(v___f_3208_, 5, v_stream_3198_);
lean_closure_set(v___f_3208_, 6, v_closeStream_3200_);
lean_closure_set(v___f_3208_, 7, v_toBind_3203_);
lean_closure_set(v___f_3208_, 8, v___f_3206_);
v___x_3209_ = lean_apply_4(v_toBind_3203_, lean_box(0), lean_box(0), v___x_3205_, v___f_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___boxed(lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_stream_3212_, lean_object* v_drainLimit_3213_, lean_object* v_closeStream_3214_, lean_object* v_consumed_3215_){
_start:
{
uint64_t v_consumed_boxed_3216_; lean_object* v_res_3217_; 
v_consumed_boxed_3216_ = lean_unbox_uint64(v_consumed_3215_);
lean_dec_ref(v_consumed_3215_);
v_res_3217_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3210_, v_inst_3211_, v_stream_3212_, v_drainLimit_3213_, v_closeStream_3214_, v_consumed_boxed_3216_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_object* v_m_3218_, lean_object* v_inst_3219_, lean_object* v_inst_3220_, lean_object* v_stream_3221_, lean_object* v_drainLimit_3222_, lean_object* v_closeStream_3223_, uint64_t v_consumed_3224_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3219_, v_inst_3220_, v_stream_3221_, v_drainLimit_3222_, v_closeStream_3223_, v_consumed_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___boxed(lean_object* v_m_3226_, lean_object* v_inst_3227_, lean_object* v_inst_3228_, lean_object* v_stream_3229_, lean_object* v_drainLimit_3230_, lean_object* v_closeStream_3231_, lean_object* v_consumed_3232_){
_start:
{
uint64_t v_consumed_boxed_3233_; lean_object* v_res_3234_; 
v_consumed_boxed_3233_ = lean_unbox_uint64(v_consumed_3232_);
lean_dec_ref(v_consumed_3232_);
v_res_3234_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(v_m_3226_, v_inst_3227_, v_inst_3228_, v_stream_3229_, v_drainLimit_3230_, v_closeStream_3231_, v_consumed_boxed_3233_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain___redArg(lean_object* v_inst_3235_, lean_object* v_inst_3236_, lean_object* v_stream_3237_, lean_object* v_drainLimit_3238_, lean_object* v_closeStream_3239_){
_start:
{
uint64_t v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = 0ULL;
v___x_3241_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3235_, v_inst_3236_, v_stream_3237_, v_drainLimit_3238_, v_closeStream_3239_, v___x_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain(lean_object* v_m_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_stream_3245_, lean_object* v_drainLimit_3246_, lean_object* v_closeStream_3247_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Std_Http_Body_Stream_drain___redArg(v_inst_3243_, v_inst_3244_, v_stream_3245_, v_drainLimit_3246_, v_closeStream_3247_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t v_incomplete_3254_, lean_object* v_chunk_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v_pendingProducer_3260_; lean_object* v_pendingConsumer_3261_; lean_object* v_interestWaiter_3262_; uint8_t v_closed_3263_; lean_object* v_knownSize_3264_; lean_object* v_pendingIncompleteChunk_3265_; lean_object* v_closeError_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3307_; 
v___x_3258_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_3256_);
v___x_3259_ = lean_st_ref_get(v___y_3256_);
v_pendingProducer_3260_ = lean_ctor_get(v___x_3259_, 0);
v_pendingConsumer_3261_ = lean_ctor_get(v___x_3259_, 1);
v_interestWaiter_3262_ = lean_ctor_get(v___x_3259_, 2);
v_closed_3263_ = lean_ctor_get_uint8(v___x_3259_, sizeof(void*)*6);
v_knownSize_3264_ = lean_ctor_get(v___x_3259_, 3);
v_pendingIncompleteChunk_3265_ = lean_ctor_get(v___x_3259_, 4);
v_closeError_3266_ = lean_ctor_get(v___x_3259_, 5);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3268_ = v___x_3259_;
v_isShared_3269_ = v_isSharedCheck_3307_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_closeError_3266_);
lean_inc(v_pendingIncompleteChunk_3265_);
lean_inc(v_knownSize_3264_);
lean_inc(v_interestWaiter_3262_);
lean_inc(v_pendingConsumer_3261_);
lean_inc(v_pendingProducer_3260_);
lean_dec(v___x_3259_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3307_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___y_3271_; 
if (v_closed_3263_ == 0)
{
if (lean_obj_tag(v_pendingIncompleteChunk_3265_) == 0)
{
v___y_3271_ = v_chunk_3255_;
goto v___jp_3270_;
}
else
{
lean_object* v_val_3285_; lean_object* v_data_3286_; lean_object* v_extensions_3287_; lean_object* v_data_3288_; lean_object* v_extensions_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3305_; 
v_val_3285_ = lean_ctor_get(v_pendingIncompleteChunk_3265_, 0);
lean_inc(v_val_3285_);
lean_dec_ref_known(v_pendingIncompleteChunk_3265_, 1);
v_data_3286_ = lean_ctor_get(v_val_3285_, 0);
lean_inc_ref(v_data_3286_);
v_extensions_3287_ = lean_ctor_get(v_val_3285_, 1);
lean_inc_ref(v_extensions_3287_);
lean_dec(v_val_3285_);
v_data_3288_ = lean_ctor_get(v_chunk_3255_, 0);
v_extensions_3289_ = lean_ctor_get(v_chunk_3255_, 1);
v_isSharedCheck_3305_ = !lean_is_exclusive(v_chunk_3255_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3291_ = v_chunk_3255_;
v_isShared_3292_ = v_isSharedCheck_3305_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_extensions_3289_);
lean_inc(v_data_3288_);
lean_dec(v_chunk_3255_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3305_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3293_ = lean_unsigned_to_nat(0u);
v___x_3294_ = lean_byte_array_size(v_data_3286_);
v___x_3295_ = lean_byte_array_size(v_data_3288_);
v___x_3296_ = lean_byte_array_copy_slice(v_data_3288_, v___x_3293_, v_data_3286_, v___x_3294_, v___x_3295_, v_closed_3263_);
lean_dec_ref(v_data_3288_);
v___x_3297_ = lean_array_get_size(v_extensions_3287_);
v___x_3298_ = lean_nat_dec_eq(v___x_3297_, v___x_3293_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3300_; 
lean_dec_ref(v_extensions_3289_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v_extensions_3287_);
lean_ctor_set(v___x_3291_, 0, v___x_3296_);
v___x_3300_ = v___x_3291_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_extensions_3287_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
v___y_3271_ = v___x_3300_;
goto v___jp_3270_;
}
}
else
{
lean_object* v___x_3303_; 
lean_dec_ref(v_extensions_3287_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3296_);
v___x_3303_ = v___x_3291_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_extensions_3289_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
v___y_3271_ = v___x_3303_;
goto v___jp_3270_;
}
}
}
}
}
else
{
lean_object* v___x_3306_; 
lean_del_object(v___x_3268_);
lean_dec(v_closeError_3266_);
lean_dec(v_pendingIncompleteChunk_3265_);
lean_dec(v_knownSize_3264_);
lean_dec(v_interestWaiter_3262_);
lean_dec(v_pendingConsumer_3261_);
lean_dec(v_pendingProducer_3260_);
lean_dec_ref(v_chunk_3255_);
v___x_3306_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_3306_;
}
v___jp_3270_:
{
if (v_incomplete_3254_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3272_ = lean_box(0);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 4, v___x_3272_);
v___x_3274_ = v___x_3268_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_pendingProducer_3260_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_pendingConsumer_3261_);
lean_ctor_set(v_reuseFailAlloc_3278_, 2, v_interestWaiter_3262_);
lean_ctor_set(v_reuseFailAlloc_3278_, 3, v_knownSize_3264_);
lean_ctor_set(v_reuseFailAlloc_3278_, 4, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3278_, 5, v_closeError_3266_);
lean_ctor_set_uint8(v_reuseFailAlloc_3278_, sizeof(void*)*6, v_closed_3263_);
v___x_3274_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = lean_st_ref_swap(v___y_3256_, v___x_3274_);
lean_dec(v___x_3275_);
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___y_3271_);
v___x_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
return v___x_3277_;
}
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___y_3271_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 4, v___x_3279_);
v___x_3281_ = v___x_3268_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_pendingProducer_3260_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_pendingConsumer_3261_);
lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_interestWaiter_3262_);
lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_knownSize_3264_);
lean_ctor_set(v_reuseFailAlloc_3284_, 4, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3284_, 5, v_closeError_3266_);
lean_ctor_set_uint8(v_reuseFailAlloc_3284_, sizeof(void*)*6, v_closed_3263_);
v___x_3281_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = lean_st_ref_swap(v___y_3256_, v___x_3281_);
lean_dec(v___x_3282_);
v___x_3283_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
return v___x_3283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_incomplete_3308_, lean_object* v_chunk_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
uint8_t v_incomplete_boxed_3312_; lean_object* v_res_3313_; 
v_incomplete_boxed_3312_ = lean_unbox(v_incomplete_3308_);
v_res_3313_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_incomplete_boxed_3312_, v_chunk_3309_, v___y_3310_);
lean_dec(v___y_3310_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_3314_, lean_object* v_chunk_3315_, uint8_t v_incomplete_3316_){
_start:
{
lean_object* v___x_3318_; lean_object* v___f_3319_; lean_object* v___x_3320_; 
v___x_3318_ = lean_box(v_incomplete_3316_);
v___f_3319_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3319_, 0, v___x_3318_);
lean_closure_set(v___f_3319_, 1, v_chunk_3315_);
v___x_3320_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_3314_, v___f_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_3321_, lean_object* v_chunk_3322_, lean_object* v_incomplete_3323_, lean_object* v_a_3324_){
_start:
{
uint8_t v_incomplete_boxed_3325_; lean_object* v_res_3326_; 
v_incomplete_boxed_3325_ = lean_unbox(v_incomplete_3323_);
v_res_3326_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3321_, v_chunk_3322_, v_incomplete_boxed_3325_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_3333_){
_start:
{
if (lean_obj_tag(v_x_3333_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3343_; 
v_a_3335_ = lean_ctor_get(v_x_3333_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_x_3333_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3337_ = v_x_3333_;
v_isShared_3338_ = v_isSharedCheck_3343_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v_x_3333_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3343_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
}
}
else
{
lean_object* v___x_3344_; 
lean_dec_ref_known(v_x_3333_, 1);
v___x_3344_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_3345_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___3351_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_3358_, lean_object* v_x_3359_){
_start:
{
if (lean_obj_tag(v_x_3359_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3371_; 
lean_dec_ref(v___f_3358_);
v_a_3363_ = lean_ctor_get(v_x_3359_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_x_3359_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3365_ = v_x_3359_;
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v_x_3359_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
return v___x_3369_;
}
}
}
else
{
lean_object* v_a_3372_; 
v_a_3372_ = lean_ctor_get(v_x_3359_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v_x_3359_, 1);
if (lean_obj_tag(v_a_3372_) == 1)
{
lean_object* v_val_3373_; uint8_t v___x_3374_; 
v_val_3373_ = lean_ctor_get(v_a_3372_, 0);
lean_inc(v_val_3373_);
lean_dec_ref_known(v_a_3372_, 1);
v___x_3374_ = lean_unbox(v_val_3373_);
lean_dec(v_val_3373_);
if (v___x_3374_ == 1)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = lean_box(0);
v___x_3376_ = lean_apply_2(v___f_3358_, v___x_3375_, lean_box(0));
return v___x_3376_;
}
else
{
lean_dec_ref(v___f_3358_);
goto v___jp_3361_;
}
}
else
{
lean_dec(v_a_3372_);
lean_dec_ref(v___f_3358_);
goto v___jp_3361_;
}
}
v___jp_3361_:
{
lean_object* v___x_3362_; 
v___x_3362_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_3377_, lean_object* v_x_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_3377_, v_x_3378_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3382_, 0, v_a_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_3383_, lean_object* v_x_3384_){
_start:
{
if (lean_obj_tag(v_x_3384_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3394_; 
v_a_3386_ = lean_ctor_get(v_x_3384_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_x_3384_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3388_ = v_x_3384_;
v_isShared_3389_ = v_isSharedCheck_3394_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v_x_3384_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3394_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
}
}
else
{
lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3405_; 
v_isSharedCheck_3405_ = !lean_is_exclusive(v_x_3384_);
if (v_isSharedCheck_3405_ == 0)
{
lean_object* v_unused_3406_; 
v_unused_3406_ = lean_ctor_get(v_x_3384_, 0);
lean_dec(v_unused_3406_);
v___x_3396_ = v_x_3384_;
v_isShared_3397_ = v_isSharedCheck_3405_;
goto v_resetjp_3395_;
}
else
{
lean_dec(v_x_3384_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3405_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3398_ = lean_box(v___x_3383_);
v___x_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3399_);
v___x_3401_ = v___x_3396_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_3407_, lean_object* v_x_3408_, lean_object* v___y_3409_){
_start:
{
uint8_t v___x_5091__boxed_3410_; lean_object* v_res_3411_; 
v___x_5091__boxed_3410_ = lean_unbox(v___x_3407_);
v_res_3411_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5091__boxed_3410_, v_x_3408_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_3412_, lean_object* v_x_3413_){
_start:
{
if (lean_obj_tag(v_x_3413_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3423_; 
v_a_3415_ = lean_ctor_get(v_x_3413_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_x_3413_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3417_ = v_x_3413_;
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v_x_3413_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
}
}
}
else
{
lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3434_; 
v_isSharedCheck_3434_ = !lean_is_exclusive(v_x_3413_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; 
v_unused_3435_ = lean_ctor_get(v_x_3413_, 0);
lean_dec(v_unused_3435_);
v___x_3425_ = v_x_3413_;
v_isShared_3426_ = v_isSharedCheck_3434_;
goto v_resetjp_3424_;
}
else
{
lean_dec(v_x_3413_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3434_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3427_ = lean_box(v_a_3412_);
v___x_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3428_);
v___x_3430_ = v___x_3425_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
return v___x_3432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_3436_, lean_object* v_x_3437_, lean_object* v___y_3438_){
_start:
{
uint8_t v_a_5143__boxed_3439_; lean_object* v_res_3440_; 
v_a_5143__boxed_3439_ = lean_unbox(v_a_3436_);
v_res_3440_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5143__boxed_3439_, v_x_3437_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_3441_, lean_object* v_interestWaiter_3442_, uint8_t v_closed_3443_, lean_object* v_knownSize_3444_, lean_object* v_pendingIncompleteChunk_3445_, lean_object* v_closeError_3446_, lean_object* v___y_3447_, lean_object* v_chunk_3448_, lean_object* v___f_3449_, lean_object* v_x_3450_){
_start:
{
if (lean_obj_tag(v_x_3450_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref(v___f_3449_);
lean_dec(v_closeError_3446_);
lean_dec(v_pendingIncompleteChunk_3445_);
lean_dec(v_knownSize_3444_);
lean_dec(v_interestWaiter_3442_);
lean_dec(v_pendingProducer_3441_);
v_a_3452_ = lean_ctor_get(v_x_3450_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_x_3450_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3454_ = v_x_3450_;
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v_x_3450_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
return v___x_3458_;
}
}
}
else
{
lean_object* v_a_3461_; uint8_t v___x_3462_; 
v_a_3461_ = lean_ctor_get(v_x_3450_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v_x_3450_, 1);
v___x_3462_ = lean_unbox(v_a_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___f_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; lean_object* v___x_3470_; 
lean_dec_ref(v___f_3449_);
lean_inc(v_a_3461_);
v___f_3463_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3463_, 0, v_a_3461_);
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3465_, 0, v_pendingProducer_3441_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
lean_ctor_set(v___x_3465_, 2, v_interestWaiter_3442_);
lean_ctor_set(v___x_3465_, 3, v_knownSize_3444_);
lean_ctor_set(v___x_3465_, 4, v_pendingIncompleteChunk_3445_);
lean_ctor_set(v___x_3465_, 5, v_closeError_3446_);
lean_ctor_set_uint8(v___x_3465_, sizeof(void*)*6, v_closed_3443_);
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_st_ref_swap(v___y_3447_, v___x_3465_);
lean_dec(v___x_3467_);
v___x_3468_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3469_ = lean_unbox(v_a_3461_);
lean_dec(v_a_3461_);
v___x_3470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3466_, v___x_3469_, v___x_3468_, v___f_3463_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_dec(v_a_3461_);
v___x_3471_ = lean_box(0);
v___x_3472_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_3444_, v_chunk_3448_);
v___x_3473_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3473_, 0, v_pendingProducer_3441_);
lean_ctor_set(v___x_3473_, 1, v___x_3471_);
lean_ctor_set(v___x_3473_, 2, v_interestWaiter_3442_);
lean_ctor_set(v___x_3473_, 3, v___x_3472_);
lean_ctor_set(v___x_3473_, 4, v_pendingIncompleteChunk_3445_);
lean_ctor_set(v___x_3473_, 5, v_closeError_3446_);
lean_ctor_set_uint8(v___x_3473_, sizeof(void*)*6, v_closed_3443_);
v___x_3474_ = lean_unsigned_to_nat(0u);
v___x_3475_ = lean_st_ref_swap(v___y_3447_, v___x_3473_);
lean_dec(v___x_3475_);
v___x_3476_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3477_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3474_, v_closed_3443_, v___x_3476_, v___f_3449_);
return v___x_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_3478_, lean_object* v_interestWaiter_3479_, lean_object* v_closed_3480_, lean_object* v_knownSize_3481_, lean_object* v_pendingIncompleteChunk_3482_, lean_object* v_closeError_3483_, lean_object* v___y_3484_, lean_object* v_chunk_3485_, lean_object* v___f_3486_, lean_object* v_x_3487_, lean_object* v___y_3488_){
_start:
{
uint8_t v_closed_boxed_3489_; lean_object* v_res_3490_; 
v_closed_boxed_3489_ = lean_unbox(v_closed_3480_);
v_res_3490_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_3478_, v_interestWaiter_3479_, v_closed_boxed_3489_, v_knownSize_3481_, v_pendingIncompleteChunk_3482_, v_closeError_3483_, v___y_3484_, v_chunk_3485_, v___f_3486_, v_x_3487_);
lean_dec_ref(v_chunk_3485_);
lean_dec(v___y_3484_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v___y_3509_, lean_object* v_chunk_3510_, lean_object* v_a_3511_, lean_object* v___f_3512_, lean_object* v_x_3513_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3523_; 
lean_dec_ref(v___f_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_chunk_3510_);
v_a_3515_ = lean_ctor_get(v_x_3513_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_x_3513_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3517_ = v_x_3513_;
v_isShared_3518_ = v_isSharedCheck_3523_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v_x_3513_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3523_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3577_; 
v_a_3524_ = lean_ctor_get(v_x_3513_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_x_3513_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3526_ = v_x_3513_;
v_isShared_3527_ = v_isSharedCheck_3577_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v_x_3513_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3577_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
uint8_t v_closed_3528_; 
v_closed_3528_ = lean_ctor_get_uint8(v_a_3524_, sizeof(void*)*6);
if (v_closed_3528_ == 0)
{
lean_object* v_pendingConsumer_3529_; 
v_pendingConsumer_3529_ = lean_ctor_get(v_a_3524_, 1);
lean_inc(v_pendingConsumer_3529_);
if (lean_obj_tag(v_pendingConsumer_3529_) == 1)
{
lean_object* v_pendingProducer_3530_; lean_object* v_interestWaiter_3531_; lean_object* v_knownSize_3532_; lean_object* v_pendingIncompleteChunk_3533_; lean_object* v_closeError_3534_; lean_object* v_val_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3554_; 
lean_dec_ref(v___f_3512_);
lean_dec(v_a_3511_);
v_pendingProducer_3530_ = lean_ctor_get(v_a_3524_, 0);
lean_inc(v_pendingProducer_3530_);
v_interestWaiter_3531_ = lean_ctor_get(v_a_3524_, 2);
lean_inc(v_interestWaiter_3531_);
v_knownSize_3532_ = lean_ctor_get(v_a_3524_, 3);
lean_inc(v_knownSize_3532_);
v_pendingIncompleteChunk_3533_ = lean_ctor_get(v_a_3524_, 4);
lean_inc(v_pendingIncompleteChunk_3533_);
v_closeError_3534_ = lean_ctor_get(v_a_3524_, 5);
lean_inc(v_closeError_3534_);
lean_dec(v_a_3524_);
v_val_3535_ = lean_ctor_get(v_pendingConsumer_3529_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_pendingConsumer_3529_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3537_ = v_pendingConsumer_3529_;
v_isShared_3538_ = v_isSharedCheck_3554_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_val_3535_);
lean_dec(v_pendingConsumer_3529_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3554_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___f_3539_; lean_object* v___x_3540_; lean_object* v___f_3541_; lean_object* v___x_3543_; 
v___f_3539_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_3540_ = lean_box(v_closed_3528_);
lean_inc_ref(v_chunk_3510_);
lean_inc(v___y_3509_);
v___f_3541_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 11, 9);
lean_closure_set(v___f_3541_, 0, v_pendingProducer_3530_);
lean_closure_set(v___f_3541_, 1, v_interestWaiter_3531_);
lean_closure_set(v___f_3541_, 2, v___x_3540_);
lean_closure_set(v___f_3541_, 3, v_knownSize_3532_);
lean_closure_set(v___f_3541_, 4, v_pendingIncompleteChunk_3533_);
lean_closure_set(v___f_3541_, 5, v_closeError_3534_);
lean_closure_set(v___f_3541_, 6, v___y_3509_);
lean_closure_set(v___f_3541_, 7, v_chunk_3510_);
lean_closure_set(v___f_3541_, 8, v___f_3539_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_chunk_3510_);
v___x_3543_ = v___x_3537_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_chunk_3510_);
v___x_3543_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3543_);
v___x_3545_ = v___x_3526_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3546_ = lean_unsigned_to_nat(0u);
v___x_3547_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_3535_, v___x_3545_);
lean_dec(v_val_3535_);
v___x_3548_ = lean_box(v___x_3547_);
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
v___x_3551_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3546_, v_closed_3528_, v___x_3550_, v___f_3541_);
return v___x_3551_;
}
}
}
}
else
{
lean_object* v_pendingProducer_3555_; 
lean_del_object(v___x_3526_);
v_pendingProducer_3555_ = lean_ctor_get(v_a_3524_, 0);
if (lean_obj_tag(v_pendingProducer_3555_) == 0)
{
lean_object* v_interestWaiter_3556_; lean_object* v_knownSize_3557_; lean_object* v_pendingIncompleteChunk_3558_; lean_object* v_closeError_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3572_; 
v_interestWaiter_3556_ = lean_ctor_get(v_a_3524_, 2);
v_knownSize_3557_ = lean_ctor_get(v_a_3524_, 3);
v_pendingIncompleteChunk_3558_ = lean_ctor_get(v_a_3524_, 4);
v_closeError_3559_ = lean_ctor_get(v_a_3524_, 5);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_a_3524_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; lean_object* v_unused_3574_; 
v_unused_3573_ = lean_ctor_get(v_a_3524_, 1);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v_a_3524_, 0);
lean_dec(v_unused_3574_);
v___x_3561_ = v_a_3524_;
v_isShared_3562_ = v_isSharedCheck_3572_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_closeError_3559_);
lean_inc(v_pendingIncompleteChunk_3558_);
lean_inc(v_knownSize_3557_);
lean_inc(v_interestWaiter_3556_);
lean_dec(v_a_3524_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3572_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3563_, 0, v_chunk_3510_);
lean_ctor_set(v___x_3563_, 1, v_a_3511_);
v___x_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3564_);
v___x_3566_ = v___x_3561_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_pendingConsumer_3529_);
lean_ctor_set(v_reuseFailAlloc_3571_, 2, v_interestWaiter_3556_);
lean_ctor_set(v_reuseFailAlloc_3571_, 3, v_knownSize_3557_);
lean_ctor_set(v_reuseFailAlloc_3571_, 4, v_pendingIncompleteChunk_3558_);
lean_ctor_set(v_reuseFailAlloc_3571_, 5, v_closeError_3559_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, sizeof(void*)*6, v_closed_3528_);
v___x_3566_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3567_ = lean_unsigned_to_nat(0u);
v___x_3568_ = lean_st_ref_swap(v___y_3509_, v___x_3566_);
lean_dec(v___x_3568_);
v___x_3569_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3570_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3567_, v_closed_3528_, v___x_3569_, v___f_3512_);
return v___x_3570_;
}
}
}
else
{
lean_object* v___x_3575_; 
lean_dec(v_pendingConsumer_3529_);
lean_dec(v_a_3524_);
lean_dec_ref(v___f_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_chunk_3510_);
v___x_3575_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_3575_;
}
}
}
else
{
lean_object* v___x_3576_; 
lean_del_object(v___x_3526_);
lean_dec(v_a_3524_);
lean_dec_ref(v___f_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_chunk_3510_);
v___x_3576_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_3576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v___y_3578_, lean_object* v_chunk_3579_, lean_object* v_a_3580_, lean_object* v___f_3581_, lean_object* v_x_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v___y_3578_, v_chunk_3579_, v_a_3580_, v___f_3581_, v_x_3582_);
lean_dec(v___y_3578_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_3585_, lean_object* v___f_3586_, lean_object* v_x_3587_){
_start:
{
if (lean_obj_tag(v_x_3587_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v___f_3586_);
v_a_3589_ = lean_ctor_get(v_x_3587_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_x_3587_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3591_ = v_x_3587_;
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v_x_3587_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
return v___x_3595_;
}
}
}
else
{
lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3609_; 
v_isSharedCheck_3609_ = !lean_is_exclusive(v_x_3587_);
if (v_isSharedCheck_3609_ == 0)
{
lean_object* v_unused_3610_; 
v_unused_3610_ = lean_ctor_get(v_x_3587_, 0);
lean_dec(v_unused_3610_);
v___x_3599_ = v_x_3587_;
v_isShared_3600_ = v_isSharedCheck_3609_;
goto v_resetjp_3598_;
}
else
{
lean_dec(v_x_3587_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3609_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3601_ = lean_unsigned_to_nat(0u);
v___x_3602_ = 0;
v___x_3603_ = lean_st_ref_get(v___y_3585_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v___x_3603_);
v___x_3605_ = v___x_3599_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
v___x_3607_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3601_, v___x_3602_, v___x_3606_, v___f_3586_);
return v___x_3607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_3611_, lean_object* v___f_3612_, lean_object* v_x_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_3611_, v___f_3612_, v_x_3613_);
lean_dec(v___y_3611_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_3616_, lean_object* v_a_3617_, lean_object* v___f_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___f_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
lean_inc_n(v___y_3619_, 2);
v___f_3621_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_3621_, 0, v___y_3619_);
lean_closure_set(v___f_3621_, 1, v_chunk_3616_);
lean_closure_set(v___f_3621_, 2, v_a_3617_);
lean_closure_set(v___f_3621_, 3, v___f_3618_);
v___f_3622_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_3622_, 0, v___y_3619_);
lean_closure_set(v___f_3622_, 1, v___f_3621_);
v___x_3623_ = lean_unsigned_to_nat(0u);
v___x_3624_ = 0;
v___x_3625_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3619_);
v___x_3626_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3623_, v___x_3624_, v___x_3625_, v___f_3622_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_3627_, lean_object* v_a_3628_, lean_object* v___f_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_3627_, v_a_3628_, v___f_3629_, v___y_3630_);
lean_dec(v___y_3630_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_3638_, lean_object* v___f_3639_, lean_object* v___f_3640_, lean_object* v_stream_3641_, lean_object* v_chunk_3642_, lean_object* v___f_3643_, lean_object* v_x_3644_){
_start:
{
if (lean_obj_tag(v_x_3644_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3654_; 
lean_dec_ref(v___f_3643_);
lean_dec_ref(v_chunk_3642_);
lean_dec_ref(v_stream_3641_);
lean_dec_ref(v___f_3640_);
lean_dec_ref(v___f_3639_);
v_a_3646_ = lean_ctor_get(v_x_3644_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_x_3644_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3648_ = v_x_3644_;
v_isShared_3649_ = v_isSharedCheck_3654_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v_x_3644_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3654_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3652_; 
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
return v___x_3652_;
}
}
}
else
{
lean_object* v_a_3655_; 
v_a_3655_ = lean_ctor_get(v_x_3644_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v_x_3644_, 1);
if (lean_obj_tag(v_a_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3664_; 
lean_dec_ref(v___f_3643_);
lean_dec_ref(v_chunk_3642_);
lean_dec_ref(v_stream_3641_);
lean_dec_ref(v___f_3640_);
lean_dec_ref(v___f_3639_);
v_a_3656_ = lean_ctor_get(v_a_3655_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_a_3655_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3658_ = v_a_3655_;
v_isShared_3659_ = v_isSharedCheck_3664_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v_a_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3664_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
return v___x_3662_;
}
}
}
else
{
lean_object* v_a_3665_; 
v_a_3665_ = lean_ctor_get(v_a_3655_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v_a_3655_, 1);
if (lean_obj_tag(v_a_3665_) == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; uint8_t v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_dec_ref(v___f_3643_);
lean_dec_ref(v_chunk_3642_);
lean_dec_ref(v_stream_3641_);
v___x_3666_ = lean_io_promise_result_opt(v_a_3638_);
v___x_3667_ = lean_unsigned_to_nat(0u);
v___x_3668_ = 0;
v___x_3669_ = lean_task_map(v___f_3639_, v___x_3666_, v___x_3667_, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
v___x_3671_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3667_, v___x_3668_, v___x_3670_, v___f_3640_);
return v___x_3671_;
}
else
{
lean_object* v_val_3672_; uint8_t v___x_3673_; 
lean_dec_ref(v___f_3640_);
lean_dec_ref(v___f_3639_);
v_val_3672_ = lean_ctor_get(v_a_3665_, 0);
lean_inc(v_val_3672_);
lean_dec_ref_known(v_a_3665_, 1);
v___x_3673_ = lean_unbox(v_val_3672_);
lean_dec(v_val_3672_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; 
lean_dec_ref(v___f_3643_);
v___x_3674_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3641_, v_chunk_3642_);
return v___x_3674_;
}
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_dec_ref(v_chunk_3642_);
lean_dec_ref(v_stream_3641_);
v___x_3675_ = lean_box(0);
v___x_3676_ = lean_apply_2(v___f_3643_, v___x_3675_, lean_box(0));
return v___x_3676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_3677_, lean_object* v___f_3678_, lean_object* v___f_3679_, lean_object* v_stream_3680_, lean_object* v_chunk_3681_, lean_object* v___f_3682_, lean_object* v_x_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_3677_, v___f_3678_, v___f_3679_, v_stream_3680_, v_chunk_3681_, v___f_3682_, v_x_3683_);
lean_dec(v_a_3677_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_3686_, lean_object* v___f_3687_, lean_object* v___f_3688_, lean_object* v___f_3689_, lean_object* v_stream_3690_, lean_object* v___f_3691_, lean_object* v_x_3692_){
_start:
{
if (lean_obj_tag(v_x_3692_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3702_; 
lean_dec_ref(v___f_3691_);
lean_dec_ref(v_stream_3690_);
lean_dec_ref(v___f_3689_);
lean_dec_ref(v___f_3688_);
lean_dec_ref(v___f_3687_);
lean_dec_ref(v_chunk_3686_);
v_a_3694_ = lean_ctor_get(v_x_3692_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_x_3692_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3696_ = v_x_3692_;
v_isShared_3697_ = v_isSharedCheck_3702_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v_x_3692_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3702_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
return v___x_3700_;
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___f_3704_; lean_object* v___f_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v_a_3703_ = lean_ctor_get(v_x_3692_, 0);
lean_inc_n(v_a_3703_, 2);
lean_dec_ref_known(v_x_3692_, 1);
lean_inc_ref(v_chunk_3686_);
v___f_3704_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_3704_, 0, v_chunk_3686_);
lean_closure_set(v___f_3704_, 1, v_a_3703_);
lean_closure_set(v___f_3704_, 2, v___f_3687_);
lean_inc_ref(v_stream_3690_);
v___f_3705_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3705_, 0, v_a_3703_);
lean_closure_set(v___f_3705_, 1, v___f_3688_);
lean_closure_set(v___f_3705_, 2, v___f_3689_);
lean_closure_set(v___f_3705_, 3, v_stream_3690_);
lean_closure_set(v___f_3705_, 4, v_chunk_3686_);
lean_closure_set(v___f_3705_, 5, v___f_3691_);
v___x_3706_ = lean_unsigned_to_nat(0u);
v___x_3707_ = 0;
v___x_3708_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3690_, v___f_3704_);
v___x_3709_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3706_, v___x_3707_, v___x_3708_, v___f_3705_);
return v___x_3709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_3710_, lean_object* v___f_3711_, lean_object* v___f_3712_, lean_object* v___f_3713_, lean_object* v_stream_3714_, lean_object* v___f_3715_, lean_object* v_x_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_3710_, v___f_3711_, v___f_3712_, v___f_3713_, v_stream_3714_, v___f_3715_, v_x_3716_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_3719_, lean_object* v_chunk_3720_){
_start:
{
lean_object* v___f_3722_; lean_object* v___f_3723_; lean_object* v___f_3724_; lean_object* v___f_3725_; lean_object* v___f_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___f_3722_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_3723_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_3724_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_3725_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_3726_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_3726_, 0, v_chunk_3720_);
lean_closure_set(v___f_3726_, 1, v___f_3722_);
lean_closure_set(v___f_3726_, 2, v___f_3725_);
lean_closure_set(v___f_3726_, 3, v___f_3724_);
lean_closure_set(v___f_3726_, 4, v_stream_3719_);
lean_closure_set(v___f_3726_, 5, v___f_3723_);
v___x_3727_ = lean_unsigned_to_nat(0u);
v___x_3728_ = 0;
v___x_3729_ = lean_io_promise_new();
v___x_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
v___x_3732_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3727_, v___x_3728_, v___x_3731_, v___f_3726_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_3733_, lean_object* v_chunk_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3733_, v_chunk_3734_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_3737_, lean_object* v_x_3738_){
_start:
{
if (lean_obj_tag(v_x_3738_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v_stream_3737_);
v_a_3740_ = lean_ctor_get(v_x_3738_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_x_3738_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3742_ = v_x_3738_;
v_isShared_3743_ = v_isSharedCheck_3748_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v_x_3738_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3748_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v___x_3746_; 
v___x_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
return v___x_3746_;
}
}
}
else
{
lean_object* v_a_3749_; 
v_a_3749_ = lean_ctor_get(v_x_3738_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v_x_3738_, 1);
if (lean_obj_tag(v_a_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3758_; 
lean_dec_ref(v_stream_3737_);
v_a_3750_ = lean_ctor_get(v_a_3749_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_a_3749_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3752_ = v_a_3749_;
v_isShared_3753_ = v_isSharedCheck_3758_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v_a_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3758_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
return v___x_3756_;
}
}
}
else
{
lean_object* v_a_3759_; 
v_a_3759_ = lean_ctor_get(v_a_3749_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v_a_3749_, 1);
if (lean_obj_tag(v_a_3759_) == 0)
{
lean_object* v___x_3760_; 
lean_dec_ref(v_stream_3737_);
v___x_3760_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3760_;
}
else
{
lean_object* v_val_3761_; uint8_t v___y_3763_; lean_object* v_data_3766_; lean_object* v_extensions_3767_; uint8_t v___x_3768_; 
v_val_3761_ = lean_ctor_get(v_a_3759_, 0);
lean_inc(v_val_3761_);
lean_dec_ref_known(v_a_3759_, 1);
v_data_3766_ = lean_ctor_get(v_val_3761_, 0);
v_extensions_3767_ = lean_ctor_get(v_val_3761_, 1);
v___x_3768_ = l_ByteArray_isEmpty(v_data_3766_);
if (v___x_3768_ == 0)
{
v___y_3763_ = v___x_3768_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v___x_3769_ = lean_array_get_size(v_extensions_3767_);
v___x_3770_ = lean_unsigned_to_nat(0u);
v___x_3771_ = lean_nat_dec_eq(v___x_3769_, v___x_3770_);
v___y_3763_ = v___x_3771_;
goto v___jp_3762_;
}
v___jp_3762_:
{
if (v___y_3763_ == 0)
{
lean_object* v___x_3764_; 
v___x_3764_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3737_, v_val_3761_);
return v___x_3764_;
}
else
{
lean_object* v___x_3765_; 
lean_dec(v_val_3761_);
lean_dec_ref(v_stream_3737_);
v___x_3765_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3765_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object* v_stream_3772_, lean_object* v_x_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_3772_, v_x_3773_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object* v_stream_3776_, lean_object* v_chunk_3777_, uint8_t v_incomplete_3778_){
_start:
{
lean_object* v___f_3780_; lean_object* v___x_3781_; uint8_t v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_inc_ref(v_stream_3776_);
v___f_3780_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3780_, 0, v_stream_3776_);
v___x_3781_ = lean_unsigned_to_nat(0u);
v___x_3782_ = 0;
v___x_3783_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3776_, v_chunk_3777_, v_incomplete_3778_);
v___x_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
v___x_3786_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3781_, v___x_3782_, v___x_3785_, v___f_3780_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object* v_stream_3787_, lean_object* v_chunk_3788_, lean_object* v_incomplete_3789_, lean_object* v_a_3790_){
_start:
{
uint8_t v_incomplete_boxed_3791_; lean_object* v_res_3792_; 
v_incomplete_boxed_3791_ = lean_unbox(v_incomplete_3789_);
v_res_3792_ = l_Std_Http_Body_Stream_send(v_stream_3787_, v_chunk_3788_, v_incomplete_boxed_3791_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object* v_x_3793_){
_start:
{
uint8_t v___y_3796_; 
if (lean_obj_tag(v_x_3793_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3808_; 
v_a_3800_ = lean_ctor_get(v_x_3793_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_x_3793_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3802_ = v_x_3793_;
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v_x_3793_);
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
lean_object* v_a_3809_; lean_object* v_pendingConsumer_3810_; 
v_a_3809_ = lean_ctor_get(v_x_3793_, 0);
lean_inc(v_a_3809_);
lean_dec_ref_known(v_x_3793_, 1);
v_pendingConsumer_3810_ = lean_ctor_get(v_a_3809_, 1);
lean_inc(v_pendingConsumer_3810_);
lean_dec(v_a_3809_);
if (lean_obj_tag(v_pendingConsumer_3810_) == 0)
{
uint8_t v___x_3811_; 
v___x_3811_ = 0;
v___y_3796_ = v___x_3811_;
goto v___jp_3795_;
}
else
{
uint8_t v___x_3812_; 
lean_dec_ref_known(v_pendingConsumer_3810_, 1);
v___x_3812_ = 1;
v___y_3796_ = v___x_3812_;
goto v___jp_3795_;
}
}
v___jp_3795_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3797_ = lean_box(v___y_3796_);
v___x_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
return v___x_3799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object* v_x_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_3813_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object* v_a_3817_){
_start:
{
lean_object* v___f_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___f_3819_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_3820_ = lean_unsigned_to_nat(0u);
v___x_3821_ = 0;
v___x_3822_ = lean_st_ref_get(v_a_3817_);
v___x_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
v___x_3825_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3820_, v___x_3821_, v___x_3824_, v___f_3819_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object* v_a_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_3826_);
lean_dec(v_a_3826_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object* v___y_3829_, lean_object* v_x_3830_){
_start:
{
if (lean_obj_tag(v_x_3830_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3840_; 
v_a_3832_ = lean_ctor_get(v_x_3830_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v_x_3830_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3834_ = v_x_3830_;
v_isShared_3835_ = v_isSharedCheck_3840_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v_x_3830_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3840_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
return v___x_3838_;
}
}
}
else
{
lean_object* v___x_3841_; 
lean_dec_ref_known(v_x_3830_, 1);
v___x_3841_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_3829_);
return v___x_3841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object* v___y_3842_, lean_object* v_x_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_3842_, v_x_3843_);
lean_dec(v___y_3842_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object* v___y_3846_){
_start:
{
lean_object* v___f_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
lean_inc(v___y_3846_);
v___f_3848_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3848_, 0, v___y_3846_);
v___x_3849_ = lean_unsigned_to_nat(0u);
v___x_3850_ = 0;
v___x_3851_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3846_);
v___x_3852_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3849_, v___x_3850_, v___x_3851_, v___f_3848_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_3853_);
lean_dec(v___y_3853_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object* v_stream_3857_){
_start:
{
lean_object* v___f_3859_; lean_object* v___x_3860_; 
v___f_3859_ = ((lean_object*)(l_Std_Http_Body_Stream_hasInterest___closed__0));
v___x_3860_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3857_, v___f_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object* v_stream_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Std_Http_Body_Stream_hasInterest(v_stream_3861_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object* v_lose_3864_, lean_object* v___y_3865_, uint8_t v___x_3866_, lean_object* v_promise_3867_, lean_object* v_x_3868_){
_start:
{
if (lean_obj_tag(v_x_3868_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3878_; 
lean_dec_ref(v_lose_3864_);
v_a_3870_ = lean_ctor_get(v_x_3868_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_x_3868_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3872_ = v_x_3868_;
v_isShared_3873_ = v_isSharedCheck_3878_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v_x_3868_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3878_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
return v___x_3876_;
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3892_; 
v_a_3879_ = lean_ctor_get(v_x_3868_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_x_3868_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3881_ = v_x_3868_;
v_isShared_3882_ = v_isSharedCheck_3892_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v_x_3868_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3892_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
uint8_t v___x_3883_; 
v___x_3883_ = lean_unbox(v_a_3879_);
lean_dec(v_a_3879_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
lean_del_object(v___x_3881_);
lean_inc(v___y_3865_);
v___x_3884_ = lean_apply_2(v_lose_3864_, v___y_3865_, lean_box(0));
return v___x_3884_;
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3887_; 
lean_dec_ref(v_lose_3864_);
v___x_3885_ = lean_box(v___x_3866_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v___x_3885_);
v___x_3887_ = v___x_3881_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3888_ = lean_io_promise_resolve(v___x_3887_, v_promise_3867_);
v___x_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
v___x_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
return v___x_3890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object* v_lose_3893_, lean_object* v___y_3894_, lean_object* v___x_3895_, lean_object* v_promise_3896_, lean_object* v_x_3897_, lean_object* v___y_3898_){
_start:
{
uint8_t v___x_4067__boxed_3899_; lean_object* v_res_3900_; 
v___x_4067__boxed_3899_ = lean_unbox(v___x_3895_);
v_res_3900_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_3893_, v___y_3894_, v___x_4067__boxed_3899_, v_promise_3896_, v_x_3897_);
lean_dec(v_promise_3896_);
lean_dec(v___y_3894_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_3901_, lean_object* v_lose_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_finished_3905_; lean_object* v_promise_3906_; uint8_t v___x_3907_; lean_object* v___x_3908_; lean_object* v___f_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; uint8_t v___y_3913_; uint8_t v___x_3921_; 
v_finished_3905_ = lean_ctor_get(v_w_3901_, 0);
lean_inc(v_finished_3905_);
v_promise_3906_ = lean_ctor_get(v_w_3901_, 1);
lean_inc(v_promise_3906_);
lean_dec_ref(v_w_3901_);
v___x_3907_ = 0;
v___x_3908_ = lean_box(v___x_3907_);
lean_inc(v___y_3903_);
v___f_3909_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3909_, 0, v_lose_3902_);
lean_closure_set(v___f_3909_, 1, v___y_3903_);
lean_closure_set(v___f_3909_, 2, v___x_3908_);
lean_closure_set(v___f_3909_, 3, v_promise_3906_);
v___x_3910_ = lean_unsigned_to_nat(0u);
v___x_3911_ = lean_st_ref_take(v_finished_3905_);
v___x_3921_ = lean_unbox(v___x_3911_);
lean_dec(v___x_3911_);
if (v___x_3921_ == 0)
{
uint8_t v___x_3922_; 
v___x_3922_ = 1;
v___y_3913_ = v___x_3922_;
goto v___jp_3912_;
}
else
{
v___y_3913_ = v___x_3907_;
goto v___jp_3912_;
}
v___jp_3912_:
{
uint8_t v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3914_ = 1;
v___x_3915_ = lean_box(v___x_3914_);
v___x_3916_ = lean_st_ref_put(v_finished_3905_, v___x_3915_);
lean_dec(v_finished_3905_);
v___x_3917_ = lean_box(v___y_3913_);
v___x_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
v___x_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
v___x_3920_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3910_, v___x_3907_, v___x_3919_, v___f_3909_);
return v___x_3920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object* v_w_3923_, lean_object* v_lose_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_3923_, v_lose_3924_, v___y_3925_);
lean_dec(v___y_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object* v_w_3928_, lean_object* v_lose_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_finished_3932_; lean_object* v_promise_3933_; uint8_t v___x_3934_; lean_object* v___x_3935_; lean_object* v___f_3936_; lean_object* v___x_3937_; uint8_t v___x_3938_; lean_object* v___x_3939_; uint8_t v___y_3941_; uint8_t v___x_3948_; 
v_finished_3932_ = lean_ctor_get(v_w_3928_, 0);
lean_inc(v_finished_3932_);
v_promise_3933_ = lean_ctor_get(v_w_3928_, 1);
lean_inc(v_promise_3933_);
lean_dec_ref(v_w_3928_);
v___x_3934_ = 1;
v___x_3935_ = lean_box(v___x_3934_);
lean_inc(v___y_3930_);
v___f_3936_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3936_, 0, v_lose_3929_);
lean_closure_set(v___f_3936_, 1, v___y_3930_);
lean_closure_set(v___f_3936_, 2, v___x_3935_);
lean_closure_set(v___f_3936_, 3, v_promise_3933_);
v___x_3937_ = lean_unsigned_to_nat(0u);
v___x_3938_ = 0;
v___x_3939_ = lean_st_ref_take(v_finished_3932_);
v___x_3948_ = lean_unbox(v___x_3939_);
lean_dec(v___x_3939_);
if (v___x_3948_ == 0)
{
v___y_3941_ = v___x_3934_;
goto v___jp_3940_;
}
else
{
v___y_3941_ = v___x_3938_;
goto v___jp_3940_;
}
v___jp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3942_ = lean_box(v___x_3934_);
v___x_3943_ = lean_st_ref_put(v_finished_3932_, v___x_3942_);
lean_dec(v_finished_3932_);
v___x_3944_ = lean_box(v___y_3941_);
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
v___x_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
v___x_3947_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3937_, v___x_3938_, v___x_3946_, v___f_3936_);
return v___x_3947_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_3949_, lean_object* v_lose_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_3949_, v_lose_3950_, v___y_3951_);
lean_dec(v___y_3951_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_3970_){
_start:
{
if (lean_obj_tag(v_x_3970_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3980_; 
v_a_3972_ = lean_ctor_get(v_x_3970_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_x_3970_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3974_ = v_x_3970_;
v_isShared_3975_ = v_isSharedCheck_3980_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v_x_3970_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3980_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3978_; 
v___x_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
return v___x_3978_;
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v_pendingConsumer_3982_; 
v_a_3981_ = lean_ctor_get(v_x_3970_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v_x_3970_, 1);
v_pendingConsumer_3982_ = lean_ctor_get(v_a_3981_, 1);
if (lean_obj_tag(v_pendingConsumer_3982_) == 0)
{
uint8_t v_closed_3983_; 
v_closed_3983_ = lean_ctor_get_uint8(v_a_3981_, sizeof(void*)*6);
lean_dec(v_a_3981_);
if (v_closed_3983_ == 0)
{
lean_object* v___x_3984_; 
v___x_3984_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_3984_;
}
else
{
lean_object* v___x_3985_; 
v___x_3985_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_3985_;
}
}
else
{
lean_object* v___x_3986_; 
lean_dec(v_a_3981_);
v___x_3986_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_3986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_3987_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_3997_, lean_object* v___y_3998_, lean_object* v_x_3999_){
_start:
{
if (lean_obj_tag(v_x_3999_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v_waiter_3997_);
v_a_4001_ = lean_ctor_get(v_x_3999_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_x_3999_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4003_ = v_x_3999_;
v_isShared_4004_ = v_isSharedCheck_4009_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v_x_3999_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4009_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4007_; 
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
return v___x_4007_;
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v_pendingConsumer_4011_; 
v_a_4010_ = lean_ctor_get(v_x_3999_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v_x_3999_, 1);
v_pendingConsumer_4011_ = lean_ctor_get(v_a_4010_, 1);
lean_inc(v_pendingConsumer_4011_);
if (lean_obj_tag(v_pendingConsumer_4011_) == 0)
{
uint8_t v_closed_4012_; 
v_closed_4012_ = lean_ctor_get_uint8(v_a_4010_, sizeof(void*)*6);
if (v_closed_4012_ == 0)
{
lean_object* v_interestWaiter_4013_; 
v_interestWaiter_4013_ = lean_ctor_get(v_a_4010_, 2);
if (lean_obj_tag(v_interestWaiter_4013_) == 0)
{
lean_object* v_pendingProducer_4014_; lean_object* v_knownSize_4015_; lean_object* v_pendingIncompleteChunk_4016_; lean_object* v_closeError_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4027_; 
v_pendingProducer_4014_ = lean_ctor_get(v_a_4010_, 0);
v_knownSize_4015_ = lean_ctor_get(v_a_4010_, 3);
v_pendingIncompleteChunk_4016_ = lean_ctor_get(v_a_4010_, 4);
v_closeError_4017_ = lean_ctor_get(v_a_4010_, 5);
v_isSharedCheck_4027_ = !lean_is_exclusive(v_a_4010_);
if (v_isSharedCheck_4027_ == 0)
{
lean_object* v_unused_4028_; lean_object* v_unused_4029_; 
v_unused_4028_ = lean_ctor_get(v_a_4010_, 2);
lean_dec(v_unused_4028_);
v_unused_4029_ = lean_ctor_get(v_a_4010_, 1);
lean_dec(v_unused_4029_);
v___x_4019_ = v_a_4010_;
v_isShared_4020_ = v_isSharedCheck_4027_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_closeError_4017_);
lean_inc(v_pendingIncompleteChunk_4016_);
lean_inc(v_knownSize_4015_);
lean_inc(v_pendingProducer_4014_);
lean_dec(v_a_4010_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4027_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4021_, 0, v_waiter_3997_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 2, v___x_4021_);
v___x_4023_ = v___x_4019_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_pendingProducer_4014_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v_pendingConsumer_4011_);
lean_ctor_set(v_reuseFailAlloc_4026_, 2, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4026_, 3, v_knownSize_4015_);
lean_ctor_set(v_reuseFailAlloc_4026_, 4, v_pendingIncompleteChunk_4016_);
lean_ctor_set(v_reuseFailAlloc_4026_, 5, v_closeError_4017_);
lean_ctor_set_uint8(v_reuseFailAlloc_4026_, sizeof(void*)*6, v_closed_4012_);
v___x_4023_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = lean_st_ref_swap(v___y_3998_, v___x_4023_);
lean_dec(v___x_4024_);
v___x_4025_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4025_;
}
}
}
else
{
lean_object* v___x_4030_; 
lean_dec(v_a_4010_);
lean_dec_ref(v_waiter_3997_);
v___x_4030_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_4030_;
}
}
else
{
lean_object* v___f_4031_; lean_object* v___x_4032_; 
lean_dec(v_a_4010_);
v___f_4031_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4032_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_3997_, v___f_4031_, v___y_3998_);
return v___x_4032_;
}
}
else
{
lean_object* v___f_4033_; lean_object* v___x_4034_; 
lean_dec_ref_known(v_pendingConsumer_4011_, 1);
lean_dec(v_a_4010_);
v___f_4033_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4034_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_3997_, v___f_4033_, v___y_3998_);
return v___x_4034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_4035_, lean_object* v___y_4036_, lean_object* v_x_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_4035_, v___y_4036_, v_x_4037_);
lean_dec(v___y_4036_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_4040_, lean_object* v___f_4041_, lean_object* v_x_4042_){
_start:
{
if (lean_obj_tag(v_x_4042_) == 0)
{
lean_object* v___x_4044_; 
lean_dec_ref(v___f_4041_);
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v_x_4042_);
return v___x_4044_;
}
else
{
lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4056_; 
v_isSharedCheck_4056_ = !lean_is_exclusive(v_x_4042_);
if (v_isSharedCheck_4056_ == 0)
{
lean_object* v_unused_4057_; 
v_unused_4057_ = lean_ctor_get(v_x_4042_, 0);
lean_dec(v_unused_4057_);
v___x_4046_ = v_x_4042_;
v_isShared_4047_ = v_isSharedCheck_4056_;
goto v_resetjp_4045_;
}
else
{
lean_dec(v_x_4042_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4056_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4048_; uint8_t v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4052_; 
v___x_4048_ = lean_unsigned_to_nat(0u);
v___x_4049_ = 0;
v___x_4050_ = lean_st_ref_get(v___y_4040_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 0, v___x_4050_);
v___x_4052_ = v___x_4046_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
v___x_4054_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4048_, v___x_4049_, v___x_4053_, v___f_4041_);
return v___x_4054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_4058_, lean_object* v___f_4059_, lean_object* v_x_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_4058_, v___f_4059_, v_x_4060_);
lean_dec(v___y_4058_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v___f_4066_; lean_object* v___f_4067_; lean_object* v___x_4068_; uint8_t v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_inc_n(v___y_4064_, 2);
v___f_4066_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_4066_, 0, v_waiter_4063_);
lean_closure_set(v___f_4066_, 1, v___y_4064_);
v___f_4067_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4067_, 0, v___y_4064_);
lean_closure_set(v___f_4067_, 1, v___f_4066_);
v___x_4068_ = lean_unsigned_to_nat(0u);
v___x_4069_ = 0;
v___x_4070_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4064_);
v___x_4071_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4068_, v___x_4069_, v___x_4070_, v___f_4067_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_4072_, v___y_4073_);
lean_dec(v___y_4073_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_4076_, lean_object* v_waiter_4077_){
_start:
{
lean_object* v___f_4079_; lean_object* v___x_4080_; 
v___f_4079_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4079_, 0, v_waiter_4077_);
v___x_4080_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_4076_, v___f_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_4081_, lean_object* v_waiter_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_4081_, v_waiter_4082_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_4085_, lean_object* v___f_4086_, lean_object* v_x_4087_){
_start:
{
if (lean_obj_tag(v_x_4087_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4097_; 
lean_dec_ref(v___f_4086_);
v_a_4089_ = lean_ctor_get(v_x_4087_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4091_ = v_x_4087_;
v_isShared_4092_ = v_isSharedCheck_4097_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v_x_4087_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4097_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
lean_object* v___x_4095_; 
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
return v___x_4095_;
}
}
}
else
{
lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4109_; 
v_isSharedCheck_4109_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4109_ == 0)
{
lean_object* v_unused_4110_; 
v_unused_4110_ = lean_ctor_get(v_x_4087_, 0);
lean_dec(v_unused_4110_);
v___x_4099_ = v_x_4087_;
v_isShared_4100_ = v_isSharedCheck_4109_;
goto v_resetjp_4098_;
}
else
{
lean_dec(v_x_4087_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4109_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4101_; uint8_t v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
v___x_4101_ = lean_unsigned_to_nat(0u);
v___x_4102_ = 0;
v___x_4103_ = lean_st_ref_get(v___y_4085_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___x_4103_);
v___x_4105_ = v___x_4099_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4103_);
v___x_4105_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
v___x_4107_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4101_, v___x_4102_, v___x_4106_, v___f_4086_);
return v___x_4107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_4111_, lean_object* v___f_4112_, lean_object* v_x_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_4111_, v___f_4112_, v_x_4113_);
lean_dec(v___y_4111_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___f_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_inc(v___y_4117_);
v___f_4119_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_4119_, 0, v___y_4117_);
lean_closure_set(v___f_4119_, 1, v___f_4116_);
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = 0;
v___x_4122_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4117_);
v___x_4123_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4120_, v___x_4121_, v___x_4122_, v___f_4119_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_4124_, v___y_4125_);
lean_dec(v___y_4125_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_4131_){
_start:
{
lean_object* v___f_4132_; lean_object* v___f_4133_; lean_object* v___f_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___f_4132_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_4131_, 2);
v___f_4133_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_4133_, 0, v_stream_4131_);
v___f_4134_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_4135_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4135_, 0, lean_box(0));
lean_closure_set(v___x_4135_, 1, lean_box(0));
lean_closure_set(v___x_4135_, 2, v_stream_4131_);
lean_closure_set(v___x_4135_, 3, v___f_4134_);
v___x_4136_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4136_, 0, lean_box(0));
lean_closure_set(v___x_4136_, 1, lean_box(0));
lean_closure_set(v___x_4136_, 2, v_stream_4131_);
lean_closure_set(v___x_4136_, 3, v___f_4132_);
v___x_4137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4135_);
lean_ctor_set(v___x_4137_, 1, v___f_4133_);
lean_ctor_set(v___x_4137_, 2, v___x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v_x_4138_, lean_object* v_x_4139_){
_start:
{
if (lean_obj_tag(v_x_4139_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4149_; 
lean_dec_ref(v_x_4138_);
v_a_4141_ = lean_ctor_get(v_x_4139_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v_x_4139_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4143_ = v_x_4139_;
v_isShared_4144_ = v_isSharedCheck_4149_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v_x_4139_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4149_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
lean_object* v___x_4147_; 
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
return v___x_4147_;
}
}
}
else
{
lean_object* v___x_4150_; 
lean_dec_ref_known(v_x_4139_, 1);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v_x_4138_);
return v___x_4150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0___boxed(lean_object* v_x_4151_, lean_object* v_x_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Std_Http_Body_stream___lam__0(v_x_4151_, v_x_4152_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_a_4155_, lean_object* v_x_4156_){
_start:
{
if (lean_obj_tag(v_x_4156_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4159_; 
v_a_4158_ = lean_ctor_get(v_x_4156_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v_x_4156_, 1);
v___x_4159_ = l_Std_Http_Body_Stream_closeWithError(v_a_4155_, v_a_4158_);
return v___x_4159_;
}
else
{
lean_object* v___x_4160_; 
lean_dec_ref(v_a_4155_);
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v_x_4156_);
return v___x_4160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_a_4161_, lean_object* v_x_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Std_Http_Body_stream___lam__1(v_a_4161_, v_x_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v_a_4165_, lean_object* v_x_4166_){
_start:
{
if (lean_obj_tag(v_x_4166_) == 0)
{
lean_object* v___x_4168_; 
lean_dec_ref(v_a_4165_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v_x_4166_);
return v___x_4168_;
}
else
{
lean_object* v___x_4169_; 
lean_dec_ref_known(v_x_4166_, 1);
v___x_4169_ = l_Std_Http_Body_Stream_close(v_a_4165_);
return v___x_4169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v_a_4170_, lean_object* v_x_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l_Std_Http_Body_stream___lam__2(v_a_4170_, v_x_4171_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_gen_4174_, lean_object* v_a_4175_, lean_object* v___x_4176_, uint8_t v___x_4177_, lean_object* v___f_4178_, lean_object* v___f_4179_){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4181_ = lean_apply_2(v_gen_4174_, v_a_4175_, lean_box(0));
lean_inc(v___x_4176_);
v___x_4182_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4176_, v___x_4177_, v___x_4181_, v___f_4178_);
v___x_4183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4176_, v___x_4177_, v___x_4182_, v___f_4179_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_gen_4184_, lean_object* v_a_4185_, lean_object* v___x_4186_, lean_object* v___x_4187_, lean_object* v___f_4188_, lean_object* v___f_4189_, lean_object* v___y_4190_){
_start:
{
uint8_t v___x_1066__boxed_4191_; lean_object* v_res_4192_; 
v___x_1066__boxed_4191_ = lean_unbox(v___x_4187_);
v_res_4192_ = l_Std_Http_Body_stream___lam__3(v_gen_4184_, v_a_4185_, v___x_4186_, v___x_1066__boxed_4191_, v___f_4188_, v___f_4189_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_4193_, lean_object* v_a_4194_, lean_object* v___f_4195_, lean_object* v___f_4196_, lean_object* v___f_4197_, lean_object* v_x_4198_){
_start:
{
if (lean_obj_tag(v_x_4198_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4208_; 
lean_dec_ref(v___f_4197_);
lean_dec_ref(v___f_4196_);
lean_dec_ref(v___f_4195_);
lean_dec_ref(v_a_4194_);
lean_dec_ref(v_gen_4193_);
v_a_4200_ = lean_ctor_get(v_x_4198_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v_x_4198_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4202_ = v_x_4198_;
v_isShared_4203_ = v_isSharedCheck_4208_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v_x_4198_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4208_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
lean_object* v___x_4206_; 
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
return v___x_4206_;
}
}
}
else
{
lean_object* v___x_4209_; uint8_t v___x_4210_; lean_object* v___x_4211_; lean_object* v___f_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
lean_dec_ref_known(v_x_4198_, 1);
v___x_4209_ = lean_unsigned_to_nat(0u);
v___x_4210_ = 0;
v___x_4211_ = lean_box(v___x_4210_);
v___f_4212_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 7, 6);
lean_closure_set(v___f_4212_, 0, v_gen_4193_);
lean_closure_set(v___f_4212_, 1, v_a_4194_);
lean_closure_set(v___f_4212_, 2, v___x_4209_);
lean_closure_set(v___f_4212_, 3, v___x_4211_);
lean_closure_set(v___f_4212_, 4, v___f_4195_);
lean_closure_set(v___f_4212_, 5, v___f_4196_);
v___x_4213_ = lean_io_as_task(v___f_4212_, v___x_4209_);
lean_dec_ref(v___x_4213_);
v___x_4214_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4215_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4209_, v___x_4210_, v___x_4214_, v___f_4197_);
return v___x_4215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_4216_, lean_object* v_a_4217_, lean_object* v___f_4218_, lean_object* v___f_4219_, lean_object* v___f_4220_, lean_object* v_x_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Std_Http_Body_stream___lam__4(v_gen_4216_, v_a_4217_, v___f_4218_, v___f_4219_, v___f_4220_, v_x_4221_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5(lean_object* v___x_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v___x_4227_; lean_object* v_pendingProducer_4228_; lean_object* v_pendingConsumer_4229_; lean_object* v_interestWaiter_4230_; uint8_t v_closed_4231_; lean_object* v_pendingIncompleteChunk_4232_; lean_object* v_closeError_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4242_; 
v___x_4227_ = lean_st_ref_take(v___y_4225_);
v_pendingProducer_4228_ = lean_ctor_get(v___x_4227_, 0);
v_pendingConsumer_4229_ = lean_ctor_get(v___x_4227_, 1);
v_interestWaiter_4230_ = lean_ctor_get(v___x_4227_, 2);
v_closed_4231_ = lean_ctor_get_uint8(v___x_4227_, sizeof(void*)*6);
v_pendingIncompleteChunk_4232_ = lean_ctor_get(v___x_4227_, 4);
v_closeError_4233_ = lean_ctor_get(v___x_4227_, 5);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4242_ == 0)
{
lean_object* v_unused_4243_; 
v_unused_4243_ = lean_ctor_get(v___x_4227_, 3);
lean_dec(v_unused_4243_);
v___x_4235_ = v___x_4227_;
v_isShared_4236_ = v_isSharedCheck_4242_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_closeError_4233_);
lean_inc(v_pendingIncompleteChunk_4232_);
lean_inc(v_interestWaiter_4230_);
lean_inc(v_pendingConsumer_4229_);
lean_inc(v_pendingProducer_4228_);
lean_dec(v___x_4227_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4242_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 3, v___x_4224_);
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_pendingProducer_4228_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v_pendingConsumer_4229_);
lean_ctor_set(v_reuseFailAlloc_4241_, 2, v_interestWaiter_4230_);
lean_ctor_set(v_reuseFailAlloc_4241_, 3, v___x_4224_);
lean_ctor_set(v_reuseFailAlloc_4241_, 4, v_pendingIncompleteChunk_4232_);
lean_ctor_set(v_reuseFailAlloc_4241_, 5, v_closeError_4233_);
lean_ctor_set_uint8(v_reuseFailAlloc_4241_, sizeof(void*)*6, v_closed_4231_);
v___x_4238_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = lean_st_ref_put(v___y_4225_, v___x_4238_);
v___x_4240_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object* v___x_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Std_Http_Body_stream___lam__5(v___x_4244_, v___y_4245_);
lean_dec(v___y_4245_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6(lean_object* v_gen_4252_, lean_object* v_x_4253_){
_start:
{
if (lean_obj_tag(v_x_4253_) == 0)
{
lean_object* v___x_4255_; 
lean_dec_ref(v_gen_4252_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v_x_4253_);
return v___x_4255_;
}
else
{
lean_object* v_a_4256_; lean_object* v___f_4257_; lean_object* v___f_4258_; lean_object* v___f_4259_; lean_object* v___f_4260_; lean_object* v___f_4261_; lean_object* v___x_4262_; uint8_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v_a_4256_ = lean_ctor_get(v_x_4253_, 0);
lean_inc_n(v_a_4256_, 4);
v___f_4257_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4257_, 0, v_x_4253_);
v___f_4258_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4258_, 0, v_a_4256_);
v___f_4259_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4259_, 0, v_a_4256_);
v___f_4260_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 7, 5);
lean_closure_set(v___f_4260_, 0, v_gen_4252_);
lean_closure_set(v___f_4260_, 1, v_a_4256_);
lean_closure_set(v___f_4260_, 2, v___f_4259_);
lean_closure_set(v___f_4260_, 3, v___f_4258_);
lean_closure_set(v___f_4260_, 4, v___f_4257_);
v___f_4261_ = ((lean_object*)(l_Std_Http_Body_stream___lam__6___closed__1));
v___x_4262_ = lean_unsigned_to_nat(0u);
v___x_4263_ = 0;
v___x_4264_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4256_, v___f_4261_);
v___x_4265_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4262_, v___x_4263_, v___x_4264_, v___f_4260_);
return v___x_4265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object* v_gen_4266_, lean_object* v_x_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Std_Http_Body_stream___lam__6(v_gen_4266_, v_x_4267_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object* v_gen_4270_){
_start:
{
lean_object* v___f_4272_; lean_object* v___x_4273_; uint8_t v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___f_4272_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4272_, 0, v_gen_4270_);
v___x_4273_ = lean_unsigned_to_nat(0u);
v___x_4274_ = 0;
v___x_4275_ = l_Std_Http_Body_mkStream();
v___x_4276_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4273_, v___x_4274_, v___x_4275_, v___f_4272_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_4277_, lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Std_Http_Body_stream(v_gen_4277_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v___x_4280_, lean_object* v_content_4281_, lean_object* v_s_4282_, lean_object* v_x_4283_){
_start:
{
if (lean_obj_tag(v_x_4283_) == 0)
{
lean_object* v___x_4285_; 
lean_dec_ref(v_s_4282_);
lean_dec_ref(v_content_4281_);
v___x_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4285_, 0, v_x_4283_);
return v___x_4285_;
}
else
{
lean_object* v___x_4286_; uint8_t v___x_4287_; 
lean_dec_ref_known(v_x_4283_, 1);
v___x_4286_ = lean_unsigned_to_nat(0u);
v___x_4287_ = lean_nat_dec_lt(v___x_4286_, v___x_4280_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4288_; 
lean_dec_ref(v_s_4282_);
lean_dec_ref(v_content_4281_);
v___x_4288_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4288_;
}
else
{
lean_object* v___x_4289_; uint8_t v___x_4290_; lean_object* v___x_4291_; 
v___x_4289_ = l_Std_Http_Chunk_ofByteArray(v_content_4281_);
v___x_4290_ = 0;
v___x_4291_ = l_Std_Http_Body_Stream_send(v_s_4282_, v___x_4289_, v___x_4290_);
return v___x_4291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v___x_4292_, lean_object* v_content_4293_, lean_object* v_s_4294_, lean_object* v_x_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Std_Http_Body_fromBytes___lam__0(v___x_4292_, v_content_4293_, v_s_4294_, v_x_4295_);
lean_dec(v___x_4292_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object* v_content_4298_, lean_object* v_s_4299_){
_start:
{
lean_object* v___x_4301_; lean_object* v___f_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___f_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4301_ = lean_byte_array_size(v_content_4298_);
lean_inc_ref(v_s_4299_);
v___f_4302_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4302_, 0, v___x_4301_);
lean_closure_set(v___f_4302_, 1, v_content_4298_);
lean_closure_set(v___f_4302_, 2, v_s_4299_);
v___x_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4301_);
v___x_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
v___f_4305_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4305_, 0, v___x_4304_);
v___x_4306_ = lean_unsigned_to_nat(0u);
v___x_4307_ = 0;
v___x_4308_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_4299_, v___f_4305_);
v___x_4309_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4306_, v___x_4307_, v___x_4308_, v___f_4302_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object* v_content_4310_, lean_object* v_s_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Std_Http_Body_fromBytes___lam__2(v_content_4310_, v_s_4311_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_4314_){
_start:
{
lean_object* v___f_4316_; lean_object* v___x_4317_; 
v___f_4316_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4316_, 0, v_content_4314_);
v___x_4317_ = l_Std_Http_Body_stream(v___f_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Std_Http_Body_fromBytes(v_content_4318_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1(lean_object* v_a_4321_, lean_object* v___f_4322_, lean_object* v_x_4323_){
_start:
{
if (lean_obj_tag(v_x_4323_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4333_; 
lean_dec_ref(v___f_4322_);
lean_dec_ref(v_a_4321_);
v_a_4325_ = lean_ctor_get(v_x_4323_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v_x_4323_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4327_ = v_x_4323_;
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v_x_4323_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
return v___x_4331_;
}
}
}
else
{
lean_object* v___x_4334_; uint8_t v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
lean_dec_ref_known(v_x_4323_, 1);
v___x_4334_ = lean_unsigned_to_nat(0u);
v___x_4335_ = 0;
v___x_4336_ = l_Std_Http_Body_Stream_close(v_a_4321_);
v___x_4337_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4334_, v___x_4335_, v___x_4336_, v___f_4322_);
return v___x_4337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1___boxed(lean_object* v_a_4338_, lean_object* v___f_4339_, lean_object* v_x_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Std_Http_Body_empty___lam__1(v_a_4338_, v___f_4339_, v_x_4340_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_x_4349_){
_start:
{
if (lean_obj_tag(v_x_4349_) == 0)
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v_x_4349_);
return v___x_4351_;
}
else
{
lean_object* v_a_4352_; lean_object* v___f_4353_; lean_object* v___f_4354_; lean_object* v___x_4355_; lean_object* v___f_4356_; uint8_t v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v_a_4352_ = lean_ctor_get(v_x_4349_, 0);
lean_inc_n(v_a_4352_, 2);
v___f_4353_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4353_, 0, v_x_4349_);
v___f_4354_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4354_, 0, v_a_4352_);
lean_closure_set(v___f_4354_, 1, v___f_4353_);
v___x_4355_ = lean_unsigned_to_nat(0u);
v___f_4356_ = ((lean_object*)(l_Std_Http_Body_empty___lam__2___closed__2));
v___x_4357_ = 0;
v___x_4358_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4352_, v___f_4356_);
v___x_4359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4355_, v___x_4357_, v___x_4358_, v___f_4354_);
return v___x_4359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_x_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_Std_Http_Body_empty___lam__2(v_x_4360_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___f_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___f_4365_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_4366_ = lean_unsigned_to_nat(0u);
v___x_4367_ = 0;
v___x_4368_ = l_Std_Http_Body_mkStream();
v___x_4369_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4366_, v___x_4367_, v___x_4368_, v___f_4365_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Std_Http_Body_empty();
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_4394_, lean_object* v_f_4395_){
_start:
{
lean_object* v_line_4396_; lean_object* v_body_4397_; lean_object* v_extensions_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4406_; 
v_line_4396_ = lean_ctor_get(v_f_4395_, 0);
v_body_4397_ = lean_ctor_get(v_f_4395_, 1);
v_extensions_4398_ = lean_ctor_get(v_f_4395_, 2);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_f_4395_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4400_ = v_f_4395_;
v_isShared_4401_ = v_isSharedCheck_4406_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_extensions_4398_);
lean_inc(v_body_4397_);
lean_inc(v_line_4396_);
lean_dec(v_f_4395_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4406_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4402_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4394_, v_body_4397_);
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 1, v___x_4402_);
v___x_4404_ = v___x_4400_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_line_4396_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v___x_4402_);
lean_ctor_set(v_reuseFailAlloc_4405_, 2, v_extensions_4398_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_4410_, lean_object* v_x_4411_){
_start:
{
if (lean_obj_tag(v_x_4411_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4421_; 
lean_dec_ref(v___x_4410_);
v_a_4413_ = lean_ctor_get(v_x_4411_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_x_4411_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4415_ = v_x_4411_;
v_isShared_4416_ = v_isSharedCheck_4421_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v_x_4411_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4421_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; 
v___x_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
return v___x_4419_;
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4441_; 
v_a_4422_ = lean_ctor_get(v_x_4411_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v_x_4411_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4424_ = v_x_4411_;
v_isShared_4425_ = v_isSharedCheck_4441_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v_x_4411_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4441_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v_line_4426_; lean_object* v_body_4427_; lean_object* v_extensions_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4440_; 
v_line_4426_ = lean_ctor_get(v_a_4422_, 0);
v_body_4427_ = lean_ctor_get(v_a_4422_, 1);
v_extensions_4428_ = lean_ctor_get(v_a_4422_, 2);
v_isSharedCheck_4440_ = !lean_is_exclusive(v_a_4422_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4430_ = v_a_4422_;
v_isShared_4431_ = v_isSharedCheck_4440_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_extensions_4428_);
lean_inc(v_body_4427_);
lean_inc(v_line_4426_);
lean_dec(v_a_4422_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4440_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4432_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4410_, v_body_4427_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 1, v___x_4432_);
v___x_4434_ = v___x_4430_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_line_4426_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4439_, 2, v_extensions_4428_);
v___x_4434_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4436_; 
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4434_);
v___x_4436_ = v___x_4424_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4434_);
v___x_4436_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; 
v___x_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4436_);
return v___x_4437_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_4442_, lean_object* v_x_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_4442_, v_x_4443_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_4446_, lean_object* v_action_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v___x_4450_; uint8_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4450_ = lean_unsigned_to_nat(0u);
v___x_4451_ = 0;
lean_inc_ref(v___y_4448_);
v___x_4452_ = lean_apply_2(v_action_4447_, v___y_4448_, lean_box(0));
v___x_4453_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4450_, v___x_4451_, v___x_4452_, v___f_4446_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_4454_, lean_object* v_action_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_4454_, v_action_4455_, v___y_4456_);
lean_dec_ref(v___y_4456_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_4464_, lean_object* v_action_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v___x_4468_; uint8_t v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4468_ = lean_unsigned_to_nat(0u);
v___x_4469_ = 0;
v___x_4470_ = lean_apply_1(v_action_4465_, lean_box(0));
v___x_4471_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4468_, v___x_4469_, v___x_4470_, v___f_4464_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_4472_, lean_object* v_action_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_4472_, v_action_4473_, v___y_4474_);
lean_dec_ref(v___y_4474_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_4480_, lean_object* v_x_4481_){
_start:
{
if (lean_obj_tag(v_x_4481_) == 0)
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4491_; 
v_a_4483_ = lean_ctor_get(v_x_4481_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v_x_4481_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4485_ = v_x_4481_;
v_isShared_4486_ = v_isSharedCheck_4491_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v_x_4481_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4491_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
lean_object* v___x_4489_; 
v___x_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
return v___x_4489_;
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4501_; 
v_a_4492_ = lean_ctor_get(v_x_4481_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_x_4481_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4494_ = v_x_4481_;
v_isShared_4495_ = v_isSharedCheck_4501_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v_x_4481_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4501_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4496_ = l_Std_Http_Request_Builder_body___redArg(v_builder_4480_, v_a_4492_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4496_);
v___x_4498_ = v___x_4494_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4499_; 
v___x_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
return v___x_4499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_4502_, lean_object* v_x_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_4502_, v_x_4503_);
lean_dec_ref(v_builder_4502_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_4506_, lean_object* v_gen_4507_){
_start:
{
lean_object* v___f_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___f_4509_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4509_, 0, v_builder_4506_);
v___x_4510_ = lean_unsigned_to_nat(0u);
v___x_4511_ = 0;
v___x_4512_ = l_Std_Http_Body_stream(v_gen_4507_);
v___x_4513_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4510_, v___x_4511_, v___x_4512_, v___f_4509_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_4514_, lean_object* v_gen_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Std_Http_Request_Builder_stream(v_builder_4514_, v_gen_4515_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_4518_, lean_object* v_x_4519_){
_start:
{
if (lean_obj_tag(v_x_4519_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4529_; 
v_a_4521_ = lean_ctor_get(v_x_4519_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v_x_4519_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4523_ = v_x_4519_;
v_isShared_4524_ = v_isSharedCheck_4529_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v_x_4519_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4529_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
lean_object* v___x_4527_; 
v___x_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
return v___x_4527_;
}
}
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4539_; 
v_a_4530_ = lean_ctor_get(v_x_4519_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_x_4519_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4532_ = v_x_4519_;
v_isShared_4533_ = v_isSharedCheck_4539_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v_x_4519_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4539_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4534_; lean_object* v___x_4536_; 
v___x_4534_ = l_Std_Http_Response_Builder_body___redArg(v_builder_4518_, v_a_4530_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4534_);
v___x_4536_ = v___x_4532_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
lean_object* v___x_4537_; 
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
return v___x_4537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_4540_, lean_object* v_x_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_4540_, v_x_4541_);
lean_dec_ref(v_builder_4540_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_4544_, lean_object* v_gen_4545_){
_start:
{
lean_object* v___f_4547_; lean_object* v___x_4548_; uint8_t v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___f_4547_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4547_, 0, v_builder_4544_);
v___x_4548_ = lean_unsigned_to_nat(0u);
v___x_4549_ = 0;
v___x_4550_ = l_Std_Http_Body_stream(v_gen_4545_);
v___x_4551_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4548_, v___x_4549_, v___x_4550_, v___f_4547_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_4552_, lean_object* v_gen_4553_, lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Std_Http_Response_Builder_stream(v_builder_4552_, v_gen_4553_);
return v_res_4555_;
}
}
lean_object* runtime_initialize_Std_Sync(uint8_t builtin);
lean_object* runtime_initialize_Std_Async(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Chunk(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Any(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
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
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
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
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
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
res = initialize_Init_Data_ByteArray_Basic(builtin);
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

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
uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(lean_object* v_x_39_, lean_object* v_w_40_, lean_object* v_lose_41_){
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
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_39_ = stack[0].m_obj;
lean_object* v_w_40_ = stack[1].m_obj;
lean_object* v_lose_41_ = stack[2].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_39_, v_w_40_, v_lose_41_);
stack->m_num = v_res_57_;
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
uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(uint8_t v___x_64_){
_start:
{
return v___x_64_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_64_ = stack[0].m_num;
uint8_t v_res_66_;
v_res_66_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(v___x_64_);
stack->m_num = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed(lean_object* v___x_67_, lean_object* v___y_68_){
_start:
{
uint8_t v___x_326__boxed_69_; uint8_t v_res_70_; lean_object* v_r_71_; 
v___x_326__boxed_69_ = lean_unbox(v___x_67_);
v_res_70_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(v___x_326__boxed_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(lean_object* v_c_75_, lean_object* v_x_76_){
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
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_75_ = stack[0].m_obj;
lean_object* v_x_76_ = stack[1].m_obj;
uint8_t v_res_84_;
v_res_84_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_c_75_, v_x_76_);
stack->m_num = v_res_84_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed(lean_object* v_c_85_, lean_object* v_x_86_, lean_object* v_a_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_c_85_, v_x_86_);
lean_dec_ref(v_c_85_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(uint8_t v_x_90_, lean_object* v_w_91_, lean_object* v_lose_92_){
_start:
{
lean_object* v_finished_94_; lean_object* v_promise_95_; lean_object* v___x_96_; uint8_t v___y_98_; uint8_t v___x_107_; 
v_finished_94_ = lean_ctor_get(v_w_91_, 0);
v_promise_95_ = lean_ctor_get(v_w_91_, 1);
v___x_96_ = lean_st_ref_take(v_finished_94_);
v___x_107_ = lean_unbox(v___x_96_);
lean_dec(v___x_96_);
if (v___x_107_ == 0)
{
uint8_t v___x_108_; 
v___x_108_ = 1;
v___y_98_ = v___x_108_;
goto v___jp_97_;
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
v___y_98_ = v___x_109_;
goto v___jp_97_;
}
v___jp_97_:
{
uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = 1;
v___x_100_ = lean_box(v___x_99_);
v___x_101_ = lean_st_ref_put(v_finished_94_, v___x_100_);
if (v___y_98_ == 0)
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_apply_1(v_lose_92_, lean_box(0));
v___x_103_ = lean_unbox(v___x_102_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec_ref(v_lose_92_);
v___x_104_ = lean_box(v_x_90_);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
v___x_106_ = lean_io_promise_resolve(v___x_105_, v_promise_95_);
return v___y_98_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_90_ = stack[0].m_num;
lean_object* v_w_91_ = stack[1].m_obj;
lean_object* v_lose_92_ = stack[2].m_obj;
uint8_t v_res_110_;
v_res_110_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_90_, v_w_91_, v_lose_92_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0___boxed(lean_object* v_x_111_, lean_object* v_w_112_, lean_object* v_lose_113_, lean_object* v___y_114_){
_start:
{
uint8_t v_x_boxed_115_; uint8_t v_res_116_; lean_object* v_r_117_; 
v_x_boxed_115_ = lean_unbox(v_x_111_);
v_res_116_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_boxed_115_, v_w_112_, v_lose_113_);
lean_dec_ref(v_w_112_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(lean_object* v_waiter_118_, uint8_t v_x_119_){
_start:
{
lean_object* v_lose_121_; uint8_t v___x_122_; 
v_lose_121_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_122_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_119_, v_waiter_118_, v_lose_121_);
return v___x_122_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_118_ = stack[0].m_obj;
uint8_t v_x_119_ = stack[1].m_num;
uint8_t v_res_123_;
v_res_123_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_waiter_118_, v_x_119_);
stack->m_num = v_res_123_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed(lean_object* v_waiter_124_, lean_object* v_x_125_, lean_object* v_a_126_){
_start:
{
uint8_t v_x_boxed_127_; uint8_t v_res_128_; lean_object* v_r_129_; 
v_x_boxed_127_ = lean_unbox(v_x_125_);
v_res_128_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_waiter_124_, v_x_boxed_127_);
lean_dec_ref(v_waiter_124_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
lean_object* l_Std_Http_Body_mkStream___lam__0(lean_object* v_x_141_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_151_; 
v_a_143_ = lean_ctor_get(v_x_141_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_141_);
if (v_isSharedCheck_151_ == 0)
{
v___x_145_ = v_x_141_;
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v_x_141_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_150_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_160_; 
v_a_152_ = lean_ctor_get(v_x_141_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_141_);
if (v_isSharedCheck_160_ == 0)
{
v___x_154_ = v_x_141_;
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v_x_141_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_159_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; 
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_mkStream___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_141_ = stack[0].m_obj;
lean_object* v_res_161_;
v_res_161_ = l_Std_Http_Body_mkStream___lam__0(v_x_141_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0___boxed(lean_object* v_x_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Http_Body_mkStream___lam__0(v_x_162_);
return v_res_164_;
}
}
lean_object* l_Std_Http_Body_mkStream(){
_start:
{
lean_object* v___f_170_; uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___f_170_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__0));
v___x_171_ = 0;
v___x_172_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__1));
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = l_Std_Mutex_new___redArg(v___x_172_);
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
v___x_177_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_173_, v___x_171_, v___x_176_, v___f_170_);
return v___x_177_;
}
}
LEAN_EXPORT void l_Std_Http_Body_mkStream_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_178_;
v_res_178_ = l_Std_Http_Body_mkStream();
stack->m_obj
 = v_res_178_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___boxed(lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Http_Body_mkStream();
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object* v_knownSize_181_, lean_object* v_chunk_182_){
_start:
{
if (lean_obj_tag(v_knownSize_181_) == 1)
{
lean_object* v_val_183_; 
v_val_183_ = lean_ctor_get(v_knownSize_181_, 0);
lean_inc(v_val_183_);
if (lean_obj_tag(v_val_183_) == 1)
{
lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_201_; 
v_isSharedCheck_201_ = !lean_is_exclusive(v_knownSize_181_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; 
v_unused_202_ = lean_ctor_get(v_knownSize_181_, 0);
lean_dec(v_unused_202_);
v___x_185_ = v_knownSize_181_;
v_isShared_186_ = v_isSharedCheck_201_;
goto v_resetjp_184_;
}
else
{
lean_dec(v_knownSize_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_201_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_n_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_200_; 
v_n_187_ = lean_ctor_get(v_val_183_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_val_183_);
if (v_isSharedCheck_200_ == 0)
{
v___x_189_ = v_val_183_;
v_isShared_190_ = v_isSharedCheck_200_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_n_187_);
lean_dec(v_val_183_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_200_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_data_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v_data_191_ = lean_ctor_get(v_chunk_182_, 0);
v___x_192_ = lean_byte_array_size(v_data_191_);
v___x_193_ = lean_nat_sub(v_n_187_, v___x_192_);
lean_dec(v_n_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_193_);
v___x_195_ = v___x_189_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_195_);
v___x_197_ = v___x_185_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
else
{
lean_dec(v_val_183_);
return v_knownSize_181_;
}
}
else
{
return v_knownSize_181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object* v_knownSize_203_, lean_object* v_chunk_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_203_, v_chunk_204_);
lean_dec_ref(v_chunk_204_);
return v_res_205_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object* v_pendingProducer_206_, lean_object* v_pendingConsumer_207_, uint8_t v_closed_208_, lean_object* v_knownSize_209_, lean_object* v_pendingIncompleteChunk_210_, lean_object* v_closeError_211_, lean_object* v_inst_212_, lean_object* v_interestWaiter_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_215_, 0, v_pendingProducer_206_);
lean_ctor_set(v___x_215_, 1, v_pendingConsumer_207_);
lean_ctor_set(v___x_215_, 2, v_interestWaiter_213_);
lean_ctor_set(v___x_215_, 3, v_knownSize_209_);
lean_ctor_set(v___x_215_, 4, v_pendingIncompleteChunk_210_);
lean_ctor_set(v___x_215_, 5, v_closeError_211_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*6, v_closed_208_);
lean_inc(v___y_214_);
v___x_216_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_216_, 0, lean_box(0));
lean_closure_set(v___x_216_, 1, lean_box(0));
lean_closure_set(v___x_216_, 2, v___y_214_);
lean_closure_set(v___x_216_, 3, v___x_215_);
v___x_217_ = lean_apply_2(v_inst_212_, lean_box(0), v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingProducer_206_ = stack[0].m_obj;
lean_object* v_pendingConsumer_207_ = stack[1].m_obj;
uint8_t v_closed_208_ = stack[2].m_num;
lean_object* v_knownSize_209_ = stack[3].m_obj;
lean_object* v_pendingIncompleteChunk_210_ = stack[4].m_obj;
lean_object* v_closeError_211_ = stack[5].m_obj;
lean_object* v_inst_212_ = stack[6].m_obj;
lean_object* v_interestWaiter_213_ = stack[7].m_obj;
lean_object* v___y_214_ = stack[8].m_obj;
lean_object* v_res_218_;
v_res_218_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(v_pendingProducer_206_, v_pendingConsumer_207_, v_closed_208_, v_knownSize_209_, v_pendingIncompleteChunk_210_, v_closeError_211_, v_inst_212_, v_interestWaiter_213_, v___y_214_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object* v_pendingProducer_219_, lean_object* v_pendingConsumer_220_, lean_object* v_closed_221_, lean_object* v_knownSize_222_, lean_object* v_pendingIncompleteChunk_223_, lean_object* v_closeError_224_, lean_object* v_inst_225_, lean_object* v_interestWaiter_226_, lean_object* v___y_227_){
_start:
{
uint8_t v_closed_boxed_228_; lean_object* v_res_229_; 
v_closed_boxed_228_ = lean_unbox(v_closed_221_);
v_res_229_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(v_pendingProducer_219_, v_pendingConsumer_220_, v_closed_boxed_228_, v_knownSize_222_, v_pendingIncompleteChunk_223_, v_closeError_224_, v_inst_225_, v_interestWaiter_226_, v___y_227_);
lean_dec(v___y_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object* v___f_230_, lean_object* v___y_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
lean_inc(v___y_231_);
v___x_233_ = lean_apply_2(v___f_230_, v_a_232_, v___y_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object* v___f_234_, lean_object* v___y_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(v___f_234_, v___y_235_, v_a_236_);
lean_dec(v___y_235_);
return v_res_237_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object* v_toApplicative_238_, lean_object* v_interestWaiter_239_, lean_object* v_toBind_240_, lean_object* v___f_241_, lean_object* v___f_242_, uint8_t v_a_243_){
_start:
{
if (v_a_243_ == 0)
{
lean_object* v_toPure_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v___f_242_);
v_toPure_244_ = lean_ctor_get(v_toApplicative_238_, 1);
lean_inc(v_toPure_244_);
lean_dec_ref(v_toApplicative_238_);
v___x_245_ = lean_apply_2(v_toPure_244_, lean_box(0), v_interestWaiter_239_);
v___x_246_ = lean_apply_4(v_toBind_240_, lean_box(0), lean_box(0), v___x_245_, v___f_241_);
return v___x_246_;
}
else
{
lean_object* v_toPure_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v___f_241_);
lean_dec(v_interestWaiter_239_);
v_toPure_247_ = lean_ctor_get(v_toApplicative_238_, 1);
lean_inc(v_toPure_247_);
lean_dec_ref(v_toApplicative_238_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_apply_2(v_toPure_247_, lean_box(0), v___x_248_);
v___x_250_ = lean_apply_4(v_toBind_240_, lean_box(0), lean_box(0), v___x_249_, v___f_242_);
return v___x_250_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_238_ = stack[0].m_obj;
lean_object* v_interestWaiter_239_ = stack[1].m_obj;
lean_object* v_toBind_240_ = stack[2].m_obj;
lean_object* v___f_241_ = stack[3].m_obj;
lean_object* v___f_242_ = stack[4].m_obj;
uint8_t v_a_243_ = stack[5].m_num;
lean_object* v_res_251_;
v_res_251_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(v_toApplicative_238_, v_interestWaiter_239_, v_toBind_240_, v___f_241_, v___f_242_, v_a_243_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object* v_toApplicative_252_, lean_object* v_interestWaiter_253_, lean_object* v_toBind_254_, lean_object* v___f_255_, lean_object* v___f_256_, lean_object* v_a_257_){
_start:
{
uint8_t v_a_boxed_258_; lean_object* v_res_259_; 
v_a_boxed_258_ = lean_unbox(v_a_257_);
v_res_259_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(v_toApplicative_252_, v_interestWaiter_253_, v_toBind_254_, v___f_255_, v___f_256_, v_a_boxed_258_);
return v_res_259_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object* v_pendingProducer_260_, uint8_t v_closed_261_, lean_object* v_knownSize_262_, lean_object* v_pendingIncompleteChunk_263_, lean_object* v_closeError_264_, lean_object* v_inst_265_, lean_object* v_interestWaiter_266_, lean_object* v_toApplicative_267_, lean_object* v_toBind_268_, lean_object* v_pendingConsumer_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___f_272_; 
v___x_271_ = lean_box(v_closed_261_);
lean_inc(v_inst_265_);
v___f_272_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed), 9, 7);
lean_closure_set(v___f_272_, 0, v_pendingProducer_260_);
lean_closure_set(v___f_272_, 1, v_pendingConsumer_269_);
lean_closure_set(v___f_272_, 2, v___x_271_);
lean_closure_set(v___f_272_, 3, v_knownSize_262_);
lean_closure_set(v___f_272_, 4, v_pendingIncompleteChunk_263_);
lean_closure_set(v___f_272_, 5, v_closeError_264_);
lean_closure_set(v___f_272_, 6, v_inst_265_);
if (lean_obj_tag(v_interestWaiter_266_) == 0)
{
lean_object* v_toPure_273_; lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec(v_inst_265_);
v_toPure_273_ = lean_ctor_get(v_toApplicative_267_, 1);
lean_inc(v_toPure_273_);
lean_dec_ref(v_toApplicative_267_);
lean_inc(v___y_270_);
v___f_274_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_274_, 0, v___f_272_);
lean_closure_set(v___f_274_, 1, v___y_270_);
v___x_275_ = lean_apply_2(v_toPure_273_, lean_box(0), v_interestWaiter_266_);
v___x_276_ = lean_apply_4(v_toBind_268_, lean_box(0), lean_box(0), v___x_275_, v___f_274_);
return v___x_276_;
}
else
{
lean_object* v_val_277_; lean_object* v_finished_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_val_277_ = lean_ctor_get(v_interestWaiter_266_, 0);
v_finished_278_ = lean_ctor_get(v_val_277_, 0);
lean_inc(v_finished_278_);
lean_inc(v___y_270_);
v___f_279_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_279_, 0, v___f_272_);
lean_closure_set(v___f_279_, 1, v___y_270_);
lean_inc_ref(v___f_279_);
lean_inc(v_toBind_268_);
v___f_280_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_280_, 0, v_toApplicative_267_);
lean_closure_set(v___f_280_, 1, v_interestWaiter_266_);
lean_closure_set(v___f_280_, 2, v_toBind_268_);
lean_closure_set(v___f_280_, 3, v___f_279_);
lean_closure_set(v___f_280_, 4, v___f_279_);
v___x_281_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_281_, 0, lean_box(0));
lean_closure_set(v___x_281_, 1, lean_box(0));
lean_closure_set(v___x_281_, 2, v_finished_278_);
v___x_282_ = lean_apply_2(v_inst_265_, lean_box(0), v___x_281_);
v___x_283_ = lean_apply_4(v_toBind_268_, lean_box(0), lean_box(0), v___x_282_, v___f_280_);
return v___x_283_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingProducer_260_ = stack[0].m_obj;
uint8_t v_closed_261_ = stack[1].m_num;
lean_object* v_knownSize_262_ = stack[2].m_obj;
lean_object* v_pendingIncompleteChunk_263_ = stack[3].m_obj;
lean_object* v_closeError_264_ = stack[4].m_obj;
lean_object* v_inst_265_ = stack[5].m_obj;
lean_object* v_interestWaiter_266_ = stack[6].m_obj;
lean_object* v_toApplicative_267_ = stack[7].m_obj;
lean_object* v_toBind_268_ = stack[8].m_obj;
lean_object* v_pendingConsumer_269_ = stack[9].m_obj;
lean_object* v___y_270_ = stack[10].m_obj;
lean_object* v_res_284_;
v_res_284_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(v_pendingProducer_260_, v_closed_261_, v_knownSize_262_, v_pendingIncompleteChunk_263_, v_closeError_264_, v_inst_265_, v_interestWaiter_266_, v_toApplicative_267_, v_toBind_268_, v_pendingConsumer_269_, v___y_270_);
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object* v_pendingProducer_285_, lean_object* v_closed_286_, lean_object* v_knownSize_287_, lean_object* v_pendingIncompleteChunk_288_, lean_object* v_closeError_289_, lean_object* v_inst_290_, lean_object* v_interestWaiter_291_, lean_object* v_toApplicative_292_, lean_object* v_toBind_293_, lean_object* v_pendingConsumer_294_, lean_object* v___y_295_){
_start:
{
uint8_t v_closed_boxed_296_; lean_object* v_res_297_; 
v_closed_boxed_296_ = lean_unbox(v_closed_286_);
v_res_297_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(v_pendingProducer_285_, v_closed_boxed_296_, v_knownSize_287_, v_pendingIncompleteChunk_288_, v_closeError_289_, v_inst_290_, v_interestWaiter_291_, v_toApplicative_292_, v_toBind_293_, v_pendingConsumer_294_, v___y_295_);
lean_dec(v___y_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(lean_object* v___f_298_, lean_object* v___y_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_301_; 
lean_inc(v___y_299_);
v___x_301_ = lean_apply_2(v___f_298_, v_a_300_, v___y_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(lean_object* v___f_302_, lean_object* v___y_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(v___f_302_, v___y_303_, v_a_304_);
lean_dec(v___y_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(lean_object* v___f_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_309_; 
lean_inc(v_a_307_);
v___x_309_ = lean_apply_2(v___f_306_, v_a_308_, v_a_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(lean_object* v___f_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(v___f_310_, v_a_311_, v_a_312_);
lean_dec(v_a_311_);
return v_res_313_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(lean_object* v_toApplicative_314_, lean_object* v_pendingConsumer_315_, lean_object* v_toBind_316_, lean_object* v___f_317_, lean_object* v___f_318_, uint8_t v_a_319_){
_start:
{
if (v_a_319_ == 0)
{
lean_object* v_toPure_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v___f_318_);
v_toPure_320_ = lean_ctor_get(v_toApplicative_314_, 1);
lean_inc(v_toPure_320_);
lean_dec_ref(v_toApplicative_314_);
v___x_321_ = lean_apply_2(v_toPure_320_, lean_box(0), v_pendingConsumer_315_);
v___x_322_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_321_, v___f_317_);
return v___x_322_;
}
else
{
lean_object* v_toPure_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v___f_317_);
lean_dec(v_pendingConsumer_315_);
v_toPure_323_ = lean_ctor_get(v_toApplicative_314_, 1);
lean_inc(v_toPure_323_);
lean_dec_ref(v_toApplicative_314_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_apply_2(v_toPure_323_, lean_box(0), v___x_324_);
v___x_326_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_325_, v___f_318_);
return v___x_326_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_314_ = stack[0].m_obj;
lean_object* v_pendingConsumer_315_ = stack[1].m_obj;
lean_object* v_toBind_316_ = stack[2].m_obj;
lean_object* v___f_317_ = stack[3].m_obj;
lean_object* v___f_318_ = stack[4].m_obj;
uint8_t v_a_319_ = stack[5].m_num;
lean_object* v_res_327_;
v_res_327_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(v_toApplicative_314_, v_pendingConsumer_315_, v_toBind_316_, v___f_317_, v___f_318_, v_a_319_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(lean_object* v_toApplicative_328_, lean_object* v_pendingConsumer_329_, lean_object* v_toBind_330_, lean_object* v___f_331_, lean_object* v___f_332_, lean_object* v_a_333_){
_start:
{
uint8_t v_a_boxed_334_; lean_object* v_res_335_; 
v_a_boxed_334_ = lean_unbox(v_a_333_);
v_res_335_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(v_toApplicative_328_, v_pendingConsumer_329_, v_toBind_330_, v___f_331_, v___f_332_, v_a_boxed_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(lean_object* v_inst_336_, lean_object* v_toApplicative_337_, lean_object* v_toBind_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_pendingProducer_341_; lean_object* v_pendingConsumer_342_; lean_object* v_interestWaiter_343_; uint8_t v_closed_344_; lean_object* v_knownSize_345_; lean_object* v_pendingIncompleteChunk_346_; lean_object* v_closeError_347_; lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___y_351_; 
v_pendingProducer_341_ = lean_ctor_get(v_a_340_, 0);
lean_inc(v_pendingProducer_341_);
v_pendingConsumer_342_ = lean_ctor_get(v_a_340_, 1);
lean_inc(v_pendingConsumer_342_);
v_interestWaiter_343_ = lean_ctor_get(v_a_340_, 2);
lean_inc(v_interestWaiter_343_);
v_closed_344_ = lean_ctor_get_uint8(v_a_340_, sizeof(void*)*6);
v_knownSize_345_ = lean_ctor_get(v_a_340_, 3);
lean_inc(v_knownSize_345_);
v_pendingIncompleteChunk_346_ = lean_ctor_get(v_a_340_, 4);
lean_inc(v_pendingIncompleteChunk_346_);
v_closeError_347_ = lean_ctor_get(v_a_340_, 5);
lean_inc(v_closeError_347_);
lean_dec_ref(v_a_340_);
v___x_348_ = lean_box(v_closed_344_);
lean_inc(v_toBind_338_);
lean_inc_ref(v_toApplicative_337_);
lean_inc(v_inst_336_);
v___f_349_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_349_, 0, v_pendingProducer_341_);
lean_closure_set(v___f_349_, 1, v___x_348_);
lean_closure_set(v___f_349_, 2, v_knownSize_345_);
lean_closure_set(v___f_349_, 3, v_pendingIncompleteChunk_346_);
lean_closure_set(v___f_349_, 4, v_closeError_347_);
lean_closure_set(v___f_349_, 5, v_inst_336_);
lean_closure_set(v___f_349_, 6, v_interestWaiter_343_);
lean_closure_set(v___f_349_, 7, v_toApplicative_337_);
lean_closure_set(v___f_349_, 8, v_toBind_338_);
if (lean_obj_tag(v_pendingConsumer_342_) == 1)
{
lean_object* v_val_356_; 
v_val_356_ = lean_ctor_get(v_pendingConsumer_342_, 0);
if (lean_obj_tag(v_val_356_) == 1)
{
lean_object* v_finished_357_; lean_object* v_finished_358_; lean_object* v___f_359_; lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_finished_357_ = lean_ctor_get(v_val_356_, 0);
v_finished_358_ = lean_ctor_get(v_finished_357_, 0);
lean_inc(v_finished_358_);
lean_inc(v_a_339_);
v___f_359_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_359_, 0, v___f_349_);
lean_closure_set(v___f_359_, 1, v_a_339_);
lean_inc_ref(v___f_359_);
lean_inc(v_toBind_338_);
v___f_360_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_360_, 0, v_toApplicative_337_);
lean_closure_set(v___f_360_, 1, v_pendingConsumer_342_);
lean_closure_set(v___f_360_, 2, v_toBind_338_);
lean_closure_set(v___f_360_, 3, v___f_359_);
lean_closure_set(v___f_360_, 4, v___f_359_);
v___x_361_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_361_, 0, lean_box(0));
lean_closure_set(v___x_361_, 1, lean_box(0));
lean_closure_set(v___x_361_, 2, v_finished_358_);
v___x_362_ = lean_apply_2(v_inst_336_, lean_box(0), v___x_361_);
v___x_363_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_362_, v___f_360_);
return v___x_363_;
}
else
{
lean_dec(v_inst_336_);
v___y_351_ = v_a_339_;
goto v___jp_350_;
}
}
else
{
lean_dec(v_inst_336_);
v___y_351_ = v_a_339_;
goto v___jp_350_;
}
v___jp_350_:
{
lean_object* v_toPure_352_; lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_toPure_352_ = lean_ctor_get(v_toApplicative_337_, 1);
lean_inc(v_toPure_352_);
lean_dec_ref(v_toApplicative_337_);
lean_inc(v___y_351_);
v___f_353_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_353_, 0, v___f_349_);
lean_closure_set(v___f_353_, 1, v___y_351_);
v___x_354_ = lean_apply_2(v_toPure_352_, lean_box(0), v_pendingConsumer_342_);
v___x_355_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_354_, v___f_353_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(lean_object* v_inst_364_, lean_object* v_toApplicative_365_, lean_object* v_toBind_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(v_inst_364_, v_toApplicative_365_, v_toBind_366_, v_a_367_, v_a_368_);
lean_dec(v_a_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_toApplicative_373_; lean_object* v_toBind_374_; lean_object* v___f_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_toApplicative_373_ = lean_ctor_get(v_inst_370_, 0);
lean_inc_ref(v_toApplicative_373_);
v_toBind_374_ = lean_ctor_get(v_inst_370_, 1);
lean_inc_n(v_toBind_374_, 2);
lean_dec_ref(v_inst_370_);
lean_inc_n(v_a_372_, 2);
lean_inc(v_inst_371_);
v___f_375_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_375_, 0, v_inst_371_);
lean_closure_set(v___f_375_, 1, v_toApplicative_373_);
lean_closure_set(v___f_375_, 2, v_toBind_374_);
lean_closure_set(v___f_375_, 3, v_a_372_);
v___x_376_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_376_, 0, lean_box(0));
lean_closure_set(v___x_376_, 1, lean_box(0));
lean_closure_set(v___x_376_, 2, v_a_372_);
v___x_377_ = lean_apply_2(v_inst_371_, lean_box(0), v___x_376_);
v___x_378_ = lean_apply_4(v_toBind_374_, lean_box(0), lean_box(0), v___x_377_, v___f_375_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_379_, v_inst_380_, v_a_381_);
lean_dec(v_a_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(lean_object* v_m_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_384_, v_inst_385_, v_a_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(lean_object* v_m_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(v_m_388_, v_inst_389_, v_inst_390_, v_a_391_);
lean_dec(v_a_391_);
return v_res_392_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object* v_pendingProducer_393_, lean_object* v_pendingConsumer_394_, uint8_t v_closed_395_, lean_object* v_knownSize_396_, lean_object* v_pendingIncompleteChunk_397_, lean_object* v_closeError_398_, lean_object* v_a_399_, lean_object* v_inst_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_box(0);
v___x_403_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_403_, 0, v_pendingProducer_393_);
lean_ctor_set(v___x_403_, 1, v_pendingConsumer_394_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
lean_ctor_set(v___x_403_, 3, v_knownSize_396_);
lean_ctor_set(v___x_403_, 4, v_pendingIncompleteChunk_397_);
lean_ctor_set(v___x_403_, 5, v_closeError_398_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*6, v_closed_395_);
lean_inc(v_a_399_);
v___x_404_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_404_, 0, lean_box(0));
lean_closure_set(v___x_404_, 1, lean_box(0));
lean_closure_set(v___x_404_, 2, v_a_399_);
lean_closure_set(v___x_404_, 3, v___x_403_);
v___x_405_ = lean_apply_2(v_inst_400_, lean_box(0), v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingProducer_393_ = stack[0].m_obj;
lean_object* v_pendingConsumer_394_ = stack[1].m_obj;
uint8_t v_closed_395_ = stack[2].m_num;
lean_object* v_knownSize_396_ = stack[3].m_obj;
lean_object* v_pendingIncompleteChunk_397_ = stack[4].m_obj;
lean_object* v_closeError_398_ = stack[5].m_obj;
lean_object* v_a_399_ = stack[6].m_obj;
lean_object* v_inst_400_ = stack[7].m_obj;
lean_object* v_a_401_ = stack[8].m_obj;
lean_object* v_res_406_;
v_res_406_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(v_pendingProducer_393_, v_pendingConsumer_394_, v_closed_395_, v_knownSize_396_, v_pendingIncompleteChunk_397_, v_closeError_398_, v_a_399_, v_inst_400_, v_a_401_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object* v_pendingProducer_407_, lean_object* v_pendingConsumer_408_, lean_object* v_closed_409_, lean_object* v_knownSize_410_, lean_object* v_pendingIncompleteChunk_411_, lean_object* v_closeError_412_, lean_object* v_a_413_, lean_object* v_inst_414_, lean_object* v_a_415_){
_start:
{
uint8_t v_closed_boxed_416_; lean_object* v_res_417_; 
v_closed_boxed_416_ = lean_unbox(v_closed_409_);
v_res_417_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(v_pendingProducer_407_, v_pendingConsumer_408_, v_closed_boxed_416_, v_knownSize_410_, v_pendingIncompleteChunk_411_, v_closeError_412_, v_a_413_, v_inst_414_, v_a_415_);
lean_dec(v_a_413_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(lean_object* v_toApplicative_418_, lean_object* v_a_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_toBind_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_interestWaiter_424_; 
v_interestWaiter_424_ = lean_ctor_get(v_a_423_, 2);
lean_inc(v_interestWaiter_424_);
if (lean_obj_tag(v_interestWaiter_424_) == 1)
{
lean_object* v_toFunctor_425_; lean_object* v_pendingProducer_426_; lean_object* v_pendingConsumer_427_; uint8_t v_closed_428_; lean_object* v_knownSize_429_; lean_object* v_pendingIncompleteChunk_430_; lean_object* v_closeError_431_; lean_object* v_val_432_; lean_object* v_mapConst_433_; lean_object* v___x_434_; lean_object* v___f_435_; uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_toFunctor_425_ = lean_ctor_get(v_toApplicative_418_, 0);
lean_inc_ref(v_toFunctor_425_);
lean_dec_ref(v_toApplicative_418_);
v_pendingProducer_426_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_pendingProducer_426_);
v_pendingConsumer_427_ = lean_ctor_get(v_a_423_, 1);
lean_inc(v_pendingConsumer_427_);
v_closed_428_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*6);
v_knownSize_429_ = lean_ctor_get(v_a_423_, 3);
lean_inc(v_knownSize_429_);
v_pendingIncompleteChunk_430_ = lean_ctor_get(v_a_423_, 4);
lean_inc(v_pendingIncompleteChunk_430_);
v_closeError_431_ = lean_ctor_get(v_a_423_, 5);
lean_inc(v_closeError_431_);
lean_dec_ref(v_a_423_);
v_val_432_ = lean_ctor_get(v_interestWaiter_424_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v_interestWaiter_424_, 1);
v_mapConst_433_ = lean_ctor_get(v_toFunctor_425_, 1);
lean_inc(v_mapConst_433_);
lean_dec_ref(v_toFunctor_425_);
v___x_434_ = lean_box(v_closed_428_);
lean_inc(v_a_419_);
v___f_435_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_435_, 0, v_pendingProducer_426_);
lean_closure_set(v___f_435_, 1, v_pendingConsumer_427_);
lean_closure_set(v___f_435_, 2, v___x_434_);
lean_closure_set(v___f_435_, 3, v_knownSize_429_);
lean_closure_set(v___f_435_, 4, v_pendingIncompleteChunk_430_);
lean_closure_set(v___f_435_, 5, v_closeError_431_);
lean_closure_set(v___f_435_, 6, v_a_419_);
lean_closure_set(v___f_435_, 7, v_inst_420_);
v___x_436_ = 1;
v___x_437_ = lean_box(v___x_436_);
v___x_438_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_438_, 0, v_val_432_);
lean_closure_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_apply_2(v_inst_421_, lean_box(0), v___x_438_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_apply_4(v_mapConst_433_, lean_box(0), lean_box(0), v___x_440_, v___x_439_);
v___x_442_ = lean_apply_4(v_toBind_422_, lean_box(0), lean_box(0), v___x_441_, v___f_435_);
return v___x_442_;
}
else
{
lean_object* v_toPure_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec(v_interestWaiter_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_toBind_422_);
lean_dec(v_inst_421_);
lean_dec(v_inst_420_);
v_toPure_443_ = lean_ctor_get(v_toApplicative_418_, 1);
lean_inc(v_toPure_443_);
lean_dec_ref(v_toApplicative_418_);
v___x_444_ = lean_box(0);
v___x_445_ = lean_apply_2(v_toPure_443_, lean_box(0), v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(lean_object* v_toApplicative_446_, lean_object* v_a_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_toBind_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(v_toApplicative_446_, v_a_447_, v_inst_448_, v_inst_449_, v_toBind_450_, v_a_451_);
lean_dec(v_a_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_toApplicative_457_; lean_object* v_toBind_458_; lean_object* v___f_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_toApplicative_457_ = lean_ctor_get(v_inst_453_, 0);
lean_inc_ref(v_toApplicative_457_);
v_toBind_458_ = lean_ctor_get(v_inst_453_, 1);
lean_inc_n(v_toBind_458_, 2);
lean_dec_ref(v_inst_453_);
lean_inc(v_inst_454_);
lean_inc_n(v_a_456_, 2);
v___f_459_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_459_, 0, v_toApplicative_457_);
lean_closure_set(v___f_459_, 1, v_a_456_);
lean_closure_set(v___f_459_, 2, v_inst_454_);
lean_closure_set(v___f_459_, 3, v_inst_455_);
lean_closure_set(v___f_459_, 4, v_toBind_458_);
v___x_460_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_460_, 0, lean_box(0));
lean_closure_set(v___x_460_, 1, lean_box(0));
lean_closure_set(v___x_460_, 2, v_a_456_);
v___x_461_ = lean_apply_2(v_inst_454_, lean_box(0), v___x_460_);
v___x_462_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v___x_461_, v___f_459_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_463_, v_inst_464_, v_inst_465_, v_a_466_);
lean_dec(v_a_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(lean_object* v_m_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_469_, v_inst_470_, v_inst_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(lean_object* v_m_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(v_m_474_, v_inst_475_, v_inst_476_, v_inst_477_, v_a_478_);
lean_dec(v_a_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_480_, lean_object* v_a_481_){
_start:
{
uint8_t v___y_483_; lean_object* v_pendingProducer_487_; 
v_pendingProducer_487_ = lean_ctor_get(v_a_481_, 0);
if (lean_obj_tag(v_pendingProducer_487_) == 0)
{
uint8_t v_closed_488_; 
v_closed_488_ = lean_ctor_get_uint8(v_a_481_, sizeof(void*)*6);
v___y_483_ = v_closed_488_;
goto v___jp_482_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = 1;
v___y_483_ = v___x_489_;
goto v___jp_482_;
}
v___jp_482_:
{
lean_object* v_toPure_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_toPure_484_ = lean_ctor_get(v_toApplicative_480_, 1);
lean_inc(v_toPure_484_);
lean_dec_ref(v_toApplicative_480_);
v___x_485_ = lean_box(v___y_483_);
v___x_486_ = lean_apply_2(v_toPure_484_, lean_box(0), v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(v_toApplicative_490_, v_a_491_);
lean_dec_ref(v_a_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_toApplicative_496_; lean_object* v_toBind_497_; lean_object* v___f_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_toApplicative_496_ = lean_ctor_get(v_inst_493_, 0);
lean_inc_ref(v_toApplicative_496_);
v_toBind_497_ = lean_ctor_get(v_inst_493_, 1);
lean_inc(v_toBind_497_);
lean_dec_ref(v_inst_493_);
v___f_498_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_498_, 0, v_toApplicative_496_);
lean_inc(v_a_495_);
v___x_499_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_499_, 0, lean_box(0));
lean_closure_set(v___x_499_, 1, lean_box(0));
lean_closure_set(v___x_499_, 2, v_a_495_);
v___x_500_ = lean_apply_2(v_inst_494_, lean_box(0), v___x_499_);
v___x_501_ = lean_apply_4(v_toBind_497_, lean_box(0), lean_box(0), v___x_500_, v___f_498_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_502_, v_inst_503_, v_a_504_);
lean_dec(v_a_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(lean_object* v_m_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_507_, v_inst_508_, v_a_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(lean_object* v_m_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(v_m_511_, v_inst_512_, v_inst_513_, v_a_514_);
lean_dec(v_a_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(lean_object* v_toApplicative_516_, lean_object* v_a_517_){
_start:
{
uint8_t v___y_519_; lean_object* v_pendingConsumer_523_; 
v_pendingConsumer_523_ = lean_ctor_get(v_a_517_, 1);
if (lean_obj_tag(v_pendingConsumer_523_) == 0)
{
uint8_t v___x_524_; 
v___x_524_ = 0;
v___y_519_ = v___x_524_;
goto v___jp_518_;
}
else
{
uint8_t v___x_525_; 
v___x_525_ = 1;
v___y_519_ = v___x_525_;
goto v___jp_518_;
}
v___jp_518_:
{
lean_object* v_toPure_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_toPure_520_ = lean_ctor_get(v_toApplicative_516_, 1);
lean_inc(v_toPure_520_);
lean_dec_ref(v_toApplicative_516_);
v___x_521_ = lean_box(v___y_519_);
v___x_522_ = lean_apply_2(v_toPure_520_, lean_box(0), v___x_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(v_toApplicative_526_, v_a_527_);
lean_dec_ref(v_a_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_toApplicative_532_; lean_object* v_toBind_533_; lean_object* v___f_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_toApplicative_532_ = lean_ctor_get(v_inst_529_, 0);
lean_inc_ref(v_toApplicative_532_);
v_toBind_533_ = lean_ctor_get(v_inst_529_, 1);
lean_inc(v_toBind_533_);
lean_dec_ref(v_inst_529_);
v___f_534_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_534_, 0, v_toApplicative_532_);
lean_inc(v_a_531_);
v___x_535_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_535_, 0, lean_box(0));
lean_closure_set(v___x_535_, 1, lean_box(0));
lean_closure_set(v___x_535_, 2, v_a_531_);
v___x_536_ = lean_apply_2(v_inst_530_, lean_box(0), v___x_535_);
v___x_537_ = lean_apply_4(v_toBind_533_, lean_box(0), lean_box(0), v___x_536_, v___f_534_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_538_, v_inst_539_, v_a_540_);
lean_dec(v_a_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(lean_object* v_m_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_543_, v_inst_544_, v_a_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(lean_object* v_m_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(v_m_547_, v_inst_548_, v_inst_549_, v_a_550_);
lean_dec(v_a_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_552_, lean_object* v_chunk_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_toPure_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_toPure_555_ = lean_ctor_get(v_toApplicative_552_, 1);
lean_inc(v_toPure_555_);
lean_dec_ref(v_toApplicative_552_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v_chunk_553_);
v___x_557_ = lean_apply_2(v_toPure_555_, lean_box(0), v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_558_, lean_object* v_done_559_, lean_object* v_inst_560_, lean_object* v_toBind_561_, lean_object* v___f_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_toFunctor_564_; lean_object* v_mapConst_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_toFunctor_564_ = lean_ctor_get(v_toApplicative_558_, 0);
lean_inc_ref(v_toFunctor_564_);
lean_dec_ref(v_toApplicative_558_);
v_mapConst_565_ = lean_ctor_get(v_toFunctor_564_, 1);
lean_inc(v_mapConst_565_);
lean_dec_ref(v_toFunctor_564_);
v___x_566_ = 1;
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_568_, 0, lean_box(0));
lean_closure_set(v___x_568_, 1, v___x_567_);
lean_closure_set(v___x_568_, 2, v_done_559_);
v___x_569_ = lean_apply_2(v_inst_560_, lean_box(0), v___x_568_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_4(v_mapConst_565_, lean_box(0), lean_box(0), v___x_570_, v___x_569_);
v___x_572_ = lean_apply_4(v_toBind_561_, lean_box(0), lean_box(0), v___x_571_, v___f_562_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_573_, lean_object* v_inst_574_, lean_object* v_toBind_575_, lean_object* v_a_576_, lean_object* v_inst_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_pendingProducer_579_; 
v_pendingProducer_579_ = lean_ctor_get(v_a_578_, 0);
if (lean_obj_tag(v_pendingProducer_579_) == 1)
{
lean_object* v_val_580_; lean_object* v_pendingConsumer_581_; lean_object* v_interestWaiter_582_; uint8_t v_closed_583_; lean_object* v_knownSize_584_; lean_object* v_pendingIncompleteChunk_585_; lean_object* v_closeError_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_602_; 
v_val_580_ = lean_ctor_get(v_pendingProducer_579_, 0);
lean_inc(v_val_580_);
v_pendingConsumer_581_ = lean_ctor_get(v_a_578_, 1);
v_interestWaiter_582_ = lean_ctor_get(v_a_578_, 2);
v_closed_583_ = lean_ctor_get_uint8(v_a_578_, sizeof(void*)*6);
v_knownSize_584_ = lean_ctor_get(v_a_578_, 3);
v_pendingIncompleteChunk_585_ = lean_ctor_get(v_a_578_, 4);
v_closeError_586_ = lean_ctor_get(v_a_578_, 5);
v_isSharedCheck_602_ = !lean_is_exclusive(v_a_578_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_a_578_, 0);
lean_dec(v_unused_603_);
v___x_588_ = v_a_578_;
v_isShared_589_ = v_isSharedCheck_602_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_closeError_586_);
lean_inc(v_pendingIncompleteChunk_585_);
lean_inc(v_knownSize_584_);
lean_inc(v_interestWaiter_582_);
lean_inc(v_pendingConsumer_581_);
lean_dec(v_a_578_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_602_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_chunk_590_; lean_object* v_done_591_; lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v_chunk_590_ = lean_ctor_get(v_val_580_, 0);
lean_inc_ref_n(v_chunk_590_, 2);
v_done_591_ = lean_ctor_get(v_val_580_, 1);
lean_inc(v_done_591_);
lean_dec(v_val_580_);
v___x_592_ = lean_box(0);
lean_inc_ref(v_toApplicative_573_);
v___f_593_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_593_, 0, v_toApplicative_573_);
lean_closure_set(v___f_593_, 1, v_chunk_590_);
lean_inc(v_toBind_575_);
v___f_594_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_594_, 0, v_toApplicative_573_);
lean_closure_set(v___f_594_, 1, v_done_591_);
lean_closure_set(v___f_594_, 2, v_inst_574_);
lean_closure_set(v___f_594_, 3, v_toBind_575_);
lean_closure_set(v___f_594_, 4, v___f_593_);
v___x_595_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_584_, v_chunk_590_);
lean_dec_ref(v_chunk_590_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 3, v___x_595_);
lean_ctor_set(v___x_588_, 0, v___x_592_);
v___x_597_ = v___x_588_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_pendingConsumer_581_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_interestWaiter_582_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_pendingIncompleteChunk_585_);
lean_ctor_set(v_reuseFailAlloc_601_, 5, v_closeError_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_601_, sizeof(void*)*6, v_closed_583_);
v___x_597_ = v_reuseFailAlloc_601_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
lean_inc(v_a_576_);
v___x_598_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_598_, 0, lean_box(0));
lean_closure_set(v___x_598_, 1, lean_box(0));
lean_closure_set(v___x_598_, 2, v_a_576_);
lean_closure_set(v___x_598_, 3, v___x_597_);
v___x_599_ = lean_apply_2(v_inst_577_, lean_box(0), v___x_598_);
v___x_600_ = lean_apply_4(v_toBind_575_, lean_box(0), lean_box(0), v___x_599_, v___f_594_);
return v___x_600_;
}
}
}
else
{
lean_object* v_toPure_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec_ref(v_a_578_);
lean_dec(v_inst_577_);
lean_dec(v_toBind_575_);
lean_dec(v_inst_574_);
v_toPure_604_ = lean_ctor_get(v_toApplicative_573_, 1);
lean_inc(v_toPure_604_);
lean_dec_ref(v_toApplicative_573_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_apply_2(v_toPure_604_, lean_box(0), v___x_605_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_toApplicative_607_, lean_object* v_inst_608_, lean_object* v_toBind_609_, lean_object* v_a_610_, lean_object* v_inst_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(v_toApplicative_607_, v_inst_608_, v_toBind_609_, v_a_610_, v_inst_611_, v_a_612_);
lean_dec(v_a_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_toApplicative_618_; lean_object* v_toBind_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_toApplicative_618_ = lean_ctor_get(v_inst_614_, 0);
lean_inc_ref(v_toApplicative_618_);
v_toBind_619_ = lean_ctor_get(v_inst_614_, 1);
lean_inc_n(v_toBind_619_, 2);
lean_dec_ref(v_inst_614_);
lean_inc(v_inst_615_);
lean_inc_n(v_a_617_, 2);
v___f_620_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_620_, 0, v_toApplicative_618_);
lean_closure_set(v___f_620_, 1, v_inst_616_);
lean_closure_set(v___f_620_, 2, v_toBind_619_);
lean_closure_set(v___f_620_, 3, v_a_617_);
lean_closure_set(v___f_620_, 4, v_inst_615_);
v___x_621_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_621_, 0, lean_box(0));
lean_closure_set(v___x_621_, 1, lean_box(0));
lean_closure_set(v___x_621_, 2, v_a_617_);
v___x_622_ = lean_apply_2(v_inst_615_, lean_box(0), v___x_621_);
v___x_623_ = lean_apply_4(v_toBind_619_, lean_box(0), lean_box(0), v___x_622_, v___f_620_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_624_, v_inst_625_, v_inst_626_, v_a_627_);
lean_dec(v_a_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(lean_object* v_m_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_630_, v_inst_631_, v_inst_632_, v_a_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(lean_object* v_m_635_, lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(v_m_635_, v_inst_636_, v_inst_637_, v_inst_638_, v_a_639_);
lean_dec(v_a_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0(lean_object* v_toApplicative_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_closeError_645_; 
v_closeError_645_ = lean_ctor_get(v_a_644_, 5);
lean_inc(v_closeError_645_);
lean_dec_ref(v_a_644_);
if (lean_obj_tag(v_closeError_645_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_655_; 
v_val_646_ = lean_ctor_get(v_closeError_645_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v_closeError_645_);
if (v_isSharedCheck_655_ == 0)
{
v___x_648_ = v_closeError_645_;
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_val_646_);
lean_dec(v_closeError_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_toPure_650_; lean_object* v___x_652_; 
v_toPure_650_ = lean_ctor_get(v_toApplicative_643_, 1);
lean_inc(v_toPure_650_);
lean_dec_ref(v_toApplicative_643_);
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 0);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_val_646_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; 
v___x_653_ = lean_apply_2(v_toPure_650_, lean_box(0), v___x_652_);
return v___x_653_;
}
}
}
else
{
lean_object* v_toPure_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec(v_closeError_645_);
v_toPure_656_ = lean_ctor_get(v_toApplicative_643_, 1);
lean_inc(v_toPure_656_);
lean_dec_ref(v_toApplicative_643_);
v___x_657_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_658_ = lean_apply_2(v_toPure_656_, lean_box(0), v___x_657_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(lean_object* v_toApplicative_659_, lean_object* v_a_660_, lean_object* v_inst_661_, lean_object* v_toBind_662_, lean_object* v___f_663_, lean_object* v_a_664_){
_start:
{
if (lean_obj_tag(v_a_664_) == 1)
{
lean_object* v_toPure_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec(v___f_663_);
lean_dec(v_toBind_662_);
lean_dec(v_inst_661_);
v_toPure_665_ = lean_ctor_get(v_toApplicative_659_, 1);
lean_inc(v_toPure_665_);
lean_dec_ref(v_toApplicative_659_);
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v_a_664_);
v___x_667_ = lean_apply_2(v_toPure_665_, lean_box(0), v___x_666_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec(v_a_664_);
lean_dec_ref(v_toApplicative_659_);
lean_inc(v_a_660_);
v___x_668_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_668_, 0, lean_box(0));
lean_closure_set(v___x_668_, 1, lean_box(0));
lean_closure_set(v___x_668_, 2, v_a_660_);
v___x_669_ = lean_apply_2(v_inst_661_, lean_box(0), v___x_668_);
v___x_670_ = lean_apply_4(v_toBind_662_, lean_box(0), lean_box(0), v___x_669_, v___f_663_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_671_, lean_object* v_a_672_, lean_object* v_inst_673_, lean_object* v_toBind_674_, lean_object* v___f_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(v_toApplicative_671_, v_a_672_, v_inst_673_, v_toBind_674_, v___f_675_, v_a_676_);
lean_dec(v_a_672_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_toApplicative_682_; lean_object* v_toBind_683_; lean_object* v___f_684_; lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_toApplicative_682_ = lean_ctor_get(v_inst_678_, 0);
v_toBind_683_ = lean_ctor_get(v_inst_678_, 1);
lean_inc_n(v_toBind_683_, 2);
lean_inc_ref_n(v_toApplicative_682_, 2);
v___f_684_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_684_, 0, v_toApplicative_682_);
lean_inc(v_inst_679_);
lean_inc(v_a_681_);
v___f_685_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_685_, 0, v_toApplicative_682_);
lean_closure_set(v___f_685_, 1, v_a_681_);
lean_closure_set(v___f_685_, 2, v_inst_679_);
lean_closure_set(v___f_685_, 3, v_toBind_683_);
lean_closure_set(v___f_685_, 4, v___f_684_);
v___x_686_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_678_, v_inst_679_, v_inst_680_, v_a_681_);
v___x_687_ = lean_apply_4(v_toBind_683_, lean_box(0), lean_box(0), v___x_686_, v___f_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___boxed(lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_688_, v_inst_689_, v_inst_690_, v_a_691_);
lean_dec(v_a_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(lean_object* v_m_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_a_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___boxed(lean_object* v_m_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(v_m_699_, v_inst_700_, v_inst_701_, v_inst_702_, v_a_703_);
lean_dec(v_a_703_);
return v_res_704_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(uint8_t v___x_705_, lean_object* v_knownSize_706_, lean_object* v_closeError_707_, lean_object* v_inst_708_, lean_object* v_____r_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_711_ = lean_box(0);
v___x_712_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
lean_ctor_set(v___x_712_, 3, v_knownSize_706_);
lean_ctor_set(v___x_712_, 4, v___x_711_);
lean_ctor_set(v___x_712_, 5, v_closeError_707_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*6, v___x_705_);
lean_inc(v___y_710_);
v___x_713_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_713_, 0, lean_box(0));
lean_closure_set(v___x_713_, 1, lean_box(0));
lean_closure_set(v___x_713_, 2, v___y_710_);
lean_closure_set(v___x_713_, 3, v___x_712_);
v___x_714_ = lean_apply_2(v_inst_708_, lean_box(0), v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_705_ = stack[0].m_num;
lean_object* v_knownSize_706_ = stack[1].m_obj;
lean_object* v_closeError_707_ = stack[2].m_obj;
lean_object* v_inst_708_ = stack[3].m_obj;
lean_object* v_____r_709_ = stack[4].m_obj;
lean_object* v___y_710_ = stack[5].m_obj;
lean_object* v_res_715_;
v_res_715_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(v___x_705_, v_knownSize_706_, v_closeError_707_, v_inst_708_, v_____r_709_, v___y_710_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed(lean_object* v___x_716_, lean_object* v_knownSize_717_, lean_object* v_closeError_718_, lean_object* v_inst_719_, lean_object* v_____r_720_, lean_object* v___y_721_){
_start:
{
uint8_t v___x_635__boxed_722_; lean_object* v_res_723_; 
v___x_635__boxed_722_ = lean_unbox(v___x_716_);
v_res_723_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(v___x_635__boxed_722_, v_knownSize_717_, v_closeError_718_, v_inst_719_, v_____r_720_, v___y_721_);
lean_dec(v___y_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(lean_object* v___f_724_, lean_object* v___y_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_727_; 
lean_inc(v___y_725_);
v___x_727_ = lean_apply_2(v___f_724_, v_a_726_, v___y_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object* v___f_728_, lean_object* v___y_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(v___f_728_, v___y_729_, v_a_730_);
lean_dec(v___y_729_);
return v_res_731_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object* v_pendingProducer_732_, lean_object* v_toApplicative_733_, lean_object* v___f_734_, uint8_t v_closed_735_, lean_object* v_inst_736_, lean_object* v_toBind_737_, lean_object* v_____r_738_, lean_object* v___y_739_){
_start:
{
if (lean_obj_tag(v_pendingProducer_732_) == 1)
{
lean_object* v_val_740_; lean_object* v_toFunctor_741_; lean_object* v_done_742_; lean_object* v_mapConst_743_; lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_val_740_ = lean_ctor_get(v_pendingProducer_732_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v_pendingProducer_732_, 1);
v_toFunctor_741_ = lean_ctor_get(v_toApplicative_733_, 0);
lean_inc_ref(v_toFunctor_741_);
lean_dec_ref(v_toApplicative_733_);
v_done_742_ = lean_ctor_get(v_val_740_, 1);
lean_inc(v_done_742_);
lean_dec(v_val_740_);
v_mapConst_743_ = lean_ctor_get(v_toFunctor_741_, 1);
lean_inc(v_mapConst_743_);
lean_dec_ref(v_toFunctor_741_);
lean_inc(v___y_739_);
v___f_744_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_744_, 0, v___f_734_);
lean_closure_set(v___f_744_, 1, v___y_739_);
v___x_745_ = lean_box(v_closed_735_);
v___x_746_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_746_, 0, lean_box(0));
lean_closure_set(v___x_746_, 1, v___x_745_);
lean_closure_set(v___x_746_, 2, v_done_742_);
v___x_747_ = lean_apply_2(v_inst_736_, lean_box(0), v___x_746_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_apply_4(v_mapConst_743_, lean_box(0), lean_box(0), v___x_748_, v___x_747_);
v___x_750_ = lean_apply_4(v_toBind_737_, lean_box(0), lean_box(0), v___x_749_, v___f_744_);
return v___x_750_;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec(v_toBind_737_);
lean_dec(v_inst_736_);
lean_dec_ref(v_toApplicative_733_);
lean_dec(v_pendingProducer_732_);
v___x_751_ = lean_box(0);
lean_inc(v___y_739_);
v___x_752_ = lean_apply_2(v___f_734_, v___x_751_, v___y_739_);
return v___x_752_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingProducer_732_ = stack[0].m_obj;
lean_object* v_toApplicative_733_ = stack[1].m_obj;
lean_object* v___f_734_ = stack[2].m_obj;
uint8_t v_closed_735_ = stack[3].m_num;
lean_object* v_inst_736_ = stack[4].m_obj;
lean_object* v_toBind_737_ = stack[5].m_obj;
lean_object* v_____r_738_ = stack[6].m_obj;
lean_object* v___y_739_ = stack[7].m_obj;
lean_object* v_res_753_;
v_res_753_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(v_pendingProducer_732_, v_toApplicative_733_, v___f_734_, v_closed_735_, v_inst_736_, v_toBind_737_, v_____r_738_, v___y_739_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed(lean_object* v_pendingProducer_754_, lean_object* v_toApplicative_755_, lean_object* v___f_756_, lean_object* v_closed_757_, lean_object* v_inst_758_, lean_object* v_toBind_759_, lean_object* v_____r_760_, lean_object* v___y_761_){
_start:
{
uint8_t v_closed_boxed_762_; lean_object* v_res_763_; 
v_closed_boxed_762_ = lean_unbox(v_closed_757_);
v_res_763_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(v_pendingProducer_754_, v_toApplicative_755_, v___f_756_, v_closed_boxed_762_, v_inst_758_, v_toBind_759_, v_____r_760_, v___y_761_);
lean_dec(v___y_761_);
return v_res_763_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object* v_interestWaiter_764_, lean_object* v_toApplicative_765_, lean_object* v___f_766_, uint8_t v_closed_767_, lean_object* v_inst_768_, lean_object* v_toBind_769_, lean_object* v_____r_770_, lean_object* v___y_771_){
_start:
{
if (lean_obj_tag(v_interestWaiter_764_) == 1)
{
lean_object* v_toFunctor_772_; lean_object* v_val_773_; lean_object* v_mapConst_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_toFunctor_772_ = lean_ctor_get(v_toApplicative_765_, 0);
lean_inc_ref(v_toFunctor_772_);
lean_dec_ref(v_toApplicative_765_);
v_val_773_ = lean_ctor_get(v_interestWaiter_764_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v_interestWaiter_764_, 1);
v_mapConst_774_ = lean_ctor_get(v_toFunctor_772_, 1);
lean_inc(v_mapConst_774_);
lean_dec_ref(v_toFunctor_772_);
lean_inc(v___y_771_);
v___f_775_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_775_, 0, v___f_766_);
lean_closure_set(v___f_775_, 1, v___y_771_);
v___x_776_ = lean_box(v_closed_767_);
v___x_777_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_777_, 0, v_val_773_);
lean_closure_set(v___x_777_, 1, v___x_776_);
v___x_778_ = lean_apply_2(v_inst_768_, lean_box(0), v___x_777_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_apply_4(v_mapConst_774_, lean_box(0), lean_box(0), v___x_779_, v___x_778_);
v___x_781_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_780_, v___f_775_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v_toBind_769_);
lean_dec(v_inst_768_);
lean_dec_ref(v_toApplicative_765_);
lean_dec(v_interestWaiter_764_);
v___x_782_ = lean_box(0);
lean_inc(v___y_771_);
v___x_783_ = lean_apply_2(v___f_766_, v___x_782_, v___y_771_);
return v___x_783_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_interestWaiter_764_ = stack[0].m_obj;
lean_object* v_toApplicative_765_ = stack[1].m_obj;
lean_object* v___f_766_ = stack[2].m_obj;
uint8_t v_closed_767_ = stack[3].m_num;
lean_object* v_inst_768_ = stack[4].m_obj;
lean_object* v_toBind_769_ = stack[5].m_obj;
lean_object* v_____r_770_ = stack[6].m_obj;
lean_object* v___y_771_ = stack[7].m_obj;
lean_object* v_res_784_;
v_res_784_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_764_, v_toApplicative_765_, v___f_766_, v_closed_767_, v_inst_768_, v_toBind_769_, v_____r_770_, v___y_771_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object* v_interestWaiter_785_, lean_object* v_toApplicative_786_, lean_object* v___f_787_, lean_object* v_closed_788_, lean_object* v_inst_789_, lean_object* v_toBind_790_, lean_object* v_____r_791_, lean_object* v___y_792_){
_start:
{
uint8_t v_closed_boxed_793_; lean_object* v_res_794_; 
v_closed_boxed_793_ = lean_unbox(v_closed_788_);
v_res_794_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_785_, v_toApplicative_786_, v___f_787_, v_closed_boxed_793_, v_inst_789_, v_toBind_790_, v_____r_791_, v___y_792_);
lean_dec(v___y_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(lean_object* v___f_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_798_; 
lean_inc(v_a_796_);
v___x_798_ = lean_apply_2(v___f_795_, v_a_797_, v_a_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object* v___f_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(v___f_799_, v_a_800_, v_a_801_);
lean_dec(v_a_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object* v_inst_803_, lean_object* v_toApplicative_804_, lean_object* v_inst_805_, lean_object* v_toBind_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
uint8_t v_closed_809_; 
v_closed_809_ = lean_ctor_get_uint8(v_a_808_, sizeof(void*)*6);
if (v_closed_809_ == 0)
{
lean_object* v_pendingProducer_810_; lean_object* v_pendingConsumer_811_; lean_object* v_interestWaiter_812_; lean_object* v_knownSize_813_; lean_object* v_closeError_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___f_819_; lean_object* v___x_820_; lean_object* v___f_821_; 
v_pendingProducer_810_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_pendingProducer_810_);
v_pendingConsumer_811_ = lean_ctor_get(v_a_808_, 1);
lean_inc(v_pendingConsumer_811_);
v_interestWaiter_812_ = lean_ctor_get(v_a_808_, 2);
lean_inc_n(v_interestWaiter_812_, 2);
v_knownSize_813_ = lean_ctor_get(v_a_808_, 3);
lean_inc(v_knownSize_813_);
v_closeError_814_ = lean_ctor_get(v_a_808_, 5);
lean_inc_n(v_closeError_814_, 2);
lean_dec_ref(v_a_808_);
v___x_815_ = 1;
v___x_816_ = lean_box(v___x_815_);
v___f_817_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_817_, 0, v___x_816_);
lean_closure_set(v___f_817_, 1, v_knownSize_813_);
lean_closure_set(v___f_817_, 2, v_closeError_814_);
lean_closure_set(v___f_817_, 3, v_inst_803_);
v___x_818_ = lean_box(v_closed_809_);
lean_inc_n(v_toBind_806_, 2);
lean_inc_n(v_inst_805_, 2);
lean_inc_ref_n(v_toApplicative_804_, 2);
v___f_819_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_819_, 0, v_pendingProducer_810_);
lean_closure_set(v___f_819_, 1, v_toApplicative_804_);
lean_closure_set(v___f_819_, 2, v___f_817_);
lean_closure_set(v___f_819_, 3, v___x_818_);
lean_closure_set(v___f_819_, 4, v_inst_805_);
lean_closure_set(v___f_819_, 5, v_toBind_806_);
v___x_820_ = lean_box(v_closed_809_);
lean_inc_ref(v___f_819_);
v___f_821_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_821_, 0, v_interestWaiter_812_);
lean_closure_set(v___f_821_, 1, v_toApplicative_804_);
lean_closure_set(v___f_821_, 2, v___f_819_);
lean_closure_set(v___f_821_, 3, v___x_820_);
lean_closure_set(v___f_821_, 4, v_inst_805_);
lean_closure_set(v___f_821_, 5, v_toBind_806_);
if (lean_obj_tag(v_pendingConsumer_811_) == 1)
{
lean_object* v_val_822_; lean_object* v___f_823_; lean_object* v___y_825_; 
lean_dec_ref(v___f_819_);
lean_dec(v_interestWaiter_812_);
v_val_822_ = lean_ctor_get(v_pendingConsumer_811_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v_pendingConsumer_811_, 1);
lean_inc(v_a_807_);
v___f_823_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_823_, 0, v___f_821_);
lean_closure_set(v___f_823_, 1, v_a_807_);
if (lean_obj_tag(v_closeError_814_) == 0)
{
lean_object* v___x_833_; 
v___x_833_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___y_825_ = v___x_833_;
goto v___jp_824_;
}
else
{
lean_object* v_val_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_val_834_ = lean_ctor_get(v_closeError_814_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v_closeError_814_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v_closeError_814_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_val_834_);
lean_dec(v_closeError_814_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_val_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
v___y_825_ = v___x_839_;
goto v___jp_824_;
}
}
}
v___jp_824_:
{
lean_object* v_toFunctor_826_; lean_object* v_mapConst_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_toFunctor_826_ = lean_ctor_get(v_toApplicative_804_, 0);
lean_inc_ref(v_toFunctor_826_);
lean_dec_ref(v_toApplicative_804_);
v_mapConst_827_ = lean_ctor_get(v_toFunctor_826_, 1);
lean_inc(v_mapConst_827_);
lean_dec_ref(v_toFunctor_826_);
v___x_828_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed), 3, 2);
lean_closure_set(v___x_828_, 0, v_val_822_);
lean_closure_set(v___x_828_, 1, v___y_825_);
v___x_829_ = lean_apply_2(v_inst_805_, lean_box(0), v___x_828_);
v___x_830_ = lean_box(0);
v___x_831_ = lean_apply_4(v_mapConst_827_, lean_box(0), lean_box(0), v___x_830_, v___x_829_);
v___x_832_ = lean_apply_4(v_toBind_806_, lean_box(0), lean_box(0), v___x_831_, v___f_823_);
return v___x_832_;
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref(v___f_821_);
lean_dec(v_closeError_814_);
lean_dec(v_pendingConsumer_811_);
v___x_842_ = lean_box(0);
v___x_843_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_812_, v_toApplicative_804_, v___f_819_, v_closed_809_, v_inst_805_, v_toBind_806_, v___x_842_, v_a_807_);
return v___x_843_;
}
}
else
{
lean_object* v_toPure_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec_ref(v_a_808_);
lean_dec(v_toBind_806_);
lean_dec(v_inst_805_);
lean_dec(v_inst_803_);
v_toPure_844_ = lean_ctor_get(v_toApplicative_804_, 1);
lean_inc(v_toPure_844_);
lean_dec_ref(v_toApplicative_804_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_apply_2(v_toPure_844_, lean_box(0), v___x_845_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object* v_inst_847_, lean_object* v_toApplicative_848_, lean_object* v_inst_849_, lean_object* v_toBind_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(v_inst_847_, v_toApplicative_848_, v_inst_849_, v_toBind_850_, v_a_851_, v_a_852_);
lean_dec(v_a_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_toApplicative_858_; lean_object* v_toBind_859_; lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_toApplicative_858_ = lean_ctor_get(v_inst_854_, 0);
lean_inc_ref(v_toApplicative_858_);
v_toBind_859_ = lean_ctor_get(v_inst_854_, 1);
lean_inc_n(v_toBind_859_, 2);
lean_dec_ref(v_inst_854_);
lean_inc_n(v_a_857_, 2);
lean_inc(v_inst_855_);
v___f_860_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_860_, 0, v_inst_855_);
lean_closure_set(v___f_860_, 1, v_toApplicative_858_);
lean_closure_set(v___f_860_, 2, v_inst_856_);
lean_closure_set(v___f_860_, 3, v_toBind_859_);
lean_closure_set(v___f_860_, 4, v_a_857_);
v___x_861_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_861_, 0, lean_box(0));
lean_closure_set(v___x_861_, 1, lean_box(0));
lean_closure_set(v___x_861_, 2, v_a_857_);
v___x_862_ = lean_apply_2(v_inst_855_, lean_box(0), v___x_861_);
v___x_863_ = lean_apply_4(v_toBind_859_, lean_box(0), lean_box(0), v___x_862_, v___f_860_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_864_, v_inst_865_, v_inst_866_, v_a_867_);
lean_dec(v_a_867_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object* v_m_869_, lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_870_, v_inst_871_, v_inst_872_, v_a_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object* v_m_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(v_m_875_, v_inst_876_, v_inst_877_, v_inst_878_, v_a_879_);
lean_dec(v_a_879_);
return v_res_880_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object* v_pendingProducer_885_, lean_object* v_pendingConsumer_886_, uint8_t v_closed_887_, lean_object* v_knownSize_888_, lean_object* v_pendingIncompleteChunk_889_, lean_object* v_closeError_890_, lean_object* v_interestWaiter_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_894_, 0, v_pendingProducer_885_);
lean_ctor_set(v___x_894_, 1, v_pendingConsumer_886_);
lean_ctor_set(v___x_894_, 2, v_interestWaiter_891_);
lean_ctor_set(v___x_894_, 3, v_knownSize_888_);
lean_ctor_set(v___x_894_, 4, v_pendingIncompleteChunk_889_);
lean_ctor_set(v___x_894_, 5, v_closeError_890_);
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*6, v_closed_887_);
v___x_895_ = lean_st_ref_swap(v___y_892_, v___x_894_);
lean_dec(v___x_895_);
v___x_896_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_896_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingProducer_885_ = stack[0].m_obj;
lean_object* v_pendingConsumer_886_ = stack[1].m_obj;
uint8_t v_closed_887_ = stack[2].m_num;
lean_object* v_knownSize_888_ = stack[3].m_obj;
lean_object* v_pendingIncompleteChunk_889_ = stack[4].m_obj;
lean_object* v_closeError_890_ = stack[5].m_obj;
lean_object* v_interestWaiter_891_ = stack[6].m_obj;
lean_object* v___y_892_ = stack[7].m_obj;
lean_object* v_res_897_;
v_res_897_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_885_, v_pendingConsumer_886_, v_closed_887_, v_knownSize_888_, v_pendingIncompleteChunk_889_, v_closeError_890_, v_interestWaiter_891_, v___y_892_);
stack->m_obj
 = v_res_897_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object* v_pendingProducer_898_, lean_object* v_pendingConsumer_899_, lean_object* v_closed_900_, lean_object* v_knownSize_901_, lean_object* v_pendingIncompleteChunk_902_, lean_object* v_closeError_903_, lean_object* v_interestWaiter_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v_closed_boxed_907_; lean_object* v_res_908_; 
v_closed_boxed_907_ = lean_unbox(v_closed_900_);
v_res_908_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_898_, v_pendingConsumer_899_, v_closed_boxed_907_, v_knownSize_901_, v_pendingIncompleteChunk_902_, v_closeError_903_, v_interestWaiter_904_, v___y_905_);
lean_dec(v___y_905_);
return v_res_908_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object* v___f_909_, lean_object* v___y_910_, lean_object* v_x_911_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_921_; 
lean_dec_ref(v___f_909_);
v_a_913_ = lean_ctor_get(v_x_911_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_911_);
if (v_isSharedCheck_921_ == 0)
{
v___x_915_ = v_x_911_;
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v_x_911_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_920_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_923_; 
v_a_922_ = lean_ctor_get(v_x_911_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v_x_911_, 1);
lean_inc(v___y_910_);
v___x_923_ = lean_apply_3(v___f_909_, v_a_922_, v___y_910_, lean_box(0));
return v___x_923_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_909_ = stack[0].m_obj;
lean_object* v___y_910_ = stack[1].m_obj;
lean_object* v_x_911_ = stack[2].m_obj;
lean_object* v_res_924_;
v_res_924_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_909_, v___y_910_, v_x_911_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object* v___f_925_, lean_object* v___y_926_, lean_object* v_x_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_925_, v___y_926_, v_x_927_);
lean_dec(v___y_926_);
return v_res_929_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object* v_interestWaiter_934_, lean_object* v___f_935_, lean_object* v___f_936_, lean_object* v_x_937_){
_start:
{
if (lean_obj_tag(v_x_937_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v___f_936_);
lean_dec_ref(v___f_935_);
lean_dec(v_interestWaiter_934_);
v_a_939_ = lean_ctor_get(v_x_937_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_937_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v_x_937_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v_x_937_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_946_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_964_; 
v_a_948_ = lean_ctor_get(v_x_937_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_937_);
if (v_isSharedCheck_964_ == 0)
{
v___x_950_ = v_x_937_;
v_isShared_951_ = v_isSharedCheck_964_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v_x_937_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_964_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
uint8_t v___x_952_; 
v___x_952_ = lean_unbox(v_a_948_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_955_; 
lean_dec_ref(v___f_936_);
v___x_953_ = lean_unsigned_to_nat(0u);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v_interestWaiter_934_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_interestWaiter_934_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; 
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
v___x_957_ = lean_unbox(v_a_948_);
lean_dec(v_a_948_);
v___x_958_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_953_, v___x_957_, v___x_956_, v___f_935_);
return v___x_958_;
}
}
else
{
lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_del_object(v___x_950_);
lean_dec(v_a_948_);
lean_dec_ref(v___f_935_);
lean_dec(v_interestWaiter_934_);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = 0;
v___x_962_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1));
v___x_963_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_960_, v___x_961_, v___x_962_, v___f_936_);
return v___x_963_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_interestWaiter_934_ = stack[0].m_obj;
lean_object* v___f_935_ = stack[1].m_obj;
lean_object* v___f_936_ = stack[2].m_obj;
lean_object* v_x_937_ = stack[3].m_obj;
lean_object* v_res_965_;
v_res_965_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_934_, v___f_935_, v___f_936_, v_x_937_);
stack->m_obj
 = v_res_965_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object* v_interestWaiter_966_, lean_object* v___f_967_, lean_object* v___f_968_, lean_object* v_x_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_966_, v___f_967_, v___f_968_, v_x_969_);
return v_res_971_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object* v_pendingProducer_972_, uint8_t v_closed_973_, lean_object* v_knownSize_974_, lean_object* v_pendingIncompleteChunk_975_, lean_object* v_closeError_976_, lean_object* v_interestWaiter_977_, lean_object* v_pendingConsumer_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; lean_object* v___f_982_; 
v___x_981_ = lean_box(v_closed_973_);
v___f_982_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed), 9, 6);
lean_closure_set(v___f_982_, 0, v_pendingProducer_972_);
lean_closure_set(v___f_982_, 1, v_pendingConsumer_978_);
lean_closure_set(v___f_982_, 2, v___x_981_);
lean_closure_set(v___f_982_, 3, v_knownSize_974_);
lean_closure_set(v___f_982_, 4, v_pendingIncompleteChunk_975_);
lean_closure_set(v___f_982_, 5, v_closeError_976_);
if (lean_obj_tag(v_interestWaiter_977_) == 0)
{
lean_object* v___f_983_; lean_object* v___x_984_; uint8_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_inc(v___y_979_);
v___f_983_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_983_, 0, v___f_982_);
lean_closure_set(v___f_983_, 1, v___y_979_);
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = 0;
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_interestWaiter_977_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
v___x_988_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_984_, v___x_985_, v___x_987_, v___f_983_);
return v___x_988_;
}
else
{
lean_object* v_val_989_; lean_object* v_finished_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_val_989_ = lean_ctor_get(v_interestWaiter_977_, 0);
v_finished_990_ = lean_ctor_get(v_val_989_, 0);
lean_inc(v_finished_990_);
lean_inc(v___y_979_);
v___f_991_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_991_, 0, v___f_982_);
lean_closure_set(v___f_991_, 1, v___y_979_);
lean_inc_ref(v___f_991_);
v___f_992_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed), 5, 3);
lean_closure_set(v___f_992_, 0, v_interestWaiter_977_);
lean_closure_set(v___f_992_, 1, v___f_991_);
lean_closure_set(v___f_992_, 2, v___f_991_);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = 0;
v___x_995_ = lean_st_ref_get(v_finished_990_);
lean_dec(v_finished_990_);
v___x_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
v___x_998_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_993_, v___x_994_, v___x_997_, v___f_992_);
return v___x_998_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingProducer_972_ = stack[0].m_obj;
uint8_t v_closed_973_ = stack[1].m_num;
lean_object* v_knownSize_974_ = stack[2].m_obj;
lean_object* v_pendingIncompleteChunk_975_ = stack[3].m_obj;
lean_object* v_closeError_976_ = stack[4].m_obj;
lean_object* v_interestWaiter_977_ = stack[5].m_obj;
lean_object* v_pendingConsumer_978_ = stack[6].m_obj;
lean_object* v___y_979_ = stack[7].m_obj;
lean_object* v_res_999_;
v_res_999_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_972_, v_closed_973_, v_knownSize_974_, v_pendingIncompleteChunk_975_, v_closeError_976_, v_interestWaiter_977_, v_pendingConsumer_978_, v___y_979_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object* v_pendingProducer_1000_, lean_object* v_closed_1001_, lean_object* v_knownSize_1002_, lean_object* v_pendingIncompleteChunk_1003_, lean_object* v_closeError_1004_, lean_object* v_interestWaiter_1005_, lean_object* v_pendingConsumer_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v_closed_boxed_1009_; lean_object* v_res_1010_; 
v_closed_boxed_1009_ = lean_unbox(v_closed_1001_);
v_res_1010_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_1000_, v_closed_boxed_1009_, v_knownSize_1002_, v_pendingIncompleteChunk_1003_, v_closeError_1004_, v_interestWaiter_1005_, v_pendingConsumer_1006_, v___y_1007_);
lean_dec(v___y_1007_);
return v_res_1010_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object* v___f_1011_, lean_object* v___y_1012_, lean_object* v_x_1013_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v___f_1011_);
v_a_1015_ = lean_ctor_get(v_x_1013_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_x_1013_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1017_ = v_x_1013_;
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v_x_1013_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v_x_1013_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v_x_1013_, 1);
lean_inc(v___y_1012_);
v___x_1025_ = lean_apply_3(v___f_1011_, v_a_1024_, v___y_1012_, lean_box(0));
return v___x_1025_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1011_ = stack[0].m_obj;
lean_object* v___y_1012_ = stack[1].m_obj;
lean_object* v_x_1013_ = stack[2].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_1011_, v___y_1012_, v_x_1013_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object* v___f_1027_, lean_object* v___y_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_1027_, v___y_1028_, v_x_1029_);
lean_dec(v___y_1028_);
return v_res_1031_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object* v___f_1032_, lean_object* v_a_1033_, lean_object* v_x_1034_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v___f_1032_);
v_a_1036_ = lean_ctor_get(v_x_1034_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v_x_1034_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v_x_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1046_; 
v_a_1045_ = lean_ctor_get(v_x_1034_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v_x_1034_, 1);
lean_inc(v_a_1033_);
v___x_1046_ = lean_apply_3(v___f_1032_, v_a_1045_, v_a_1033_, lean_box(0));
return v___x_1046_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1032_ = stack[0].m_obj;
lean_object* v_a_1033_ = stack[1].m_obj;
lean_object* v_x_1034_ = stack[2].m_obj;
lean_object* v_res_1047_;
v_res_1047_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_1032_, v_a_1033_, v_x_1034_);
stack->m_obj
 = v_res_1047_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object* v___f_1048_, lean_object* v_a_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_1048_, v_a_1049_, v_x_1050_);
lean_dec(v_a_1049_);
return v_res_1052_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object* v_pendingConsumer_1057_, lean_object* v___f_1058_, lean_object* v___f_1059_, lean_object* v_x_1060_){
_start:
{
if (lean_obj_tag(v_x_1060_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v___f_1059_);
lean_dec_ref(v___f_1058_);
lean_dec(v_pendingConsumer_1057_);
v_a_1062_ = lean_ctor_get(v_x_1060_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_x_1060_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1064_ = v_x_1060_;
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v_x_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1087_; 
v_a_1071_ = lean_ctor_get(v_x_1060_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_x_1060_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1073_ = v_x_1060_;
v_isShared_1074_ = v_isSharedCheck_1087_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v_x_1060_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1087_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_unbox(v_a_1071_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec_ref(v___f_1059_);
v___x_1076_ = lean_unsigned_to_nat(0u);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v_pendingConsumer_1057_);
v___x_1078_ = v___x_1073_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_pendingConsumer_1057_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
v___x_1080_ = lean_unbox(v_a_1071_);
lean_dec(v_a_1071_);
v___x_1081_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1076_, v___x_1080_, v___x_1079_, v___f_1058_);
return v___x_1081_;
}
}
else
{
lean_object* v___x_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_del_object(v___x_1073_);
lean_dec(v_a_1071_);
lean_dec_ref(v___f_1058_);
lean_dec(v_pendingConsumer_1057_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = 0;
v___x_1085_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1));
v___x_1086_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1083_, v___x_1084_, v___x_1085_, v___f_1059_);
return v___x_1086_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingConsumer_1057_ = stack[0].m_obj;
lean_object* v___f_1058_ = stack[1].m_obj;
lean_object* v___f_1059_ = stack[2].m_obj;
lean_object* v_x_1060_ = stack[3].m_obj;
lean_object* v_res_1088_;
v_res_1088_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_1057_, v___f_1058_, v___f_1059_, v_x_1060_);
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object* v_pendingConsumer_1089_, lean_object* v___f_1090_, lean_object* v___f_1091_, lean_object* v_x_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_1089_, v___f_1090_, v___f_1091_, v_x_1092_);
return v_res_1094_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object* v_a_1095_, lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1106_; 
v_a_1098_ = lean_ctor_get(v_x_1096_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1100_ = v_x_1096_;
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v_x_1096_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1147_; 
v_a_1107_ = lean_ctor_get(v_x_1096_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1109_ = v_x_1096_;
v_isShared_1110_ = v_isSharedCheck_1147_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v_x_1096_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1147_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_pendingProducer_1111_; lean_object* v_pendingConsumer_1112_; lean_object* v_interestWaiter_1113_; uint8_t v_closed_1114_; lean_object* v_knownSize_1115_; lean_object* v_pendingIncompleteChunk_1116_; lean_object* v_closeError_1117_; lean_object* v___x_1118_; lean_object* v___f_1119_; lean_object* v___y_1121_; 
v_pendingProducer_1111_ = lean_ctor_get(v_a_1107_, 0);
lean_inc(v_pendingProducer_1111_);
v_pendingConsumer_1112_ = lean_ctor_get(v_a_1107_, 1);
lean_inc(v_pendingConsumer_1112_);
v_interestWaiter_1113_ = lean_ctor_get(v_a_1107_, 2);
lean_inc(v_interestWaiter_1113_);
v_closed_1114_ = lean_ctor_get_uint8(v_a_1107_, sizeof(void*)*6);
v_knownSize_1115_ = lean_ctor_get(v_a_1107_, 3);
lean_inc(v_knownSize_1115_);
v_pendingIncompleteChunk_1116_ = lean_ctor_get(v_a_1107_, 4);
lean_inc(v_pendingIncompleteChunk_1116_);
v_closeError_1117_ = lean_ctor_get(v_a_1107_, 5);
lean_inc(v_closeError_1117_);
lean_dec(v_a_1107_);
v___x_1118_ = lean_box(v_closed_1114_);
v___f_1119_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed), 9, 6);
lean_closure_set(v___f_1119_, 0, v_pendingProducer_1111_);
lean_closure_set(v___f_1119_, 1, v___x_1118_);
lean_closure_set(v___f_1119_, 2, v_knownSize_1115_);
lean_closure_set(v___f_1119_, 3, v_pendingIncompleteChunk_1116_);
lean_closure_set(v___f_1119_, 4, v_closeError_1117_);
lean_closure_set(v___f_1119_, 5, v_interestWaiter_1113_);
if (lean_obj_tag(v_pendingConsumer_1112_) == 1)
{
lean_object* v_val_1130_; 
v_val_1130_ = lean_ctor_get(v_pendingConsumer_1112_, 0);
lean_inc(v_val_1130_);
if (lean_obj_tag(v_val_1130_) == 1)
{
lean_object* v_finished_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1146_; 
lean_del_object(v___x_1109_);
v_finished_1131_ = lean_ctor_get(v_val_1130_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_val_1130_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1133_ = v_val_1130_;
v_isShared_1134_ = v_isSharedCheck_1146_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_finished_1131_);
lean_dec(v_val_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1146_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_finished_1135_; lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v_finished_1135_ = lean_ctor_get(v_finished_1131_, 0);
lean_inc(v_finished_1135_);
lean_dec_ref(v_finished_1131_);
lean_inc(v_a_1095_);
v___f_1136_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1136_, 0, v___f_1119_);
lean_closure_set(v___f_1136_, 1, v_a_1095_);
lean_inc_ref(v___f_1136_);
v___f_1137_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1137_, 0, v_pendingConsumer_1112_);
lean_closure_set(v___f_1137_, 1, v___f_1136_);
lean_closure_set(v___f_1137_, 2, v___f_1136_);
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = 0;
v___x_1140_ = lean_st_ref_get(v_finished_1135_);
lean_dec(v_finished_1135_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1140_);
v___x_1142_ = v___x_1133_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
v___x_1144_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1138_, v___x_1139_, v___x_1143_, v___f_1137_);
return v___x_1144_;
}
}
}
else
{
lean_dec(v_val_1130_);
v___y_1121_ = v_a_1095_;
goto v___jp_1120_;
}
}
else
{
v___y_1121_ = v_a_1095_;
goto v___jp_1120_;
}
v___jp_1120_:
{
lean_object* v___f_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1126_; 
lean_inc(v___y_1121_);
v___f_1122_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1122_, 0, v___f_1119_);
lean_closure_set(v___f_1122_, 1, v___y_1121_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = 0;
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v_pendingConsumer_1112_);
v___x_1126_ = v___x_1109_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_pendingConsumer_1112_);
v___x_1126_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
v___x_1128_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1123_, v___x_1124_, v___x_1127_, v___f_1122_);
return v___x_1128_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1095_ = stack[0].m_obj;
lean_object* v_x_1096_ = stack[1].m_obj;
lean_object* v_res_1148_;
v_res_1148_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_1095_, v_x_1096_);
stack->m_obj
 = v_res_1148_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object* v_a_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_1149_, v_x_1150_);
lean_dec(v_a_1149_);
return v_res_1152_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object* v_a_1153_){
_start:
{
lean_object* v___f_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_inc(v_a_1153_);
v___f_1155_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1155_, 0, v_a_1153_);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = 0;
v___x_1158_ = lean_st_ref_get(v_a_1153_);
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
v___x_1161_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1156_, v___x_1157_, v___x_1160_, v___f_1155_);
return v___x_1161_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1153_ = stack[0].m_obj;
lean_object* v_res_1162_;
v_res_1162_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_1153_);
stack->m_obj
 = v_res_1162_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object* v_a_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_1163_);
lean_dec(v_a_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object* v___y_1166_){
_start:
{
if (lean_obj_tag(v___y_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___y_1166_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___y_1166_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___y_1166_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___y_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
v_a_1175_ = lean_ctor_get(v___y_1166_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___y_1166_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v___y_1166_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___y_1166_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_fst_1179_; lean_object* v___x_1181_; 
v_fst_1179_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_fst_1179_);
lean_dec(v_a_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_fst_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_fst_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object* v_mutex_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = lean_io_basemutex_unlock(v_mutex_1184_);
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1184_ = stack[0].m_obj;
lean_object* v_x_1185_ = stack[1].m_obj;
lean_object* v_res_1190_;
v_res_1190_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(v_mutex_1184_, v_x_1185_);
stack->m_obj
 = v_res_1190_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(v_mutex_1191_, v_x_1192_);
lean_dec(v_x_1192_);
lean_dec(v_mutex_1191_);
return v_res_1194_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object* v_k_1195_, lean_object* v_ref_1196_, lean_object* v_x_1197_){
_start:
{
if (lean_obj_tag(v_x_1197_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_ref_1196_);
lean_dec_ref(v_k_1195_);
v_a_1199_ = lean_ctor_get(v_x_1197_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_x_1197_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1201_ = v_x_1197_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v_x_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
}
else
{
lean_object* v___x_1208_; 
lean_dec_ref_known(v_x_1197_, 1);
v___x_1208_ = lean_apply_2(v_k_1195_, v_ref_1196_, lean_box(0));
return v___x_1208_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1195_ = stack[0].m_obj;
lean_object* v_ref_1196_ = stack[1].m_obj;
lean_object* v_x_1197_ = stack[2].m_obj;
lean_object* v_res_1209_;
v_res_1209_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(v_k_1195_, v_ref_1196_, v_x_1197_);
stack->m_obj
 = v_res_1209_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object* v_k_1210_, lean_object* v_ref_1211_, lean_object* v_x_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(v_k_1210_, v_ref_1211_, v_x_1212_);
return v_res_1214_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object* v_mutex_1215_, lean_object* v___f_1216_){
_start:
{
lean_object* v___x_1218_; uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = 0;
v___x_1220_ = lean_io_basemutex_lock(v_mutex_1215_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
v___x_1223_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1218_, v___x_1219_, v___x_1222_, v___f_1216_);
return v___x_1223_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1215_ = stack[0].m_obj;
lean_object* v___f_1216_ = stack[1].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(v_mutex_1215_, v___f_1216_);
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_1225_, lean_object* v___f_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(v_mutex_1225_, v___f_1226_);
lean_dec(v_mutex_1225_);
return v_res_1228_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(lean_object* v_mutex_1230_, lean_object* v_k_1231_){
_start:
{
lean_object* v_ref_1233_; lean_object* v_mutex_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___y_1243_; 
v_ref_1233_ = lean_ctor_get(v_mutex_1230_, 0);
lean_inc(v_ref_1233_);
v_mutex_1234_ = lean_ctor_get(v_mutex_1230_, 1);
lean_inc_n(v_mutex_1234_, 2);
lean_dec_ref(v_mutex_1230_);
v___f_1235_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0));
v___f_1236_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1236_, 0, v_mutex_1234_);
v___f_1237_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1237_, 0, v_k_1231_);
lean_closure_set(v___f_1237_, 1, v_ref_1233_);
v___f_1238_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1238_, 0, v_mutex_1234_);
lean_closure_set(v___f_1238_, 1, v___f_1237_);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = 0;
v___x_1241_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1238_, v___f_1236_, v___x_1239_, v___x_1240_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1245_; 
v_a_1245_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1241_, 1);
if (lean_obj_tag(v_a_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_a_1246_ = lean_ctor_get(v_a_1245_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_a_1245_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v_a_1245_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v_a_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
v___y_1243_ = v___x_1251_;
goto v___jp_1242_;
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1262_; 
v_a_1254_ = lean_ctor_get(v_a_1245_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_a_1245_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1256_ = v_a_1245_;
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v_a_1245_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_fst_1258_; lean_object* v___x_1260_; 
v_fst_1258_ = lean_ctor_get(v_a_1254_, 0);
lean_inc(v_fst_1258_);
lean_dec(v_a_1254_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v_fst_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_fst_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v___y_1243_ = v___x_1260_;
goto v___jp_1242_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_a_1263_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v___x_1241_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1241_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_task_map(v___f_1235_, v_a_1263_, v___x_1239_, v___x_1240_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
v___jp_1242_:
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___y_1243_);
return v___x_1244_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1230_ = stack[0].m_obj;
lean_object* v_k_1231_ = stack[1].m_obj;
lean_object* v_res_1272_;
v_res_1272_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1230_, v_k_1231_);
stack->m_obj
 = v_res_1272_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___boxed(lean_object* v_mutex_1273_, lean_object* v_k_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1273_, v_k_1274_);
return v_res_1276_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03b2_1278_, lean_object* v_mutex_1279_, lean_object* v_k_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1279_, v_k_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1279_ = stack[2].m_obj;
lean_object* v_k_1280_ = stack[3].m_obj;
lean_object* v_res_1283_;
v_res_1283_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(lean_box(0), lean_box(0), v_mutex_1279_, v_k_1280_);
stack->m_obj
 = v_res_1283_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_00_u03b2_1285_, lean_object* v_mutex_1286_, lean_object* v_k_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(v_00_u03b1_1284_, v_00_u03b2_1285_, v_mutex_1286_, v_k_1287_);
return v_res_1289_;
}
}
lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0(lean_object* v_x_1290_){
_start:
{
if (lean_obj_tag(v_x_1290_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1300_; 
v_a_1292_ = lean_ctor_get(v_x_1290_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_x_1290_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1294_ = v_x_1290_;
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v_x_1290_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1302_; 
v_a_1301_ = lean_ctor_get(v_x_1290_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v_x_1290_, 1);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_a_1301_);
return v___x_1302_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_tryRecv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1290_ = stack[0].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l_Std_Http_Body_Stream_tryRecv___lam__0(v_x_1290_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(lean_object* v_x_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Std_Http_Body_Stream_tryRecv___lam__0(v_x_1304_);
return v_res_1306_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object* v_a_1307_, lean_object* v___f_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v___f_1308_);
v_a_1311_ = lean_ctor_get(v_x_1309_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1313_ = v_x_1309_;
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v_x_1309_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; 
v_a_1320_ = lean_ctor_get(v_x_1309_, 0);
lean_inc(v_a_1320_);
if (lean_obj_tag(v_a_1320_) == 1)
{
lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v___f_1308_);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_a_1320_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v_a_1320_, 0);
lean_dec(v_unused_1329_);
v___x_1322_ = v_a_1320_;
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
else
{
lean_dec(v_a_1320_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v_x_1309_);
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_x_1309_);
v___x_1325_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
return v___x_1326_;
}
}
}
else
{
lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_a_1320_);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v_x_1309_, 0);
lean_dec(v_unused_1342_);
v___x_1331_ = v_x_1309_;
v_isShared_1332_ = v_isSharedCheck_1341_;
goto v_resetjp_1330_;
}
else
{
lean_dec(v_x_1309_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1341_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = 0;
v___x_1335_ = lean_st_ref_get(v_a_1307_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1335_);
v___x_1337_ = v___x_1331_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
v___x_1339_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1333_, v___x_1334_, v___x_1338_, v___f_1308_);
return v___x_1339_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1307_ = stack[0].m_obj;
lean_object* v___f_1308_ = stack[1].m_obj;
lean_object* v_x_1309_ = stack[2].m_obj;
lean_object* v_res_1343_;
v_res_1343_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_a_1307_, v___f_1308_, v_x_1309_);
stack->m_obj
 = v_res_1343_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object* v_a_1344_, lean_object* v___f_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_a_1344_, v___f_1345_, v_x_1346_);
lean_dec(v_a_1344_);
return v_res_1348_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object* v_x_1353_){
_start:
{
if (lean_obj_tag(v_x_1353_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1363_; 
v_a_1355_ = lean_ctor_get(v_x_1353_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1353_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1357_ = v_x_1353_;
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v_x_1353_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1382_; 
v_a_1364_ = lean_ctor_get(v_x_1353_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1353_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1366_ = v_x_1353_;
v_isShared_1367_ = v_isSharedCheck_1382_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v_x_1353_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1382_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_closeError_1368_; 
v_closeError_1368_ = lean_ctor_get(v_a_1364_, 5);
lean_inc(v_closeError_1368_);
lean_dec(v_a_1364_);
if (lean_obj_tag(v_closeError_1368_) == 1)
{
lean_object* v_val_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1380_; 
v_val_1369_ = lean_ctor_get(v_closeError_1368_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_closeError_1368_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1371_ = v_closeError_1368_;
v_isShared_1372_ = v_isSharedCheck_1380_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_val_1369_);
lean_dec(v_closeError_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1380_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set_tag(v___x_1366_, 0);
lean_ctor_set(v___x_1366_, 0, v_val_1369_);
v___x_1374_ = v___x_1366_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_val_1369_);
v___x_1374_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1376_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1374_);
v___x_1376_ = v___x_1371_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
}
}
}
else
{
lean_object* v___x_1381_; 
lean_dec(v_closeError_1368_);
lean_del_object(v___x_1366_);
v___x_1381_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__1));
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1353_ = stack[0].m_obj;
lean_object* v_res_1383_;
v_res_1383_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_x_1353_);
stack->m_obj
 = v_res_1383_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object* v_x_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_x_1384_);
return v_res_1386_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(lean_object* v_done_1387_, lean_object* v___f_1388_, lean_object* v_x_1389_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v___f_1388_);
v_a_1391_ = lean_ctor_get(v_x_1389_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1393_ = v_x_1389_;
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v_x_1389_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
}
}
else
{
uint8_t v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec_ref_known(v_x_1389_, 1);
v___x_1400_ = 1;
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = 0;
v___x_1403_ = lean_box(v___x_1400_);
v___x_1404_ = lean_io_promise_resolve(v___x_1403_, v_done_1387_);
v___x_1405_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1406_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1401_, v___x_1402_, v___x_1405_, v___f_1388_);
return v___x_1406_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_done_1387_ = stack[0].m_obj;
lean_object* v___f_1388_ = stack[1].m_obj;
lean_object* v_x_1389_ = stack[2].m_obj;
lean_object* v_res_1407_;
v_res_1407_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(v_done_1387_, v___f_1388_, v_x_1389_);
stack->m_obj
 = v_res_1407_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed(lean_object* v_done_1408_, lean_object* v___f_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(v_done_1408_, v___f_1409_, v_x_1410_);
lean_dec(v_done_1408_);
return v_res_1412_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(lean_object* v_chunk_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_chunk_1413_);
v_a_1416_ = lean_ctor_get(v_x_1414_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v_x_1414_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v_x_1414_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
}
else
{
lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1433_; 
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1414_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v_x_1414_, 0);
lean_dec(v_unused_1434_);
v___x_1426_ = v_x_1414_;
v_isShared_1427_ = v_isSharedCheck_1433_;
goto v_resetjp_1425_;
}
else
{
lean_dec(v_x_1414_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1433_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_chunk_1413_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1428_);
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
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_chunk_1413_ = stack[0].m_obj;
lean_object* v_x_1414_ = stack[1].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(v_chunk_1413_, v_x_1414_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed(lean_object* v_chunk_1436_, lean_object* v_x_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(v_chunk_1436_, v_x_1437_);
return v_res_1439_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(lean_object* v_a_1442_, lean_object* v_x_1443_){
_start:
{
if (lean_obj_tag(v_x_1443_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
v_a_1445_ = lean_ctor_get(v_x_1443_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_x_1443_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1447_ = v_x_1443_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v_x_1443_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v_pendingProducer_1455_; 
v_a_1454_ = lean_ctor_get(v_x_1443_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v_x_1443_, 1);
v_pendingProducer_1455_ = lean_ctor_get(v_a_1454_, 0);
if (lean_obj_tag(v_pendingProducer_1455_) == 1)
{
lean_object* v_val_1456_; lean_object* v_pendingConsumer_1457_; lean_object* v_interestWaiter_1458_; uint8_t v_closed_1459_; lean_object* v_knownSize_1460_; lean_object* v_pendingIncompleteChunk_1461_; lean_object* v_closeError_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1480_; 
v_val_1456_ = lean_ctor_get(v_pendingProducer_1455_, 0);
lean_inc(v_val_1456_);
v_pendingConsumer_1457_ = lean_ctor_get(v_a_1454_, 1);
v_interestWaiter_1458_ = lean_ctor_get(v_a_1454_, 2);
v_closed_1459_ = lean_ctor_get_uint8(v_a_1454_, sizeof(void*)*6);
v_knownSize_1460_ = lean_ctor_get(v_a_1454_, 3);
v_pendingIncompleteChunk_1461_ = lean_ctor_get(v_a_1454_, 4);
v_closeError_1462_ = lean_ctor_get(v_a_1454_, 5);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_a_1454_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v_a_1454_, 0);
lean_dec(v_unused_1481_);
v___x_1464_ = v_a_1454_;
v_isShared_1465_ = v_isSharedCheck_1480_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_closeError_1462_);
lean_inc(v_pendingIncompleteChunk_1461_);
lean_inc(v_knownSize_1460_);
lean_inc(v_interestWaiter_1458_);
lean_inc(v_pendingConsumer_1457_);
lean_dec(v_a_1454_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1480_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_chunk_1466_; lean_object* v_done_1467_; lean_object* v___x_1468_; lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v_chunk_1466_ = lean_ctor_get(v_val_1456_, 0);
lean_inc_ref_n(v_chunk_1466_, 2);
v_done_1467_ = lean_ctor_get(v_val_1456_, 1);
lean_inc(v_done_1467_);
lean_dec(v_val_1456_);
v___x_1468_ = lean_box(0);
v___f_1469_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1469_, 0, v_chunk_1466_);
v___f_1470_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1470_, 0, v_done_1467_);
lean_closure_set(v___f_1470_, 1, v___f_1469_);
v___x_1471_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1460_, v_chunk_1466_);
lean_dec_ref(v_chunk_1466_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 3, v___x_1471_);
lean_ctor_set(v___x_1464_, 0, v___x_1468_);
v___x_1473_ = v___x_1464_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_pendingConsumer_1457_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_interestWaiter_1458_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_pendingIncompleteChunk_1461_);
lean_ctor_set(v_reuseFailAlloc_1479_, 5, v_closeError_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*6, v_closed_1459_);
v___x_1473_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = 0;
v___x_1476_ = lean_st_ref_swap(v_a_1442_, v___x_1473_);
lean_dec(v___x_1476_);
v___x_1477_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1478_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1474_, v___x_1475_, v___x_1477_, v___f_1470_);
return v___x_1478_;
}
}
}
else
{
lean_object* v___x_1482_; 
lean_dec(v_a_1454_);
v___x_1482_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_1482_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1442_ = stack[0].m_obj;
lean_object* v_x_1443_ = stack[1].m_obj;
lean_object* v_res_1483_;
v_res_1483_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(v_a_1442_, v_x_1443_);
stack->m_obj
 = v_res_1483_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1484_, lean_object* v_x_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(v_a_1484_, v_x_1485_);
lean_dec(v_a_1484_);
return v_res_1487_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(lean_object* v_a_1488_){
_start:
{
lean_object* v___f_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_inc(v_a_1488_);
v___f_1490_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1490_, 0, v_a_1488_);
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = 0;
v___x_1493_ = lean_st_ref_get(v_a_1488_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
v___x_1496_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1491_, v___x_1492_, v___x_1495_, v___f_1490_);
return v___x_1496_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1488_ = stack[0].m_obj;
lean_object* v_res_1497_;
v_res_1497_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1488_);
stack->m_obj
 = v_res_1497_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___boxed(lean_object* v_a_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1498_);
lean_dec(v_a_1498_);
return v_res_1500_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object* v_a_1502_){
_start:
{
lean_object* v___f_1504_; lean_object* v___f_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___f_1504_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0));
lean_inc(v_a_1502_);
v___f_1505_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1505_, 0, v_a_1502_);
lean_closure_set(v___f_1505_, 1, v___f_1504_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = 0;
v___x_1508_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_1502_);
v___x_1509_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1506_, v___x_1507_, v___x_1508_, v___f_1505_);
return v___x_1509_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1502_ = stack[0].m_obj;
lean_object* v_res_1510_;
v_res_1510_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_1502_);
stack->m_obj
 = v_res_1510_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object* v_a_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_1511_);
lean_dec(v_a_1511_);
return v_res_1513_;
}
}
lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1(lean_object* v___y_1514_, lean_object* v___f_1515_, lean_object* v_x_1516_){
_start:
{
if (lean_obj_tag(v_x_1516_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___f_1515_);
v_a_1518_ = lean_ctor_get(v_x_1516_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_x_1516_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1520_ = v_x_1516_;
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v_x_1516_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
}
}
else
{
lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec_ref_known(v_x_1516_, 1);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = 0;
v___x_1529_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1514_);
v___x_1530_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1527_, v___x_1528_, v___x_1529_, v___f_1515_);
return v___x_1530_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_tryRecv___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1514_ = stack[0].m_obj;
lean_object* v___f_1515_ = stack[1].m_obj;
lean_object* v_x_1516_ = stack[2].m_obj;
lean_object* v_res_1531_;
v_res_1531_ = l_Std_Http_Body_Stream_tryRecv___lam__1(v___y_1514_, v___f_1515_, v_x_1516_);
stack->m_obj
 = v_res_1531_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(lean_object* v___y_1532_, lean_object* v___f_1533_, lean_object* v_x_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Std_Http_Body_Stream_tryRecv___lam__1(v___y_1532_, v___f_1533_, v_x_1534_);
lean_dec(v___y_1532_);
return v_res_1536_;
}
}
lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2(lean_object* v___f_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___f_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_inc(v___y_1538_);
v___f_1540_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecv___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1540_, 0, v___y_1538_);
lean_closure_set(v___f_1540_, 1, v___f_1537_);
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = 0;
v___x_1543_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1538_);
v___x_1544_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1541_, v___x_1542_, v___x_1543_, v___f_1540_);
return v___x_1544_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_tryRecv___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1537_ = stack[0].m_obj;
lean_object* v___y_1538_ = stack[1].m_obj;
lean_object* v_res_1545_;
v_res_1545_ = l_Std_Http_Body_Stream_tryRecv___lam__2(v___f_1537_, v___y_1538_);
stack->m_obj
 = v_res_1545_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2___boxed(lean_object* v___f_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Std_Http_Body_Stream_tryRecv___lam__2(v___f_1546_, v___y_1547_);
lean_dec(v___y_1547_);
return v_res_1549_;
}
}
lean_object* l_Std_Http_Body_Stream_tryRecv(lean_object* v_stream_1553_){
_start:
{
lean_object* v___f_1555_; lean_object* v___x_1556_; 
v___f_1555_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecv___closed__1));
v___x_1556_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1553_, v___f_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_1553_ = stack[0].m_obj;
lean_object* v_res_1557_;
v_res_1557_ = l_Std_Http_Body_Stream_tryRecv(v_stream_1553_);
stack->m_obj
 = v_res_1557_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___boxed(lean_object* v_stream_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Std_Http_Body_Stream_tryRecv(v_stream_1558_);
return v_res_1560_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(lean_object* v_x_1561_){
_start:
{
uint8_t v___y_1564_; 
if (lean_obj_tag(v_x_1561_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1576_; 
v_a_1568_ = lean_ctor_get(v_x_1561_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_x_1561_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1570_ = v_x_1561_;
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v_x_1561_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v_pendingProducer_1578_; 
v_a_1577_ = lean_ctor_get(v_x_1561_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v_x_1561_, 1);
v_pendingProducer_1578_ = lean_ctor_get(v_a_1577_, 0);
if (lean_obj_tag(v_pendingProducer_1578_) == 0)
{
uint8_t v_closed_1579_; 
v_closed_1579_ = lean_ctor_get_uint8(v_a_1577_, sizeof(void*)*6);
lean_dec(v_a_1577_);
v___y_1564_ = v_closed_1579_;
goto v___jp_1563_;
}
else
{
uint8_t v___x_1580_; 
lean_dec(v_a_1577_);
v___x_1580_ = 1;
v___y_1564_ = v___x_1580_;
goto v___jp_1563_;
}
}
v___jp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_box(v___y_1564_);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1561_ = stack[0].m_obj;
lean_object* v_res_1581_;
v_res_1581_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(v_x_1561_);
stack->m_obj
 = v_res_1581_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed(lean_object* v_x_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(v_x_1582_);
return v_res_1584_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(lean_object* v_a_1586_){
_start:
{
lean_object* v___f_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___f_1588_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0));
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = 0;
v___x_1591_ = lean_st_ref_get(v_a_1586_);
v___x_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
v___x_1594_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1589_, v___x_1590_, v___x_1593_, v___f_1588_);
return v___x_1594_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1586_ = stack[0].m_obj;
lean_object* v_res_1595_;
v_res_1595_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v_a_1586_);
stack->m_obj
 = v_res_1595_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___boxed(lean_object* v_a_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v_a_1596_);
lean_dec(v_a_1596_);
return v_res_1598_;
}
}
lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0(lean_object* v_x_1599_){
_start:
{
if (lean_obj_tag(v_x_1599_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1609_; 
v_a_1601_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1603_ = v_x_1599_;
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v_x_1599_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
return v___x_1607_;
}
}
}
else
{
lean_object* v_a_1610_; 
v_a_1610_ = lean_ctor_get(v_x_1599_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v_x_1599_, 1);
if (lean_obj_tag(v_a_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1619_; 
v_a_1611_ = lean_ctor_get(v_a_1610_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_a_1610_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1613_ = v_a_1610_;
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v_a_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1629_; 
v_a_1620_ = lean_ctor_get(v_a_1610_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_a_1610_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1622_ = v_a_1610_;
v_isShared_1623_ = v_isSharedCheck_1629_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v_a_1610_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1629_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v_a_1620_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1624_);
v___x_1626_ = v___x_1622_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_tryRecvBody___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1599_ = stack[0].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Std_Http_Body_Stream_tryRecvBody___lam__0(v_x_1599_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed(lean_object* v_x_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Std_Http_Body_Stream_tryRecvBody___lam__0(v_x_1631_);
return v_res_1633_;
}
}
lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1(lean_object* v___y_1638_, lean_object* v___f_1639_, lean_object* v_x_1640_){
_start:
{
if (lean_obj_tag(v_x_1640_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v___f_1639_);
v_a_1642_ = lean_ctor_get(v_x_1640_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1644_ = v_x_1640_;
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v_x_1640_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1651_; uint8_t v___x_1652_; 
v_a_1651_ = lean_ctor_get(v_x_1640_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v_x_1640_, 1);
v___x_1652_ = lean_unbox(v_a_1651_);
lean_dec(v_a_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v___f_1639_);
v___x_1653_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1));
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1654_ = lean_unsigned_to_nat(0u);
v___x_1655_ = 0;
v___x_1656_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1638_);
v___x_1657_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1654_, v___x_1655_, v___x_1656_, v___f_1639_);
return v___x_1657_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_tryRecvBody___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1638_ = stack[0].m_obj;
lean_object* v___f_1639_ = stack[1].m_obj;
lean_object* v_x_1640_ = stack[2].m_obj;
lean_object* v_res_1658_;
v_res_1658_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1(v___y_1638_, v___f_1639_, v_x_1640_);
stack->m_obj
 = v_res_1658_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed(lean_object* v___y_1659_, lean_object* v___f_1660_, lean_object* v_x_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1(v___y_1659_, v___f_1660_, v_x_1661_);
lean_dec(v___y_1659_);
return v_res_1663_;
}
}
lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2(lean_object* v___y_1664_, lean_object* v___f_1665_, lean_object* v_x_1666_){
_start:
{
if (lean_obj_tag(v_x_1666_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1676_; 
lean_dec_ref(v___f_1665_);
v_a_1668_ = lean_ctor_get(v_x_1666_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1666_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1670_ = v_x_1666_;
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v_x_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
}
else
{
lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec_ref_known(v_x_1666_, 1);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = 0;
v___x_1679_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_1664_);
v___x_1680_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1677_, v___x_1678_, v___x_1679_, v___f_1665_);
return v___x_1680_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_tryRecvBody___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1664_ = stack[0].m_obj;
lean_object* v___f_1665_ = stack[1].m_obj;
lean_object* v_x_1666_ = stack[2].m_obj;
lean_object* v_res_1681_;
v_res_1681_ = l_Std_Http_Body_Stream_tryRecvBody___lam__2(v___y_1664_, v___f_1665_, v_x_1666_);
stack->m_obj
 = v_res_1681_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed(lean_object* v___y_1682_, lean_object* v___f_1683_, lean_object* v_x_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Std_Http_Body_Stream_tryRecvBody___lam__2(v___y_1682_, v___f_1683_, v_x_1684_);
lean_dec(v___y_1682_);
return v_res_1686_;
}
}
lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3(lean_object* v___f_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc_n(v___y_1688_, 2);
v___f_1690_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1690_, 0, v___y_1688_);
lean_closure_set(v___f_1690_, 1, v___f_1687_);
v___f_1691_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1691_, 0, v___y_1688_);
lean_closure_set(v___f_1691_, 1, v___f_1690_);
v___x_1692_ = lean_unsigned_to_nat(0u);
v___x_1693_ = 0;
v___x_1694_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1688_);
v___x_1695_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1692_, v___x_1693_, v___x_1694_, v___f_1691_);
return v___x_1695_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_tryRecvBody___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1687_ = stack[0].m_obj;
lean_object* v___y_1688_ = stack[1].m_obj;
lean_object* v_res_1696_;
v_res_1696_ = l_Std_Http_Body_Stream_tryRecvBody___lam__3(v___f_1687_, v___y_1688_);
stack->m_obj
 = v_res_1696_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed(lean_object* v___f_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_Http_Body_Stream_tryRecvBody___lam__3(v___f_1697_, v___y_1698_);
lean_dec(v___y_1698_);
return v_res_1700_;
}
}
lean_object* l_Std_Http_Body_Stream_tryRecvBody(lean_object* v_stream_1704_){
_start:
{
lean_object* v___f_1706_; lean_object* v___x_1707_; 
v___f_1706_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_1707_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1704_, v___f_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_tryRecvBody_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_1704_ = stack[0].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_1704_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___boxed(lean_object* v_stream_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_1709_);
return v_res_1711_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v_pendingProducer_1715_; lean_object* v_pendingConsumer_1716_; lean_object* v_interestWaiter_1717_; uint8_t v_closed_1718_; lean_object* v_knownSize_1719_; lean_object* v_pendingIncompleteChunk_1720_; lean_object* v_closeError_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1748_; 
v___x_1714_ = lean_st_ref_get(v_a_1712_);
v_pendingProducer_1715_ = lean_ctor_get(v___x_1714_, 0);
v_pendingConsumer_1716_ = lean_ctor_get(v___x_1714_, 1);
v_interestWaiter_1717_ = lean_ctor_get(v___x_1714_, 2);
v_closed_1718_ = lean_ctor_get_uint8(v___x_1714_, sizeof(void*)*6);
v_knownSize_1719_ = lean_ctor_get(v___x_1714_, 3);
v_pendingIncompleteChunk_1720_ = lean_ctor_get(v___x_1714_, 4);
v_closeError_1721_ = lean_ctor_get(v___x_1714_, 5);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1723_ = v___x_1714_;
v_isShared_1724_ = v_isSharedCheck_1748_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_closeError_1721_);
lean_inc(v_pendingIncompleteChunk_1720_);
lean_inc(v_knownSize_1719_);
lean_inc(v_interestWaiter_1717_);
lean_inc(v_pendingConsumer_1716_);
lean_inc(v_pendingProducer_1715_);
lean_dec(v___x_1714_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1748_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___y_1726_; lean_object* v_interestWaiter_1727_; lean_object* v___y_1728_; lean_object* v_pendingConsumer_1735_; lean_object* v___y_1736_; 
if (lean_obj_tag(v_pendingConsumer_1716_) == 1)
{
lean_object* v_val_1742_; 
v_val_1742_ = lean_ctor_get(v_pendingConsumer_1716_, 0);
if (lean_obj_tag(v_val_1742_) == 1)
{
lean_object* v_finished_1743_; lean_object* v_finished_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v_finished_1743_ = lean_ctor_get(v_val_1742_, 0);
v_finished_1744_ = lean_ctor_get(v_finished_1743_, 0);
v___x_1745_ = lean_st_ref_get(v_finished_1744_);
v___x_1746_ = lean_unbox(v___x_1745_);
lean_dec(v___x_1745_);
if (v___x_1746_ == 0)
{
v_pendingConsumer_1735_ = v_pendingConsumer_1716_;
v___y_1736_ = v_a_1712_;
goto v___jp_1734_;
}
else
{
lean_object* v___x_1747_; 
lean_dec_ref_known(v_pendingConsumer_1716_, 1);
v___x_1747_ = lean_box(0);
v_pendingConsumer_1735_ = v___x_1747_;
v___y_1736_ = v_a_1712_;
goto v___jp_1734_;
}
}
else
{
v_pendingConsumer_1735_ = v_pendingConsumer_1716_;
v___y_1736_ = v_a_1712_;
goto v___jp_1734_;
}
}
else
{
v_pendingConsumer_1735_ = v_pendingConsumer_1716_;
v___y_1736_ = v_a_1712_;
goto v___jp_1734_;
}
v___jp_1725_:
{
lean_object* v___x_1730_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 2, v_interestWaiter_1727_);
lean_ctor_set(v___x_1723_, 1, v___y_1726_);
v___x_1730_ = v___x_1723_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_pendingProducer_1715_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___y_1726_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_interestWaiter_1727_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_knownSize_1719_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_pendingIncompleteChunk_1720_);
lean_ctor_set(v_reuseFailAlloc_1733_, 5, v_closeError_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*6, v_closed_1718_);
v___x_1730_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_st_ref_swap(v___y_1728_, v___x_1730_);
lean_dec(v___x_1732_);
return v___x_1731_;
}
}
v___jp_1734_:
{
if (lean_obj_tag(v_interestWaiter_1717_) == 0)
{
v___y_1726_ = v_pendingConsumer_1735_;
v_interestWaiter_1727_ = v_interestWaiter_1717_;
v___y_1728_ = v___y_1736_;
goto v___jp_1725_;
}
else
{
lean_object* v_val_1737_; lean_object* v_finished_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_val_1737_ = lean_ctor_get(v_interestWaiter_1717_, 0);
v_finished_1738_ = lean_ctor_get(v_val_1737_, 0);
v___x_1739_ = lean_st_ref_get(v_finished_1738_);
v___x_1740_ = lean_unbox(v___x_1739_);
lean_dec(v___x_1739_);
if (v___x_1740_ == 0)
{
v___y_1726_ = v_pendingConsumer_1735_;
v_interestWaiter_1727_ = v_interestWaiter_1717_;
v___y_1728_ = v___y_1736_;
goto v___jp_1725_;
}
else
{
lean_object* v___x_1741_; 
lean_dec_ref_known(v_interestWaiter_1717_, 1);
v___x_1741_ = lean_box(0);
v___y_1726_ = v_pendingConsumer_1735_;
v_interestWaiter_1727_ = v___x_1741_;
v___y_1728_ = v___y_1736_;
goto v___jp_1725_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1712_ = stack[0].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_1712_);
stack->m_obj
 = v_res_1749_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object* v_a_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_1750_);
lean_dec(v_a_1750_);
return v_res_1752_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; lean_object* v_pendingProducer_1756_; 
v___x_1755_ = lean_st_ref_get(v_a_1753_);
v_pendingProducer_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_pendingProducer_1756_);
if (lean_obj_tag(v_pendingProducer_1756_) == 1)
{
lean_object* v_val_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1786_; 
v_val_1757_ = lean_ctor_get(v_pendingProducer_1756_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_pendingProducer_1756_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1759_ = v_pendingProducer_1756_;
v_isShared_1760_ = v_isSharedCheck_1786_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_val_1757_);
lean_dec(v_pendingProducer_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1786_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_pendingConsumer_1761_; lean_object* v_interestWaiter_1762_; uint8_t v_closed_1763_; lean_object* v_knownSize_1764_; lean_object* v_pendingIncompleteChunk_1765_; lean_object* v_closeError_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1784_; 
v_pendingConsumer_1761_ = lean_ctor_get(v___x_1755_, 1);
v_interestWaiter_1762_ = lean_ctor_get(v___x_1755_, 2);
v_closed_1763_ = lean_ctor_get_uint8(v___x_1755_, sizeof(void*)*6);
v_knownSize_1764_ = lean_ctor_get(v___x_1755_, 3);
v_pendingIncompleteChunk_1765_ = lean_ctor_get(v___x_1755_, 4);
v_closeError_1766_ = lean_ctor_get(v___x_1755_, 5);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v___x_1755_, 0);
lean_dec(v_unused_1785_);
v___x_1768_ = v___x_1755_;
v_isShared_1769_ = v_isSharedCheck_1784_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_closeError_1766_);
lean_inc(v_pendingIncompleteChunk_1765_);
lean_inc(v_knownSize_1764_);
lean_inc(v_interestWaiter_1762_);
lean_inc(v_pendingConsumer_1761_);
lean_dec(v___x_1755_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1784_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_chunk_1770_; lean_object* v_done_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v_chunk_1770_ = lean_ctor_get(v_val_1757_, 0);
lean_inc_ref(v_chunk_1770_);
v_done_1771_ = lean_ctor_get(v_val_1757_, 1);
lean_inc(v_done_1771_);
lean_dec(v_val_1757_);
v___x_1772_ = lean_box(0);
v___x_1773_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1764_, v_chunk_1770_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 3, v___x_1773_);
lean_ctor_set(v___x_1768_, 0, v___x_1772_);
v___x_1775_ = v___x_1768_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_pendingConsumer_1761_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_interestWaiter_1762_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_pendingIncompleteChunk_1765_);
lean_ctor_set(v_reuseFailAlloc_1783_, 5, v_closeError_1766_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*6, v_closed_1763_);
v___x_1775_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1776_ = lean_st_ref_swap(v_a_1753_, v___x_1775_);
lean_dec(v___x_1776_);
v___x_1777_ = 1;
v___x_1778_ = lean_box(v___x_1777_);
v___x_1779_ = lean_io_promise_resolve(v___x_1778_, v_done_1771_);
lean_dec(v_done_1771_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v_chunk_1770_);
v___x_1781_ = v___x_1759_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_chunk_1770_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
else
{
lean_object* v___x_1787_; 
lean_dec(v_pendingProducer_1756_);
lean_dec(v___x_1755_);
v___x_1787_ = lean_box(0);
return v___x_1787_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1753_ = stack[0].m_obj;
lean_object* v_res_1788_;
v_res_1788_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_1753_);
stack->m_obj
 = v_res_1788_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object* v_a_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_1789_);
lean_dec(v_a_1789_);
return v_res_1791_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; lean_object* v_interestWaiter_1795_; 
v___x_1794_ = lean_st_ref_get(v_a_1792_);
v_interestWaiter_1795_ = lean_ctor_get(v___x_1794_, 2);
lean_inc(v_interestWaiter_1795_);
if (lean_obj_tag(v_interestWaiter_1795_) == 1)
{
lean_object* v_pendingProducer_1796_; lean_object* v_pendingConsumer_1797_; uint8_t v_closed_1798_; lean_object* v_knownSize_1799_; lean_object* v_pendingIncompleteChunk_1800_; lean_object* v_closeError_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1814_; 
v_pendingProducer_1796_ = lean_ctor_get(v___x_1794_, 0);
v_pendingConsumer_1797_ = lean_ctor_get(v___x_1794_, 1);
v_closed_1798_ = lean_ctor_get_uint8(v___x_1794_, sizeof(void*)*6);
v_knownSize_1799_ = lean_ctor_get(v___x_1794_, 3);
v_pendingIncompleteChunk_1800_ = lean_ctor_get(v___x_1794_, 4);
v_closeError_1801_ = lean_ctor_get(v___x_1794_, 5);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v___x_1794_, 2);
lean_dec(v_unused_1815_);
v___x_1803_ = v___x_1794_;
v_isShared_1804_ = v_isSharedCheck_1814_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_closeError_1801_);
lean_inc(v_pendingIncompleteChunk_1800_);
lean_inc(v_knownSize_1799_);
lean_inc(v_pendingConsumer_1797_);
lean_inc(v_pendingProducer_1796_);
lean_dec(v___x_1794_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1814_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_val_1805_; uint8_t v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
v_val_1805_ = lean_ctor_get(v_interestWaiter_1795_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v_interestWaiter_1795_, 1);
v___x_1806_ = 1;
v___x_1807_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1805_, v___x_1806_);
lean_dec(v_val_1805_);
v___x_1808_ = lean_box(0);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 2, v___x_1808_);
v___x_1810_ = v___x_1803_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_pendingProducer_1796_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_pendingConsumer_1797_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1813_, 3, v_knownSize_1799_);
lean_ctor_set(v_reuseFailAlloc_1813_, 4, v_pendingIncompleteChunk_1800_);
lean_ctor_set(v_reuseFailAlloc_1813_, 5, v_closeError_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1813_, sizeof(void*)*6, v_closed_1798_);
v___x_1810_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_st_ref_swap(v_a_1792_, v___x_1810_);
lean_dec(v___x_1812_);
return v___x_1811_;
}
}
}
else
{
lean_object* v___x_1816_; 
lean_dec(v_interestWaiter_1795_);
lean_dec(v___x_1794_);
v___x_1816_ = lean_box(0);
return v___x_1816_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1792_ = stack[0].m_obj;
lean_object* v_res_1817_;
v_res_1817_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_1792_);
stack->m_obj
 = v_res_1817_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object* v_a_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_1818_);
lean_dec(v_a_1818_);
return v_res_1820_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object* v_mutex_1821_, lean_object* v_k_1822_){
_start:
{
lean_object* v_ref_1824_; lean_object* v_mutex_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_ref_1824_ = lean_ctor_get(v_mutex_1821_, 0);
lean_inc(v_ref_1824_);
v_mutex_1825_ = lean_ctor_get(v_mutex_1821_, 1);
lean_inc(v_mutex_1825_);
lean_dec_ref(v_mutex_1821_);
v___x_1826_ = lean_io_basemutex_lock(v_mutex_1825_);
v___x_1827_ = lean_apply_2(v_k_1822_, v_ref_1824_, lean_box(0));
v___x_1828_ = lean_io_basemutex_unlock(v_mutex_1825_);
lean_dec(v_mutex_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1821_ = stack[0].m_obj;
lean_object* v_k_1822_ = stack[1].m_obj;
lean_object* v_res_1829_;
v_res_1829_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1821_, v_k_1822_);
stack->m_obj
 = v_res_1829_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object* v_mutex_1830_, lean_object* v_k_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1830_, v_k_1831_);
return v_res_1833_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object* v_00_u03b1_1834_, lean_object* v_00_u03b2_1835_, lean_object* v_mutex_1836_, lean_object* v_k_1837_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1836_, v_k_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1836_ = stack[2].m_obj;
lean_object* v_k_1837_ = stack[3].m_obj;
lean_object* v_res_1840_;
v_res_1840_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_box(0), lean_box(0), v_mutex_1836_, v_k_1837_);
stack->m_obj
 = v_res_1840_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_mutex_1843_, lean_object* v_k_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(v_00_u03b1_1841_, v_00_u03b2_1842_, v_mutex_1843_, v_k_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object* v_x_1852_){
_start:
{
if (lean_obj_tag(v_x_1852_) == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2));
return v___x_1853_;
}
else
{
lean_object* v_val_1854_; 
v_val_1854_ = lean_ctor_get(v_x_1852_, 0);
lean_inc(v_val_1854_);
return v_val_1854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___boxed(lean_object* v_x_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(v_x_1855_);
lean_dec(v_x_1855_);
return v_res_1856_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2));
v___x_1863_ = lean_task_pure(v___x_1862_);
return v___x_1863_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_1865_ = lean_task_pure(v___x_1864_);
return v___x_1865_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object* v___f_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v_closed_1871_; 
v___x_1869_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_1867_);
v___x_1870_ = lean_st_ref_get(v___y_1867_);
v_closed_1871_ = lean_ctor_get_uint8(v___x_1870_, sizeof(void*)*6);
if (v_closed_1871_ == 0)
{
uint8_t v___x_1872_; lean_object* v___x_1873_; 
lean_dec(v___x_1870_);
v___x_1872_ = 1;
v___x_1873_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_1867_);
if (lean_obj_tag(v___x_1873_) == 1)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref(v___f_1866_);
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
v___x_1875_ = lean_task_pure(v___x_1874_);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; lean_object* v_pendingConsumer_1877_; 
lean_dec(v___x_1873_);
v___x_1876_ = lean_st_ref_get(v___y_1867_);
v_pendingConsumer_1877_ = lean_ctor_get(v___x_1876_, 1);
if (lean_obj_tag(v_pendingConsumer_1877_) == 0)
{
lean_object* v_pendingProducer_1878_; lean_object* v_interestWaiter_1879_; uint8_t v_closed_1880_; lean_object* v_knownSize_1881_; lean_object* v_pendingIncompleteChunk_1882_; lean_object* v_closeError_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1898_; 
v_pendingProducer_1878_ = lean_ctor_get(v___x_1876_, 0);
v_interestWaiter_1879_ = lean_ctor_get(v___x_1876_, 2);
v_closed_1880_ = lean_ctor_get_uint8(v___x_1876_, sizeof(void*)*6);
v_knownSize_1881_ = lean_ctor_get(v___x_1876_, 3);
v_pendingIncompleteChunk_1882_ = lean_ctor_get(v___x_1876_, 4);
v_closeError_1883_ = lean_ctor_get(v___x_1876_, 5);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v___x_1876_, 1);
lean_dec(v_unused_1899_);
v___x_1885_ = v___x_1876_;
v_isShared_1886_ = v_isSharedCheck_1898_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_closeError_1883_);
lean_inc(v_pendingIncompleteChunk_1882_);
lean_inc(v_knownSize_1881_);
lean_inc(v_interestWaiter_1879_);
lean_inc(v_pendingProducer_1878_);
lean_dec(v___x_1876_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1898_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1887_ = lean_io_promise_new();
lean_inc(v___x_1887_);
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v___x_1889_);
v___x_1891_ = v___x_1885_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_pendingProducer_1878_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v_interestWaiter_1879_);
lean_ctor_set(v_reuseFailAlloc_1897_, 3, v_knownSize_1881_);
lean_ctor_set(v_reuseFailAlloc_1897_, 4, v_pendingIncompleteChunk_1882_);
lean_ctor_set(v_reuseFailAlloc_1897_, 5, v_closeError_1883_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*6, v_closed_1880_);
v___x_1891_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1892_ = lean_st_ref_swap(v___y_1867_, v___x_1891_);
lean_dec(v___x_1892_);
v___x_1893_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_1867_);
v___x_1894_ = lean_io_promise_result_opt(v___x_1887_);
lean_dec(v___x_1887_);
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_task_map(v___f_1866_, v___x_1894_, v___x_1895_, v___x_1872_);
return v___x_1896_;
}
}
}
else
{
lean_object* v___x_1900_; 
lean_dec(v___x_1876_);
lean_dec_ref(v___f_1866_);
v___x_1900_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3);
return v___x_1900_;
}
}
}
else
{
lean_object* v_closeError_1901_; 
lean_dec_ref(v___f_1866_);
v_closeError_1901_ = lean_ctor_get(v___x_1870_, 5);
lean_inc(v_closeError_1901_);
lean_dec(v___x_1870_);
if (lean_obj_tag(v_closeError_1901_) == 0)
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4);
return v___x_1902_;
}
else
{
lean_object* v_val_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1911_; 
v_val_1903_ = lean_ctor_get(v_closeError_1901_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_closeError_1901_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1905_ = v_closeError_1901_;
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_val_1903_);
lean_dec(v_closeError_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 0);
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_val_1903_);
v___x_1908_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_task_pure(v___x_1908_);
return v___x_1909_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1866_ = stack[0].m_obj;
lean_object* v___y_1867_ = stack[1].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(v___f_1866_, v___y_1867_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object* v___f_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(v___f_1913_, v___y_1914_);
lean_dec(v___y_1914_);
return v_res_1916_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object* v_stream_1920_){
_start:
{
lean_object* v___f_1922_; lean_object* v___x_1923_; 
v___f_1922_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1));
v___x_1923_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_1920_, v___f_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_1920_ = stack[0].m_obj;
lean_object* v_res_1924_;
v_res_1924_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1920_);
stack->m_obj
 = v_res_1924_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object* v_stream_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1925_);
return v_res_1927_;
}
}
lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object* v_x_1928_){
_start:
{
if (lean_obj_tag(v_x_1928_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1938_; 
v_a_1930_ = lean_ctor_get(v_x_1928_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_x_1928_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1932_ = v_x_1928_;
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v_x_1928_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1940_; 
v_a_1939_ = lean_ctor_get(v_x_1928_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v_x_1928_, 1);
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1939_);
return v___x_1940_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1928_ = stack[0].m_obj;
lean_object* v_res_1941_;
v_res_1941_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_1928_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object* v_x_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_1942_);
return v_res_1944_;
}
}
lean_object* l_Std_Http_Body_Stream_recv(lean_object* v_stream_1946_){
_start:
{
lean_object* v___f_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___f_1948_ = ((lean_object*)(l_Std_Http_Body_Stream_recv___closed__0));
v___x_1949_ = lean_unsigned_to_nat(0u);
v___x_1950_ = 0;
v___x_1951_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1946_);
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
v___x_1954_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1949_, v___x_1950_, v___x_1953_, v___f_1948_);
return v___x_1954_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_1946_ = stack[0].m_obj;
lean_object* v_res_1955_;
v_res_1955_ = l_Std_Http_Body_Stream_recv(v_stream_1946_);
stack->m_obj
 = v_res_1955_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object* v_stream_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Std_Http_Body_Stream_recv(v_stream_1956_);
return v_res_1958_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(uint8_t v___x_1959_, lean_object* v_knownSize_1960_, lean_object* v_closeError_1961_, lean_object* v_____r_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
lean_ctor_set(v___x_1966_, 2, v___x_1965_);
lean_ctor_set(v___x_1966_, 3, v_knownSize_1960_);
lean_ctor_set(v___x_1966_, 4, v___x_1965_);
lean_ctor_set(v___x_1966_, 5, v_closeError_1961_);
lean_ctor_set_uint8(v___x_1966_, sizeof(void*)*6, v___x_1959_);
v___x_1967_ = lean_st_ref_swap(v___y_1963_, v___x_1966_);
lean_dec(v___x_1967_);
v___x_1968_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_1968_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1959_ = stack[0].m_num;
lean_object* v_knownSize_1960_ = stack[1].m_obj;
lean_object* v_closeError_1961_ = stack[2].m_obj;
lean_object* v_____r_1962_ = stack[3].m_obj;
lean_object* v___y_1963_ = stack[4].m_obj;
lean_object* v_res_1969_;
v_res_1969_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(v___x_1959_, v_knownSize_1960_, v_closeError_1961_, v_____r_1962_, v___y_1963_);
stack->m_obj
 = v_res_1969_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(lean_object* v___x_1970_, lean_object* v_knownSize_1971_, lean_object* v_closeError_1972_, lean_object* v_____r_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
uint8_t v___x_2195__boxed_1976_; lean_object* v_res_1977_; 
v___x_2195__boxed_1976_ = lean_unbox(v___x_1970_);
v_res_1977_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(v___x_2195__boxed_1976_, v_knownSize_1971_, v_closeError_1972_, v_____r_1973_, v___y_1974_);
lean_dec(v___y_1974_);
return v_res_1977_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(lean_object* v___f_1978_, lean_object* v___y_1979_, lean_object* v_x_1980_){
_start:
{
if (lean_obj_tag(v_x_1980_) == 0)
{
lean_object* v___x_1982_; 
lean_dec_ref(v___f_1978_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_x_1980_);
return v___x_1982_;
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1984_; 
v_a_1983_ = lean_ctor_get(v_x_1980_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v_x_1980_, 1);
lean_inc(v___y_1979_);
v___x_1984_ = lean_apply_3(v___f_1978_, v_a_1983_, v___y_1979_, lean_box(0));
return v___x_1984_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1978_ = stack[0].m_obj;
lean_object* v___y_1979_ = stack[1].m_obj;
lean_object* v_x_1980_ = stack[2].m_obj;
lean_object* v_res_1985_;
v_res_1985_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(v___f_1978_, v___y_1979_, v_x_1980_);
stack->m_obj
 = v_res_1985_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed(lean_object* v___f_1986_, lean_object* v___y_1987_, lean_object* v_x_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(v___f_1986_, v___y_1987_, v_x_1988_);
lean_dec(v___y_1987_);
return v_res_1990_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object* v_pendingProducer_1991_, lean_object* v___f_1992_, uint8_t v_closed_1993_, lean_object* v_____r_1994_, lean_object* v___y_1995_){
_start:
{
if (lean_obj_tag(v_pendingProducer_1991_) == 1)
{
lean_object* v_val_1997_; lean_object* v_done_1998_; lean_object* v___f_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_val_1997_ = lean_ctor_get(v_pendingProducer_1991_, 0);
v_done_1998_ = lean_ctor_get(v_val_1997_, 1);
lean_inc(v___y_1995_);
v___f_1999_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1999_, 0, v___f_1992_);
lean_closure_set(v___f_1999_, 1, v___y_1995_);
v___x_2000_ = lean_unsigned_to_nat(0u);
v___x_2001_ = lean_box(v_closed_1993_);
v___x_2002_ = lean_io_promise_resolve(v___x_2001_, v_done_1998_);
v___x_2003_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2004_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2000_, v_closed_1993_, v___x_2003_, v___f_1999_);
return v___x_2004_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = lean_box(0);
lean_inc(v___y_1995_);
v___x_2006_ = lean_apply_3(v___f_1992_, v___x_2005_, v___y_1995_, lean_box(0));
return v___x_2006_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingProducer_1991_ = stack[0].m_obj;
lean_object* v___f_1992_ = stack[1].m_obj;
uint8_t v_closed_1993_ = stack[2].m_num;
lean_object* v_____r_1994_ = stack[3].m_obj;
lean_object* v___y_1995_ = stack[4].m_obj;
lean_object* v_res_2007_;
v_res_2007_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(v_pendingProducer_1991_, v___f_1992_, v_closed_1993_, v_____r_1994_, v___y_1995_);
stack->m_obj
 = v_res_2007_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object* v_pendingProducer_2008_, lean_object* v___f_2009_, lean_object* v_closed_2010_, lean_object* v_____r_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
uint8_t v_closed_boxed_2014_; lean_object* v_res_2015_; 
v_closed_boxed_2014_ = lean_unbox(v_closed_2010_);
v_res_2015_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(v_pendingProducer_2008_, v___f_2009_, v_closed_boxed_2014_, v_____r_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec(v_pendingProducer_2008_);
return v_res_2015_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object* v_interestWaiter_2016_, lean_object* v___f_2017_, uint8_t v_closed_2018_, lean_object* v_____r_2019_, lean_object* v___y_2020_){
_start:
{
if (lean_obj_tag(v_interestWaiter_2016_) == 1)
{
lean_object* v_val_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_val_2022_ = lean_ctor_get(v_interestWaiter_2016_, 0);
lean_inc(v___y_2020_);
v___f_2023_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2023_, 0, v___f_2017_);
lean_closure_set(v___f_2023_, 1, v___y_2020_);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2022_, v_closed_2018_);
v___x_2026_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2027_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2024_, v_closed_2018_, v___x_2026_, v___f_2023_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_box(0);
lean_inc(v___y_2020_);
v___x_2029_ = lean_apply_3(v___f_2017_, v___x_2028_, v___y_2020_, lean_box(0));
return v___x_2029_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_interestWaiter_2016_ = stack[0].m_obj;
lean_object* v___f_2017_ = stack[1].m_obj;
uint8_t v_closed_2018_ = stack[2].m_num;
lean_object* v_____r_2019_ = stack[3].m_obj;
lean_object* v___y_2020_ = stack[4].m_obj;
lean_object* v_res_2030_;
v_res_2030_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_2016_, v___f_2017_, v_closed_2018_, v_____r_2019_, v___y_2020_);
stack->m_obj
 = v_res_2030_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(lean_object* v_interestWaiter_2031_, lean_object* v___f_2032_, lean_object* v_closed_2033_, lean_object* v_____r_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
uint8_t v_closed_boxed_2037_; lean_object* v_res_2038_; 
v_closed_boxed_2037_ = lean_unbox(v_closed_2033_);
v_res_2038_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_2031_, v___f_2032_, v_closed_boxed_2037_, v_____r_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec(v_interestWaiter_2031_);
return v_res_2038_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(lean_object* v___f_2039_, lean_object* v_a_2040_, lean_object* v_x_2041_){
_start:
{
if (lean_obj_tag(v_x_2041_) == 0)
{
lean_object* v___x_2043_; 
lean_dec_ref(v___f_2039_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_x_2041_);
return v___x_2043_;
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v_x_2041_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v_x_2041_, 1);
lean_inc(v_a_2040_);
v___x_2045_ = lean_apply_3(v___f_2039_, v_a_2044_, v_a_2040_, lean_box(0));
return v___x_2045_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2039_ = stack[0].m_obj;
lean_object* v_a_2040_ = stack[1].m_obj;
lean_object* v_x_2041_ = stack[2].m_obj;
lean_object* v_res_2046_;
v_res_2046_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(v___f_2039_, v_a_2040_, v_x_2041_);
stack->m_obj
 = v_res_2046_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed(lean_object* v___f_2047_, lean_object* v_a_2048_, lean_object* v_x_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(v___f_2047_, v_a_2048_, v_x_2049_);
lean_dec(v_a_2048_);
return v_res_2051_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(lean_object* v_a_2052_, lean_object* v_x_2053_){
_start:
{
if (lean_obj_tag(v_x_2053_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2063_; 
v_a_2055_ = lean_ctor_get(v_x_2053_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_x_2053_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2057_ = v_x_2053_;
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v_x_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
return v___x_2061_;
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2097_; 
v_a_2064_ = lean_ctor_get(v_x_2053_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_x_2053_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2066_ = v_x_2053_;
v_isShared_2067_ = v_isSharedCheck_2097_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v_x_2053_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2097_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
uint8_t v_closed_2068_; 
v_closed_2068_ = lean_ctor_get_uint8(v_a_2064_, sizeof(void*)*6);
if (v_closed_2068_ == 0)
{
lean_object* v_pendingProducer_2069_; lean_object* v_pendingConsumer_2070_; lean_object* v_interestWaiter_2071_; lean_object* v_knownSize_2072_; lean_object* v_closeError_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___f_2076_; lean_object* v___x_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; lean_object* v___f_2080_; 
v_pendingProducer_2069_ = lean_ctor_get(v_a_2064_, 0);
lean_inc(v_pendingProducer_2069_);
v_pendingConsumer_2070_ = lean_ctor_get(v_a_2064_, 1);
lean_inc(v_pendingConsumer_2070_);
v_interestWaiter_2071_ = lean_ctor_get(v_a_2064_, 2);
lean_inc_n(v_interestWaiter_2071_, 2);
v_knownSize_2072_ = lean_ctor_get(v_a_2064_, 3);
lean_inc(v_knownSize_2072_);
v_closeError_2073_ = lean_ctor_get(v_a_2064_, 5);
lean_inc_n(v_closeError_2073_, 2);
lean_dec(v_a_2064_);
v___x_2074_ = 1;
v___x_2075_ = lean_box(v___x_2074_);
v___f_2076_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2076_, 0, v___x_2075_);
lean_closure_set(v___f_2076_, 1, v_knownSize_2072_);
lean_closure_set(v___f_2076_, 2, v_closeError_2073_);
v___x_2077_ = lean_box(v_closed_2068_);
v___f_2078_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2078_, 0, v_pendingProducer_2069_);
lean_closure_set(v___f_2078_, 1, v___f_2076_);
lean_closure_set(v___f_2078_, 2, v___x_2077_);
v___x_2079_ = lean_box(v_closed_2068_);
lean_inc_ref(v___f_2078_);
v___f_2080_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2080_, 0, v_interestWaiter_2071_);
lean_closure_set(v___f_2080_, 1, v___f_2078_);
lean_closure_set(v___f_2080_, 2, v___x_2079_);
if (lean_obj_tag(v_pendingConsumer_2070_) == 1)
{
lean_object* v_val_2081_; lean_object* v___f_2082_; lean_object* v___y_2084_; 
lean_dec_ref(v___f_2078_);
lean_dec(v_interestWaiter_2071_);
v_val_2081_ = lean_ctor_get(v_pendingConsumer_2070_, 0);
lean_inc(v_val_2081_);
lean_dec_ref_known(v_pendingConsumer_2070_, 1);
lean_inc(v_a_2052_);
v___f_2082_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2082_, 0, v___f_2080_);
lean_closure_set(v___f_2082_, 1, v_a_2052_);
if (lean_obj_tag(v_closeError_2073_) == 0)
{
lean_object* v___x_2089_; 
lean_del_object(v___x_2066_);
v___x_2089_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___y_2084_ = v___x_2089_;
goto v___jp_2083_;
}
else
{
lean_object* v_val_2090_; lean_object* v___x_2092_; 
v_val_2090_ = lean_ctor_get(v_closeError_2073_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v_closeError_2073_, 1);
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 0);
lean_ctor_set(v___x_2066_, 0, v_val_2090_);
v___x_2092_ = v___x_2066_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_val_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
v___y_2084_ = v___x_2092_;
goto v___jp_2083_;
}
}
v___jp_2083_:
{
lean_object* v___x_2085_; uint8_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_2081_, v___y_2084_);
lean_dec(v_val_2081_);
v___x_2087_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2088_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2085_, v_closed_2068_, v___x_2087_, v___f_2082_);
return v___x_2088_;
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec_ref(v___f_2080_);
lean_dec(v_closeError_2073_);
lean_dec(v_pendingConsumer_2070_);
lean_del_object(v___x_2066_);
v___x_2094_ = lean_box(0);
v___x_2095_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_2071_, v___f_2078_, v_closed_2068_, v___x_2094_, v_a_2052_);
lean_dec(v_interestWaiter_2071_);
return v___x_2095_;
}
}
else
{
lean_object* v___x_2096_; 
lean_del_object(v___x_2066_);
lean_dec(v_a_2064_);
v___x_2096_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2096_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2052_ = stack[0].m_obj;
lean_object* v_x_2053_ = stack[1].m_obj;
lean_object* v_res_2098_;
v_res_2098_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(v_a_2052_, v_x_2053_);
stack->m_obj
 = v_res_2098_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed(lean_object* v_a_2099_, lean_object* v_x_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(v_a_2099_, v_x_2100_);
lean_dec(v_a_2099_);
return v_res_2102_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(lean_object* v_a_2103_){
_start:
{
lean_object* v___f_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_inc(v_a_2103_);
v___f_2105_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed), 3, 1);
lean_closure_set(v___f_2105_, 0, v_a_2103_);
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = 0;
v___x_2108_ = lean_st_ref_get(v_a_2103_);
v___x_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
v___x_2111_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2106_, v___x_2107_, v___x_2110_, v___f_2105_);
return v___x_2111_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2103_ = stack[0].m_obj;
lean_object* v_res_2112_;
v_res_2112_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v_a_2103_);
stack->m_obj
 = v_res_2112_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed(lean_object* v_a_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v_a_2113_);
lean_dec(v_a_2113_);
return v_res_2115_;
}
}
lean_object* l_Std_Http_Body_Stream_close(lean_object* v_stream_2117_){
_start:
{
lean_object* v___f_2119_; lean_object* v___x_2120_; 
v___f_2119_ = ((lean_object*)(l_Std_Http_Body_Stream_close___closed__0));
v___x_2120_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2117_, v___f_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2117_ = stack[0].m_obj;
lean_object* v_res_2121_;
v_res_2121_ = l_Std_Http_Body_Stream_close(v_stream_2117_);
stack->m_obj
 = v_res_2121_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object* v_stream_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Std_Http_Body_Stream_close(v_stream_2122_);
return v_res_2124_;
}
}
lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(uint8_t v___x_2125_, lean_object* v_x_2126_){
_start:
{
if (lean_obj_tag(v_x_2126_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2136_; 
v_a_2128_ = lean_ctor_get(v_x_2126_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_x_2126_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2130_ = v_x_2126_;
v_isShared_2131_ = v_isSharedCheck_2136_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v_x_2126_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2136_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
}
}
else
{
lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2145_; 
v_isSharedCheck_2145_ = !lean_is_exclusive(v_x_2126_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_x_2126_, 0);
lean_dec(v_unused_2146_);
v___x_2138_ = v_x_2126_;
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
else
{
lean_dec(v_x_2126_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_box(v___x_2125_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
return v___x_2143_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_closeIfAbandoned___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2125_ = stack[0].m_num;
lean_object* v_x_2126_ = stack[1].m_obj;
lean_object* v_res_2147_;
v_res_2147_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(v___x_2125_, v_x_2126_);
stack->m_obj
 = v_res_2147_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0___boxed(lean_object* v___x_2148_, lean_object* v_x_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v___x_1415__boxed_2151_; lean_object* v_res_2152_; 
v___x_1415__boxed_2151_ = lean_unbox(v___x_2148_);
v_res_2152_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(v___x_1415__boxed_2151_, v_x_2149_);
return v_res_2152_;
}
}
lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(lean_object* v___y_2156_, lean_object* v_x_2157_){
_start:
{
uint8_t v___y_2160_; 
if (lean_obj_tag(v_x_2157_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2172_; 
v_a_2164_ = lean_ctor_get(v_x_2157_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2157_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2166_ = v_x_2157_;
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v_x_2157_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; 
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
return v___x_2170_;
}
}
}
else
{
lean_object* v_a_2173_; uint8_t v_closed_2174_; 
v_a_2173_ = lean_ctor_get(v_x_2157_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v_x_2157_, 1);
v_closed_2174_ = lean_ctor_get_uint8(v_a_2173_, sizeof(void*)*6);
if (v_closed_2174_ == 0)
{
lean_object* v_pendingConsumer_2175_; 
v_pendingConsumer_2175_ = lean_ctor_get(v_a_2173_, 1);
lean_inc(v_pendingConsumer_2175_);
lean_dec(v_a_2173_);
if (lean_obj_tag(v_pendingConsumer_2175_) == 0)
{
lean_object* v___f_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___f_2176_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0));
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v___y_2156_);
v___x_2179_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2177_, v_closed_2174_, v___x_2178_, v___f_2176_);
return v___x_2179_;
}
else
{
lean_dec_ref_known(v_pendingConsumer_2175_, 1);
v___y_2160_ = v_closed_2174_;
goto v___jp_2159_;
}
}
else
{
uint8_t v___x_2180_; 
lean_dec(v_a_2173_);
v___x_2180_ = 0;
v___y_2160_ = v___x_2180_;
goto v___jp_2159_;
}
}
v___jp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_box(v___y_2160_);
v___x_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_closeIfAbandoned___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2156_ = stack[0].m_obj;
lean_object* v_x_2157_ = stack[1].m_obj;
lean_object* v_res_2181_;
v_res_2181_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(v___y_2156_, v_x_2157_);
stack->m_obj
 = v_res_2181_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed(lean_object* v___y_2182_, lean_object* v_x_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(v___y_2182_, v_x_2183_);
lean_dec(v___y_2182_);
return v_res_2185_;
}
}
lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(lean_object* v___y_2186_, lean_object* v___f_2187_, lean_object* v_x_2188_){
_start:
{
if (lean_obj_tag(v_x_2188_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v___f_2187_);
v_a_2190_ = lean_ctor_get(v_x_2188_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_x_2188_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2192_ = v_x_2188_;
v_isShared_2193_ = v_isSharedCheck_2198_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v_x_2188_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2198_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
return v___x_2196_;
}
}
}
else
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2210_; 
v_isSharedCheck_2210_ = !lean_is_exclusive(v_x_2188_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v_x_2188_, 0);
lean_dec(v_unused_2211_);
v___x_2200_ = v_x_2188_;
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v_x_2188_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = 0;
v___x_2204_ = lean_st_ref_get(v___y_2186_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2204_);
v___x_2206_ = v___x_2200_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
v___x_2208_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2202_, v___x_2203_, v___x_2207_, v___f_2187_);
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_closeIfAbandoned___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2186_ = stack[0].m_obj;
lean_object* v___f_2187_ = stack[1].m_obj;
lean_object* v_x_2188_ = stack[2].m_obj;
lean_object* v_res_2212_;
v_res_2212_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(v___y_2186_, v___f_2187_, v_x_2188_);
stack->m_obj
 = v_res_2212_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed(lean_object* v___y_2213_, lean_object* v___f_2214_, lean_object* v_x_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(v___y_2213_, v___f_2214_, v_x_2215_);
lean_dec(v___y_2213_);
return v_res_2217_;
}
}
lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(lean_object* v___y_2218_){
_start:
{
lean_object* v___f_2220_; lean_object* v___f_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_inc_n(v___y_2218_, 2);
v___f_2220_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2220_, 0, v___y_2218_);
v___f_2221_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2221_, 0, v___y_2218_);
lean_closure_set(v___f_2221_, 1, v___f_2220_);
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = 0;
v___x_2224_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2218_);
v___x_2225_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2222_, v___x_2223_, v___x_2224_, v___f_2221_);
return v___x_2225_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_closeIfAbandoned___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2218_ = stack[0].m_obj;
lean_object* v_res_2226_;
v_res_2226_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(v___y_2218_);
stack->m_obj
 = v_res_2226_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3___boxed(lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(v___y_2227_);
lean_dec(v___y_2227_);
return v_res_2229_;
}
}
lean_object* l_Std_Http_Body_Stream_closeIfAbandoned(lean_object* v_stream_2231_){
_start:
{
lean_object* v___f_2233_; lean_object* v___x_2234_; 
v___f_2233_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___closed__0));
v___x_2234_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2231_, v___f_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_closeIfAbandoned_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2231_ = stack[0].m_obj;
lean_object* v_res_2235_;
v_res_2235_ = l_Std_Http_Body_Stream_closeIfAbandoned(v_stream_2231_);
stack->m_obj
 = v_res_2235_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___boxed(lean_object* v_stream_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Std_Http_Body_Stream_closeIfAbandoned(v_stream_2236_);
return v_res_2238_;
}
}
lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0(lean_object* v___y_2239_, lean_object* v_x_2240_){
_start:
{
if (lean_obj_tag(v_x_2240_) == 0)
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_x_2240_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; 
lean_dec_ref_known(v_x_2240_, 1);
v___x_2243_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v___y_2239_);
return v___x_2243_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_closeWithError___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2239_ = stack[0].m_obj;
lean_object* v_x_2240_ = stack[1].m_obj;
lean_object* v_res_2244_;
v_res_2244_ = l_Std_Http_Body_Stream_closeWithError___lam__0(v___y_2239_, v_x_2240_);
stack->m_obj
 = v_res_2244_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0___boxed(lean_object* v___y_2245_, lean_object* v_x_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Std_Http_Body_Stream_closeWithError___lam__0(v___y_2245_, v_x_2246_);
lean_dec(v___y_2245_);
return v_res_2248_;
}
}
lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1(lean_object* v_err_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___f_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v_fst_2257_; lean_object* v_snd_2258_; lean_object* v_pendingProducer_2263_; lean_object* v_pendingConsumer_2264_; lean_object* v_interestWaiter_2265_; uint8_t v_closed_2266_; lean_object* v_knownSize_2267_; lean_object* v_pendingIncompleteChunk_2268_; lean_object* v_closeError_2269_; lean_object* v___x_2270_; 
lean_inc(v___y_2250_);
v___f_2252_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2252_, 0, v___y_2250_);
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = 0;
v___x_2255_ = lean_st_ref_take(v___y_2250_);
v_pendingProducer_2263_ = lean_ctor_get(v___x_2255_, 0);
v_pendingConsumer_2264_ = lean_ctor_get(v___x_2255_, 1);
v_interestWaiter_2265_ = lean_ctor_get(v___x_2255_, 2);
v_closed_2266_ = lean_ctor_get_uint8(v___x_2255_, sizeof(void*)*6);
v_knownSize_2267_ = lean_ctor_get(v___x_2255_, 3);
v_pendingIncompleteChunk_2268_ = lean_ctor_get(v___x_2255_, 4);
v_closeError_2269_ = lean_ctor_get(v___x_2255_, 5);
v___x_2270_ = lean_box(0);
if (lean_obj_tag(v_closeError_2269_) == 0)
{
lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2278_; 
lean_inc(v_pendingIncompleteChunk_2268_);
lean_inc(v_knownSize_2267_);
lean_inc(v_interestWaiter_2265_);
lean_inc(v_pendingConsumer_2264_);
lean_inc(v_pendingProducer_2263_);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2278_ == 0)
{
lean_object* v_unused_2279_; lean_object* v_unused_2280_; lean_object* v_unused_2281_; lean_object* v_unused_2282_; lean_object* v_unused_2283_; lean_object* v_unused_2284_; 
v_unused_2279_ = lean_ctor_get(v___x_2255_, 5);
lean_dec(v_unused_2279_);
v_unused_2280_ = lean_ctor_get(v___x_2255_, 4);
lean_dec(v_unused_2280_);
v_unused_2281_ = lean_ctor_get(v___x_2255_, 3);
lean_dec(v_unused_2281_);
v_unused_2282_ = lean_ctor_get(v___x_2255_, 2);
lean_dec(v_unused_2282_);
v_unused_2283_ = lean_ctor_get(v___x_2255_, 1);
lean_dec(v_unused_2283_);
v_unused_2284_ = lean_ctor_get(v___x_2255_, 0);
lean_dec(v_unused_2284_);
v___x_2272_ = v___x_2255_;
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
else
{
lean_dec(v___x_2255_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_err_2249_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 5, v___x_2274_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_pendingProducer_2263_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_pendingConsumer_2264_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_interestWaiter_2265_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v_knownSize_2267_);
lean_ctor_set(v_reuseFailAlloc_2277_, 4, v_pendingIncompleteChunk_2268_);
lean_ctor_set(v_reuseFailAlloc_2277_, 5, v___x_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2277_, sizeof(void*)*6, v_closed_2266_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
v_fst_2257_ = v___x_2270_;
v_snd_2258_ = v___x_2276_;
goto v___jp_2256_;
}
}
}
else
{
lean_dec(v_err_2249_);
v_fst_2257_ = v___x_2270_;
v_snd_2258_ = v___x_2255_;
goto v___jp_2256_;
}
v___jp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2259_ = lean_st_ref_put(v___y_2250_, v_snd_2258_);
v___x_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2260_, 0, v_fst_2257_);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2253_, v___x_2254_, v___x_2261_, v___f_2252_);
return v___x_2262_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_closeWithError___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_err_2249_ = stack[0].m_obj;
lean_object* v___y_2250_ = stack[1].m_obj;
lean_object* v_res_2285_;
v_res_2285_ = l_Std_Http_Body_Stream_closeWithError___lam__1(v_err_2249_, v___y_2250_);
stack->m_obj
 = v_res_2285_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1___boxed(lean_object* v_err_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Std_Http_Body_Stream_closeWithError___lam__1(v_err_2286_, v___y_2287_);
lean_dec(v___y_2287_);
return v_res_2289_;
}
}
lean_object* l_Std_Http_Body_Stream_closeWithError(lean_object* v_stream_2290_, lean_object* v_err_2291_){
_start:
{
lean_object* v___f_2293_; lean_object* v___x_2294_; 
v___f_2293_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2293_, 0, v_err_2291_);
v___x_2294_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2290_, v___f_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_closeWithError_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2290_ = stack[0].m_obj;
lean_object* v_err_2291_ = stack[1].m_obj;
lean_object* v_res_2295_;
v_res_2295_ = l_Std_Http_Body_Stream_closeWithError(v_stream_2290_, v_err_2291_);
stack->m_obj
 = v_res_2295_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___boxed(lean_object* v_stream_2296_, lean_object* v_err_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Std_Http_Body_Stream_closeWithError(v_stream_2296_, v_err_2297_);
return v_res_2299_;
}
}
lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object* v_____do__lift_2300_, lean_object* v___y_2301_){
_start:
{
uint8_t v_closed_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_closed_2303_ = lean_ctor_get_uint8(v_____do__lift_2300_, sizeof(void*)*6);
v___x_2304_ = lean_box(v_closed_2303_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_isClosed___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_2300_ = stack[0].m_obj;
lean_object* v___y_2301_ = stack[1].m_obj;
lean_object* v_res_2307_;
v_res_2307_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_2300_, v___y_2301_);
stack->m_obj
 = v_res_2307_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object* v_____do__lift_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v_____do__lift_2308_);
return v_res_2311_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__1(void){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_2313_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__2(void){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_2314_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__6(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___f_2321_; lean_object* v___f_2322_; 
v___x_2320_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2321_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___f_2322_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2322_, 0, v___f_2321_);
lean_closure_set(v___f_2322_, 1, v___x_2320_);
return v___f_2322_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__11(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___f_2332_; lean_object* v___f_2333_; 
v___x_2331_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2332_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__10));
v___f_2333_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2333_, 0, v___f_2332_);
lean_closure_set(v___f_2333_, 1, v___x_2331_);
return v___f_2333_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__12(void){
_start:
{
lean_object* v___f_2334_; lean_object* v___x_2335_; 
v___f_2334_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__11, &l_Std_Http_Body_Stream_isClosed___closed__11_once, _init_l_Std_Http_Body_Stream_isClosed___closed__11);
v___x_2335_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2335_, 0, lean_box(0));
lean_closure_set(v___x_2335_, 1, lean_box(0));
lean_closure_set(v___x_2335_, 2, lean_box(0));
lean_closure_set(v___x_2335_, 3, v___f_2334_);
return v___x_2335_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__13(void){
_start:
{
lean_object* v___f_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___f_2336_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__0));
v___x_2337_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2338_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2339_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2339_, 0, lean_box(0));
lean_closure_set(v___x_2339_, 1, lean_box(0));
lean_closure_set(v___x_2339_, 2, v___x_2338_);
lean_closure_set(v___x_2339_, 3, lean_box(0));
lean_closure_set(v___x_2339_, 4, lean_box(0));
lean_closure_set(v___x_2339_, 5, v___x_2337_);
lean_closure_set(v___x_2339_, 6, v___f_2336_);
return v___x_2339_;
}
}
lean_object* l_Std_Http_Body_Stream_isClosed(lean_object* v_stream_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v___f_2343_; lean_object* v___f_2344_; lean_object* v___x_2345_; lean_object* v___x_214__overap_2346_; lean_object* v___x_2347_; 
v___x_2342_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2343_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2344_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2345_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__13, &l_Std_Http_Body_Stream_isClosed___closed__13_once, _init_l_Std_Http_Body_Stream_isClosed___closed__13);
v___x_214__overap_2346_ = l_Std_Mutex_atomically___redArg(v___x_2342_, v___f_2343_, v___f_2344_, v_stream_2340_, v___x_2345_);
v___x_2347_ = lean_apply_1(v___x_214__overap_2346_, lean_box(0));
return v___x_2347_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_isClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2340_ = stack[0].m_obj;
lean_object* v_res_2348_;
v_res_2348_ = l_Std_Http_Body_Stream_isClosed(v_stream_2340_);
stack->m_obj
 = v_res_2348_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___boxed(lean_object* v_stream_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Std_Http_Body_Stream_isClosed(v_stream_2349_);
return v_res_2351_;
}
}
lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0(lean_object* v_____do__lift_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_knownSize_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_knownSize_2355_ = lean_ctor_get(v_____do__lift_2352_, 3);
lean_inc(v_knownSize_2355_);
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_knownSize_2355_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_getKnownSize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_2352_ = stack[0].m_obj;
lean_object* v___y_2353_ = stack[1].m_obj;
lean_object* v_res_2358_;
v_res_2358_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_2352_, v___y_2353_);
stack->m_obj
 = v_res_2358_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(lean_object* v_____do__lift_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v_____do__lift_2359_);
return v_res_2362_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_getKnownSize___closed__1(void){
_start:
{
lean_object* v___f_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___f_2364_ = ((lean_object*)(l_Std_Http_Body_Stream_getKnownSize___closed__0));
v___x_2365_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2366_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2367_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2367_, 0, lean_box(0));
lean_closure_set(v___x_2367_, 1, lean_box(0));
lean_closure_set(v___x_2367_, 2, v___x_2366_);
lean_closure_set(v___x_2367_, 3, lean_box(0));
lean_closure_set(v___x_2367_, 4, lean_box(0));
lean_closure_set(v___x_2367_, 5, v___x_2365_);
lean_closure_set(v___x_2367_, 6, v___f_2364_);
return v___x_2367_;
}
}
lean_object* l_Std_Http_Body_Stream_getKnownSize(lean_object* v_stream_2368_){
_start:
{
lean_object* v___x_2370_; lean_object* v___f_2371_; lean_object* v___f_2372_; lean_object* v___x_2373_; lean_object* v___x_214__overap_2374_; lean_object* v___x_2375_; 
v___x_2370_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2371_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2372_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2373_ = lean_obj_once(&l_Std_Http_Body_Stream_getKnownSize___closed__1, &l_Std_Http_Body_Stream_getKnownSize___closed__1_once, _init_l_Std_Http_Body_Stream_getKnownSize___closed__1);
v___x_214__overap_2374_ = l_Std_Mutex_atomically___redArg(v___x_2370_, v___f_2371_, v___f_2372_, v_stream_2368_, v___x_2373_);
v___x_2375_ = lean_apply_1(v___x_214__overap_2374_, lean_box(0));
return v___x_2375_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_getKnownSize_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2368_ = stack[0].m_obj;
lean_object* v_res_2376_;
v_res_2376_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_2368_);
stack->m_obj
 = v_res_2376_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___boxed(lean_object* v_stream_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_2377_);
return v_res_2379_;
}
}
lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0(lean_object* v_size_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2383_; lean_object* v_pendingProducer_2384_; lean_object* v_pendingConsumer_2385_; lean_object* v_interestWaiter_2386_; uint8_t v_closed_2387_; lean_object* v_pendingIncompleteChunk_2388_; lean_object* v_closeError_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2398_; 
v___x_2383_ = lean_st_ref_take(v___y_2381_);
v_pendingProducer_2384_ = lean_ctor_get(v___x_2383_, 0);
v_pendingConsumer_2385_ = lean_ctor_get(v___x_2383_, 1);
v_interestWaiter_2386_ = lean_ctor_get(v___x_2383_, 2);
v_closed_2387_ = lean_ctor_get_uint8(v___x_2383_, sizeof(void*)*6);
v_pendingIncompleteChunk_2388_ = lean_ctor_get(v___x_2383_, 4);
v_closeError_2389_ = lean_ctor_get(v___x_2383_, 5);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v___x_2383_, 3);
lean_dec(v_unused_2399_);
v___x_2391_ = v___x_2383_;
v_isShared_2392_ = v_isSharedCheck_2398_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_closeError_2389_);
lean_inc(v_pendingIncompleteChunk_2388_);
lean_inc(v_interestWaiter_2386_);
lean_inc(v_pendingConsumer_2385_);
lean_inc(v_pendingProducer_2384_);
lean_dec(v___x_2383_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2398_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 3, v_size_2380_);
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_pendingProducer_2384_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_pendingConsumer_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_interestWaiter_2386_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_size_2380_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_pendingIncompleteChunk_2388_);
lean_ctor_set(v_reuseFailAlloc_2397_, 5, v_closeError_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*6, v_closed_2387_);
v___x_2394_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_st_ref_put(v___y_2381_, v___x_2394_);
v___x_2396_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2396_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_setKnownSize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_size_2380_ = stack[0].m_obj;
lean_object* v___y_2381_ = stack[1].m_obj;
lean_object* v_res_2400_;
v_res_2400_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_2380_, v___y_2381_);
stack->m_obj
 = v_res_2400_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(lean_object* v_size_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_2401_, v___y_2402_);
lean_dec(v___y_2402_);
return v_res_2404_;
}
}
lean_object* l_Std_Http_Body_Stream_setKnownSize(lean_object* v_stream_2405_, lean_object* v_size_2406_){
_start:
{
lean_object* v___f_2408_; lean_object* v___x_2409_; lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___x_207__overap_2412_; lean_object* v___x_2413_; 
v___f_2408_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2408_, 0, v_size_2406_);
v___x_2409_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2410_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2411_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_207__overap_2412_ = l_Std_Mutex_atomically___redArg(v___x_2409_, v___f_2410_, v___f_2411_, v_stream_2405_, v___f_2408_);
v___x_2413_ = lean_apply_1(v___x_207__overap_2412_, lean_box(0));
return v___x_2413_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_setKnownSize_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2405_ = stack[0].m_obj;
lean_object* v_size_2406_ = stack[1].m_obj;
lean_object* v_res_2414_;
v_res_2414_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_2405_, v_size_2406_);
stack->m_obj
 = v_res_2414_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___boxed(lean_object* v_stream_2415_, lean_object* v_size_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_2415_, v_size_2416_);
return v_res_2418_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object* v_pendingProducer_2419_, lean_object* v_pendingConsumer_2420_, uint8_t v_closed_2421_, lean_object* v_knownSize_2422_, lean_object* v_pendingIncompleteChunk_2423_, lean_object* v_closeError_2424_, lean_object* v_a_2425_, lean_object* v___x_2426_, lean_object* v_x_2427_){
_start:
{
if (lean_obj_tag(v_x_2427_) == 0)
{
lean_object* v___x_2429_; 
lean_dec(v_closeError_2424_);
lean_dec(v_pendingIncompleteChunk_2423_);
lean_dec(v_knownSize_2422_);
lean_dec(v_pendingConsumer_2420_);
lean_dec(v_pendingProducer_2419_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_x_2427_);
return v___x_2429_;
}
else
{
lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2440_; 
v_isSharedCheck_2440_ = !lean_is_exclusive(v_x_2427_);
if (v_isSharedCheck_2440_ == 0)
{
lean_object* v_unused_2441_; 
v_unused_2441_ = lean_ctor_get(v_x_2427_, 0);
lean_dec(v_unused_2441_);
v___x_2431_ = v_x_2427_;
v_isShared_2432_ = v_isSharedCheck_2440_;
goto v_resetjp_2430_;
}
else
{
lean_dec(v_x_2427_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2440_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2433_ = lean_box(0);
v___x_2434_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2434_, 0, v_pendingProducer_2419_);
lean_ctor_set(v___x_2434_, 1, v_pendingConsumer_2420_);
lean_ctor_set(v___x_2434_, 2, v___x_2433_);
lean_ctor_set(v___x_2434_, 3, v_knownSize_2422_);
lean_ctor_set(v___x_2434_, 4, v_pendingIncompleteChunk_2423_);
lean_ctor_set(v___x_2434_, 5, v_closeError_2424_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*6, v_closed_2421_);
v___x_2435_ = lean_st_ref_swap(v_a_2425_, v___x_2434_);
lean_dec(v___x_2435_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v___x_2426_);
v___x_2437_ = v___x_2431_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2426_);
v___x_2437_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
return v___x_2438_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingProducer_2419_ = stack[0].m_obj;
lean_object* v_pendingConsumer_2420_ = stack[1].m_obj;
uint8_t v_closed_2421_ = stack[2].m_num;
lean_object* v_knownSize_2422_ = stack[3].m_obj;
lean_object* v_pendingIncompleteChunk_2423_ = stack[4].m_obj;
lean_object* v_closeError_2424_ = stack[5].m_obj;
lean_object* v_a_2425_ = stack[6].m_obj;
lean_object* v___x_2426_ = stack[7].m_obj;
lean_object* v_x_2427_ = stack[8].m_obj;
lean_object* v_res_2442_;
v_res_2442_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_2419_, v_pendingConsumer_2420_, v_closed_2421_, v_knownSize_2422_, v_pendingIncompleteChunk_2423_, v_closeError_2424_, v_a_2425_, v___x_2426_, v_x_2427_);
stack->m_obj
 = v_res_2442_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object* v_pendingProducer_2443_, lean_object* v_pendingConsumer_2444_, lean_object* v_closed_2445_, lean_object* v_knownSize_2446_, lean_object* v_pendingIncompleteChunk_2447_, lean_object* v_closeError_2448_, lean_object* v_a_2449_, lean_object* v___x_2450_, lean_object* v_x_2451_, lean_object* v___y_2452_){
_start:
{
uint8_t v_closed_boxed_2453_; lean_object* v_res_2454_; 
v_closed_boxed_2453_ = lean_unbox(v_closed_2445_);
v_res_2454_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_2443_, v_pendingConsumer_2444_, v_closed_boxed_2453_, v_knownSize_2446_, v_pendingIncompleteChunk_2447_, v_closeError_2448_, v_a_2449_, v___x_2450_, v_x_2451_);
lean_dec(v_a_2449_);
return v_res_2454_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object* v_a_2455_, lean_object* v_x_2456_){
_start:
{
if (lean_obj_tag(v_x_2456_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2466_; 
v_a_2458_ = lean_ctor_get(v_x_2456_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_x_2456_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2460_ = v_x_2456_;
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v_x_2456_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v_interestWaiter_2468_; 
v_a_2467_ = lean_ctor_get(v_x_2456_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v_x_2456_, 1);
v_interestWaiter_2468_ = lean_ctor_get(v_a_2467_, 2);
lean_inc(v_interestWaiter_2468_);
if (lean_obj_tag(v_interestWaiter_2468_) == 1)
{
lean_object* v_pendingProducer_2469_; lean_object* v_pendingConsumer_2470_; uint8_t v_closed_2471_; lean_object* v_knownSize_2472_; lean_object* v_pendingIncompleteChunk_2473_; lean_object* v_closeError_2474_; lean_object* v_val_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___f_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_pendingProducer_2469_ = lean_ctor_get(v_a_2467_, 0);
lean_inc(v_pendingProducer_2469_);
v_pendingConsumer_2470_ = lean_ctor_get(v_a_2467_, 1);
lean_inc(v_pendingConsumer_2470_);
v_closed_2471_ = lean_ctor_get_uint8(v_a_2467_, sizeof(void*)*6);
v_knownSize_2472_ = lean_ctor_get(v_a_2467_, 3);
lean_inc(v_knownSize_2472_);
v_pendingIncompleteChunk_2473_ = lean_ctor_get(v_a_2467_, 4);
lean_inc(v_pendingIncompleteChunk_2473_);
v_closeError_2474_ = lean_ctor_get(v_a_2467_, 5);
lean_inc(v_closeError_2474_);
lean_dec(v_a_2467_);
v_val_2475_ = lean_ctor_get(v_interestWaiter_2468_, 0);
lean_inc(v_val_2475_);
lean_dec_ref_known(v_interestWaiter_2468_, 1);
v___x_2476_ = 1;
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_box(v_closed_2471_);
lean_inc(v_a_2455_);
v___f_2479_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed), 10, 8);
lean_closure_set(v___f_2479_, 0, v_pendingProducer_2469_);
lean_closure_set(v___f_2479_, 1, v_pendingConsumer_2470_);
lean_closure_set(v___f_2479_, 2, v___x_2478_);
lean_closure_set(v___f_2479_, 3, v_knownSize_2472_);
lean_closure_set(v___f_2479_, 4, v_pendingIncompleteChunk_2473_);
lean_closure_set(v___f_2479_, 5, v_closeError_2474_);
lean_closure_set(v___f_2479_, 6, v_a_2455_);
lean_closure_set(v___f_2479_, 7, v___x_2477_);
v___x_2480_ = lean_unsigned_to_nat(0u);
v___x_2481_ = 0;
v___x_2482_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2475_, v___x_2476_);
lean_dec(v_val_2475_);
v___x_2483_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2484_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2480_, v___x_2481_, v___x_2483_, v___f_2479_);
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; 
lean_dec(v_interestWaiter_2468_);
lean_dec(v_a_2467_);
v___x_2485_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2485_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2455_ = stack[0].m_obj;
lean_object* v_x_2456_ = stack[1].m_obj;
lean_object* v_res_2486_;
v_res_2486_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_2455_, v_x_2456_);
stack->m_obj
 = v_res_2486_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object* v_a_2487_, lean_object* v_x_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_2487_, v_x_2488_);
lean_dec(v_a_2487_);
return v_res_2490_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object* v_a_2491_){
_start:
{
lean_object* v___f_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_inc(v_a_2491_);
v___f_2493_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2493_, 0, v_a_2491_);
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = 0;
v___x_2496_ = lean_st_ref_get(v_a_2491_);
v___x_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
v___x_2499_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2494_, v___x_2495_, v___x_2498_, v___f_2493_);
return v___x_2499_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2491_ = stack[0].m_obj;
lean_object* v_res_2500_;
v_res_2500_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_2491_);
stack->m_obj
 = v_res_2500_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object* v_a_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_2501_);
lean_dec(v_a_2501_);
return v_res_2503_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object* v_promise_2504_, lean_object* v_x_2505_){
_start:
{
if (lean_obj_tag(v_x_2505_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2515_; 
v_a_2507_ = lean_ctor_get(v_x_2505_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_x_2505_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2509_ = v_x_2505_;
v_isShared_2510_ = v_isSharedCheck_2515_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v_x_2505_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2515_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
return v___x_2513_;
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2525_; 
v_a_2516_ = lean_ctor_get(v_x_2505_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_x_2505_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2518_ = v_x_2505_;
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v_x_2505_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2520_ = lean_io_promise_resolve(v_a_2516_, v_promise_2504_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2520_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; 
v___x_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
return v___x_2523_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_2504_ = stack[0].m_obj;
lean_object* v_x_2505_ = stack[1].m_obj;
lean_object* v_res_2526_;
v_res_2526_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(v_promise_2504_, v_x_2505_);
stack->m_obj
 = v_res_2526_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(v_promise_2527_, v_x_2528_);
lean_dec(v_promise_2527_);
return v_res_2530_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object* v_lose_2531_, lean_object* v___y_2532_, lean_object* v___f_2533_, lean_object* v_x_2534_){
_start:
{
if (lean_obj_tag(v_x_2534_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v___f_2533_);
lean_dec_ref(v_lose_2531_);
v_a_2536_ = lean_ctor_get(v_x_2534_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_x_2534_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2538_ = v_x_2534_;
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v_x_2534_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
return v___x_2542_;
}
}
}
else
{
lean_object* v_a_2545_; uint8_t v___x_2546_; 
v_a_2545_ = lean_ctor_get(v_x_2534_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v_x_2534_, 1);
v___x_2546_ = lean_unbox(v_a_2545_);
lean_dec(v_a_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
lean_dec_ref(v___f_2533_);
lean_inc(v___y_2532_);
v___x_2547_ = lean_apply_2(v_lose_2531_, v___y_2532_, lean_box(0));
return v___x_2547_;
}
else
{
lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec_ref(v_lose_2531_);
v___x_2548_ = lean_unsigned_to_nat(0u);
v___x_2549_ = 0;
v___x_2550_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2532_);
v___x_2551_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2548_, v___x_2549_, v___x_2550_, v___f_2533_);
return v___x_2551_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lose_2531_ = stack[0].m_obj;
lean_object* v___y_2532_ = stack[1].m_obj;
lean_object* v___f_2533_ = stack[2].m_obj;
lean_object* v_x_2534_ = stack[3].m_obj;
lean_object* v_res_2552_;
v_res_2552_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(v_lose_2531_, v___y_2532_, v___f_2533_, v_x_2534_);
stack->m_obj
 = v_res_2552_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object* v_lose_2553_, lean_object* v___y_2554_, lean_object* v___f_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(v_lose_2553_, v___y_2554_, v___f_2555_, v_x_2556_);
lean_dec(v___y_2554_);
return v_res_2558_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object* v_w_2559_, lean_object* v_lose_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_finished_2563_; lean_object* v_promise_2564_; lean_object* v___f_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; lean_object* v___x_2569_; uint8_t v___y_2571_; uint8_t v___x_2579_; 
v_finished_2563_ = lean_ctor_get(v_w_2559_, 0);
lean_inc(v_finished_2563_);
v_promise_2564_ = lean_ctor_get(v_w_2559_, 1);
lean_inc(v_promise_2564_);
lean_dec_ref(v_w_2559_);
v___f_2565_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2565_, 0, v_promise_2564_);
lean_inc(v___y_2561_);
v___f_2566_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2566_, 0, v_lose_2560_);
lean_closure_set(v___f_2566_, 1, v___y_2561_);
lean_closure_set(v___f_2566_, 2, v___f_2565_);
v___x_2567_ = lean_unsigned_to_nat(0u);
v___x_2568_ = 0;
v___x_2569_ = lean_st_ref_take(v_finished_2563_);
v___x_2579_ = lean_unbox(v___x_2569_);
lean_dec(v___x_2569_);
if (v___x_2579_ == 0)
{
uint8_t v___x_2580_; 
v___x_2580_ = 1;
v___y_2571_ = v___x_2580_;
goto v___jp_2570_;
}
else
{
v___y_2571_ = v___x_2568_;
goto v___jp_2570_;
}
v___jp_2570_:
{
uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2572_ = 1;
v___x_2573_ = lean_box(v___x_2572_);
v___x_2574_ = lean_st_ref_put(v_finished_2563_, v___x_2573_);
lean_dec(v_finished_2563_);
v___x_2575_ = lean_box(v___y_2571_);
v___x_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
v___x_2578_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2567_, v___x_2568_, v___x_2577_, v___f_2566_);
return v___x_2578_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_2559_ = stack[0].m_obj;
lean_object* v_lose_2560_ = stack[1].m_obj;
lean_object* v___y_2561_ = stack[2].m_obj;
lean_object* v_res_2581_;
v_res_2581_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_2559_, v_lose_2560_, v___y_2561_);
stack->m_obj
 = v_res_2581_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object* v_w_2582_, lean_object* v_lose_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_2582_, v_lose_2583_, v___y_2584_);
lean_dec(v___y_2584_);
return v_res_2586_;
}
}
lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object* v___y_2587_, lean_object* v_x_2588_){
_start:
{
if (lean_obj_tag(v_x_2588_) == 0)
{
lean_object* v___x_2590_; 
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v_x_2588_);
return v___x_2590_;
}
else
{
lean_object* v___x_2591_; 
lean_dec_ref_known(v_x_2588_, 1);
v___x_2591_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_2587_);
return v___x_2591_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recvSelector___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2587_ = stack[0].m_obj;
lean_object* v_x_2588_ = stack[1].m_obj;
lean_object* v_res_2592_;
v_res_2592_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_2587_, v_x_2588_);
stack->m_obj
 = v_res_2592_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object* v___y_2593_, lean_object* v_x_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_2593_, v_x_2594_);
lean_dec(v___y_2593_);
return v_res_2596_;
}
}
lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object* v_waiter_2597_, lean_object* v_pendingProducer_2598_, lean_object* v_interestWaiter_2599_, uint8_t v_closed_2600_, lean_object* v_knownSize_2601_, lean_object* v_pendingIncompleteChunk_2602_, lean_object* v_closeError_2603_, uint8_t v_a_2604_, lean_object* v_____r_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___f_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_inc(v___y_2606_);
v___f_2608_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2608_, 0, v___y_2606_);
v___x_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2609_, 0, v_waiter_2597_);
v___x_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2611_, 0, v_pendingProducer_2598_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
lean_ctor_set(v___x_2611_, 2, v_interestWaiter_2599_);
lean_ctor_set(v___x_2611_, 3, v_knownSize_2601_);
lean_ctor_set(v___x_2611_, 4, v_pendingIncompleteChunk_2602_);
lean_ctor_set(v___x_2611_, 5, v_closeError_2603_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*6, v_closed_2600_);
v___x_2612_ = lean_unsigned_to_nat(0u);
v___x_2613_ = lean_st_ref_swap(v___y_2606_, v___x_2611_);
lean_dec(v___x_2613_);
v___x_2614_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2615_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2612_, v_a_2604_, v___x_2614_, v___f_2608_);
return v___x_2615_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recvSelector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_2597_ = stack[0].m_obj;
lean_object* v_pendingProducer_2598_ = stack[1].m_obj;
lean_object* v_interestWaiter_2599_ = stack[2].m_obj;
uint8_t v_closed_2600_ = stack[3].m_num;
lean_object* v_knownSize_2601_ = stack[4].m_obj;
lean_object* v_pendingIncompleteChunk_2602_ = stack[5].m_obj;
lean_object* v_closeError_2603_ = stack[6].m_obj;
uint8_t v_a_2604_ = stack[7].m_num;
lean_object* v_____r_2605_ = stack[8].m_obj;
lean_object* v___y_2606_ = stack[9].m_obj;
lean_object* v_res_2616_;
v_res_2616_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2597_, v_pendingProducer_2598_, v_interestWaiter_2599_, v_closed_2600_, v_knownSize_2601_, v_pendingIncompleteChunk_2602_, v_closeError_2603_, v_a_2604_, v_____r_2605_, v___y_2606_);
stack->m_obj
 = v_res_2616_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object* v_waiter_2617_, lean_object* v_pendingProducer_2618_, lean_object* v_interestWaiter_2619_, lean_object* v_closed_2620_, lean_object* v_knownSize_2621_, lean_object* v_pendingIncompleteChunk_2622_, lean_object* v_closeError_2623_, lean_object* v_a_2624_, lean_object* v_____r_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
uint8_t v_closed_boxed_2628_; uint8_t v_a_5798__boxed_2629_; lean_object* v_res_2630_; 
v_closed_boxed_2628_ = lean_unbox(v_closed_2620_);
v_a_5798__boxed_2629_ = lean_unbox(v_a_2624_);
v_res_2630_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2617_, v_pendingProducer_2618_, v_interestWaiter_2619_, v_closed_boxed_2628_, v_knownSize_2621_, v_pendingIncompleteChunk_2622_, v_closeError_2623_, v_a_5798__boxed_2629_, v_____r_2625_, v___y_2626_);
lean_dec(v___y_2626_);
return v_res_2630_;
}
}
lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object* v_waiter_2635_, uint8_t v_a_2636_, lean_object* v___y_2637_, lean_object* v_x_2638_){
_start:
{
if (lean_obj_tag(v_x_2638_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2648_; 
lean_dec_ref(v_waiter_2635_);
v_a_2640_ = lean_ctor_get(v_x_2638_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_x_2638_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2642_ = v_x_2638_;
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v_x_2638_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
return v___x_2646_;
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v_pendingProducer_2650_; lean_object* v_pendingConsumer_2651_; lean_object* v_interestWaiter_2652_; uint8_t v_closed_2653_; lean_object* v_knownSize_2654_; lean_object* v_pendingIncompleteChunk_2655_; lean_object* v_closeError_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___f_2659_; 
v_a_2649_ = lean_ctor_get(v_x_2638_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v_x_2638_, 1);
v_pendingProducer_2650_ = lean_ctor_get(v_a_2649_, 0);
lean_inc_n(v_pendingProducer_2650_, 2);
v_pendingConsumer_2651_ = lean_ctor_get(v_a_2649_, 1);
lean_inc(v_pendingConsumer_2651_);
v_interestWaiter_2652_ = lean_ctor_get(v_a_2649_, 2);
lean_inc_n(v_interestWaiter_2652_, 2);
v_closed_2653_ = lean_ctor_get_uint8(v_a_2649_, sizeof(void*)*6);
v_knownSize_2654_ = lean_ctor_get(v_a_2649_, 3);
lean_inc_n(v_knownSize_2654_, 2);
v_pendingIncompleteChunk_2655_ = lean_ctor_get(v_a_2649_, 4);
lean_inc_n(v_pendingIncompleteChunk_2655_, 2);
v_closeError_2656_ = lean_ctor_get(v_a_2649_, 5);
lean_inc_n(v_closeError_2656_, 2);
lean_dec(v_a_2649_);
v___x_2657_ = lean_box(v_closed_2653_);
v___x_2658_ = lean_box(v_a_2636_);
lean_inc_ref(v_waiter_2635_);
v___f_2659_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__0___boxed), 11, 8);
lean_closure_set(v___f_2659_, 0, v_waiter_2635_);
lean_closure_set(v___f_2659_, 1, v_pendingProducer_2650_);
lean_closure_set(v___f_2659_, 2, v_interestWaiter_2652_);
lean_closure_set(v___f_2659_, 3, v___x_2657_);
lean_closure_set(v___f_2659_, 4, v_knownSize_2654_);
lean_closure_set(v___f_2659_, 5, v_pendingIncompleteChunk_2655_);
lean_closure_set(v___f_2659_, 6, v_closeError_2656_);
lean_closure_set(v___f_2659_, 7, v___x_2658_);
if (lean_obj_tag(v_pendingConsumer_2651_) == 0)
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec_ref(v___f_2659_);
v___x_2660_ = lean_box(0);
v___x_2661_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_2635_, v_pendingProducer_2650_, v_interestWaiter_2652_, v_closed_2653_, v_knownSize_2654_, v_pendingIncompleteChunk_2655_, v_closeError_2656_, v_a_2636_, v___x_2660_, v___y_2637_);
return v___x_2661_;
}
else
{
lean_object* v___f_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_dec_ref_known(v_pendingConsumer_2651_, 1);
lean_dec(v_closeError_2656_);
lean_dec(v_pendingIncompleteChunk_2655_);
lean_dec(v_knownSize_2654_);
lean_dec(v_interestWaiter_2652_);
lean_dec(v_pendingProducer_2650_);
lean_dec_ref(v_waiter_2635_);
lean_inc(v___y_2637_);
v___f_2662_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2662_, 0, v___f_2659_);
lean_closure_set(v___f_2662_, 1, v___y_2637_);
v___x_2663_ = lean_unsigned_to_nat(0u);
v___x_2664_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1));
v___x_2665_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2663_, v_a_2636_, v___x_2664_, v___f_2662_);
return v___x_2665_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recvSelector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_2635_ = stack[0].m_obj;
uint8_t v_a_2636_ = stack[1].m_num;
lean_object* v___y_2637_ = stack[2].m_obj;
lean_object* v_x_2638_ = stack[3].m_obj;
lean_object* v_res_2666_;
v_res_2666_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v_waiter_2635_, v_a_2636_, v___y_2637_, v_x_2638_);
stack->m_obj
 = v_res_2666_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object* v_waiter_2667_, lean_object* v_a_2668_, lean_object* v___y_2669_, lean_object* v_x_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v_a_5855__boxed_2672_; lean_object* v_res_2673_; 
v_a_5855__boxed_2672_ = lean_unbox(v_a_2668_);
v_res_2673_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v_waiter_2667_, v_a_5855__boxed_2672_, v___y_2669_, v_x_2670_);
lean_dec(v___y_2669_);
return v_res_2673_;
}
}
lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object* v___x_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2674_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recvSelector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2674_ = stack[0].m_obj;
lean_object* v___y_2675_ = stack[1].m_obj;
lean_object* v_res_2679_;
v_res_2679_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_2674_, v___y_2675_);
stack->m_obj
 = v_res_2679_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object* v___x_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_2680_, v___y_2681_);
lean_dec(v___y_2681_);
return v_res_2683_;
}
}
lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object* v_waiter_2686_, lean_object* v___y_2687_, lean_object* v_x_2688_){
_start:
{
if (lean_obj_tag(v_x_2688_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2698_; 
lean_dec_ref(v_waiter_2686_);
v_a_2690_ = lean_ctor_get(v_x_2688_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_x_2688_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2692_ = v_x_2688_;
v_isShared_2693_ = v_isSharedCheck_2698_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v_x_2688_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2698_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2715_; 
v_a_2699_ = lean_ctor_get(v_x_2688_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_x_2688_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2701_ = v_x_2688_;
v_isShared_2702_ = v_isSharedCheck_2715_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v_x_2688_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2715_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
uint8_t v___x_2703_; 
v___x_2703_ = lean_unbox(v_a_2699_);
if (v___x_2703_ == 0)
{
lean_object* v___f_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
lean_inc(v___y_2687_);
lean_inc(v_a_2699_);
v___f_2704_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2704_, 0, v_waiter_2686_);
lean_closure_set(v___f_2704_, 1, v_a_2699_);
lean_closure_set(v___f_2704_, 2, v___y_2687_);
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = lean_st_ref_get(v___y_2687_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v___x_2706_);
v___x_2708_ = v___x_2701_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
v___x_2710_ = lean_unbox(v_a_2699_);
lean_dec(v_a_2699_);
v___x_2711_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2705_, v___x_2710_, v___x_2709_, v___f_2704_);
return v___x_2711_;
}
}
else
{
lean_object* v___f_2713_; lean_object* v___x_2714_; 
lean_del_object(v___x_2701_);
lean_dec(v_a_2699_);
v___f_2713_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_2714_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_waiter_2686_, v___f_2713_, v___y_2687_);
return v___x_2714_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recvSelector___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_2686_ = stack[0].m_obj;
lean_object* v___y_2687_ = stack[1].m_obj;
lean_object* v_x_2688_ = stack[2].m_obj;
lean_object* v_res_2716_;
v_res_2716_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v_waiter_2686_, v___y_2687_, v_x_2688_);
stack->m_obj
 = v_res_2716_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object* v_waiter_2717_, lean_object* v___y_2718_, lean_object* v_x_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v_waiter_2717_, v___y_2718_, v_x_2719_);
lean_dec(v___y_2718_);
return v_res_2721_;
}
}
lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object* v___y_2722_, lean_object* v___f_2723_, lean_object* v_x_2724_){
_start:
{
if (lean_obj_tag(v_x_2724_) == 0)
{
lean_object* v___x_2726_; 
lean_dec_ref(v___f_2723_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_x_2724_);
return v___x_2726_;
}
else
{
lean_object* v___x_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec_ref_known(v_x_2724_, 1);
v___x_2727_ = lean_unsigned_to_nat(0u);
v___x_2728_ = 0;
v___x_2729_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_2722_);
v___x_2730_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2727_, v___x_2728_, v___x_2729_, v___f_2723_);
return v___x_2730_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recvSelector___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2722_ = stack[0].m_obj;
lean_object* v___f_2723_ = stack[1].m_obj;
lean_object* v_x_2724_ = stack[2].m_obj;
lean_object* v_res_2731_;
v_res_2731_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_2722_, v___f_2723_, v_x_2724_);
stack->m_obj
 = v_res_2731_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object* v___y_2732_, lean_object* v___f_2733_, lean_object* v_x_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_2732_, v___f_2733_, v_x_2734_);
lean_dec(v___y_2732_);
return v_res_2736_;
}
}
lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object* v_waiter_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___f_2740_; lean_object* v___f_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_inc_n(v___y_2738_, 2);
v___f_2740_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__4___boxed), 4, 2);
lean_closure_set(v___f_2740_, 0, v_waiter_2737_);
lean_closure_set(v___f_2740_, 1, v___y_2738_);
v___f_2741_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2741_, 0, v___y_2738_);
lean_closure_set(v___f_2741_, 1, v___f_2740_);
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = 0;
v___x_2744_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2738_);
v___x_2745_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2742_, v___x_2743_, v___x_2744_, v___f_2741_);
return v___x_2745_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recvSelector___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_2737_ = stack[0].m_obj;
lean_object* v___y_2738_ = stack[1].m_obj;
lean_object* v_res_2746_;
v_res_2746_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_2737_, v___y_2738_);
stack->m_obj
 = v_res_2746_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object* v_waiter_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_2747_, v___y_2748_);
lean_dec(v___y_2748_);
return v_res_2750_;
}
}
lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object* v_stream_2751_, lean_object* v_waiter_2752_){
_start:
{
lean_object* v___f_2754_; lean_object* v___x_2755_; 
v___f_2754_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2754_, 0, v_waiter_2752_);
v___x_2755_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2751_, v___f_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_recvSelector___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2751_ = stack[0].m_obj;
lean_object* v_waiter_2752_ = stack[1].m_obj;
lean_object* v_res_2756_;
v_res_2756_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_2751_, v_waiter_2752_);
stack->m_obj
 = v_res_2756_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object* v_stream_2757_, lean_object* v_waiter_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_2757_, v_waiter_2758_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object* v_stream_2762_){
_start:
{
lean_object* v___f_2763_; lean_object* v___f_2764_; lean_object* v___f_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___f_2763_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_2762_, 2);
v___f_2764_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2764_, 0, v_stream_2762_);
v___f_2765_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_2766_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2766_, 0, lean_box(0));
lean_closure_set(v___x_2766_, 1, lean_box(0));
lean_closure_set(v___x_2766_, 2, v_stream_2762_);
lean_closure_set(v___x_2766_, 3, v___f_2765_);
v___x_2767_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2767_, 0, lean_box(0));
lean_closure_set(v___x_2767_, 1, lean_box(0));
lean_closure_set(v___x_2767_, 2, v_stream_2762_);
lean_closure_set(v___x_2767_, 3, v___f_2763_);
v___x_2768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___f_2764_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
return v___x_2768_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0(lean_object* v_step_2769_, lean_object* v_acc_2770_, lean_object* v_x_2771_){
_start:
{
if (lean_obj_tag(v_x_2771_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_acc_2770_);
lean_dec_ref(v_step_2769_);
v_a_2773_ = lean_ctor_get(v_x_2771_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_x_2771_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2775_ = v_x_2771_;
v_isShared_2776_ = v_isSharedCheck_2781_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v_x_2771_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2781_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2793_; 
v_a_2782_ = lean_ctor_get(v_x_2771_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_x_2771_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2784_ = v_x_2771_;
v_isShared_2785_ = v_isSharedCheck_2793_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v_x_2771_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2793_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
if (lean_obj_tag(v_a_2782_) == 1)
{
lean_object* v_val_2786_; lean_object* v___x_2787_; 
lean_del_object(v___x_2784_);
v_val_2786_ = lean_ctor_get(v_a_2782_, 0);
lean_inc(v_val_2786_);
lean_dec_ref_known(v_a_2782_, 1);
v___x_2787_ = lean_apply_3(v_step_2769_, v_val_2786_, v_acc_2770_, lean_box(0));
return v___x_2787_;
}
else
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
lean_dec(v_a_2782_);
lean_dec_ref(v_step_2769_);
v___x_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2788_, 0, v_acc_2770_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2788_);
v___x_2790_ = v___x_2784_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
return v___x_2791_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_step_2769_ = stack[0].m_obj;
lean_object* v_acc_2770_ = stack[1].m_obj;
lean_object* v_x_2771_ = stack[2].m_obj;
lean_object* v_res_2794_;
v_res_2794_ = l_Std_Http_Body_Stream_forIn___redArg___lam__0(v_step_2769_, v_acc_2770_, v_x_2771_);
stack->m_obj
 = v_res_2794_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed(lean_object* v_step_2795_, lean_object* v_acc_2796_, lean_object* v_x_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Std_Http_Body_Stream_forIn___redArg___lam__0(v_step_2795_, v_acc_2796_, v_x_2797_);
return v_res_2799_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1(lean_object* v_step_2800_, lean_object* v_stream_2801_, lean_object* v_x_2802_, lean_object* v_acc_2803_){
_start:
{
lean_object* v___f_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___f_2805_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2805_, 0, v_step_2800_);
lean_closure_set(v___f_2805_, 1, v_acc_2803_);
v___x_2806_ = lean_unsigned_to_nat(0u);
v___x_2807_ = 0;
v___x_2808_ = l_Std_Http_Body_Stream_recv(v_stream_2801_);
v___x_2809_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2806_, v___x_2807_, v___x_2808_, v___f_2805_);
return v___x_2809_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_step_2800_ = stack[0].m_obj;
lean_object* v_stream_2801_ = stack[1].m_obj;
lean_object* v_x_2802_ = stack[2].m_obj;
lean_object* v_acc_2803_ = stack[3].m_obj;
lean_object* v_res_2810_;
v_res_2810_ = l_Std_Http_Body_Stream_forIn___redArg___lam__1(v_step_2800_, v_stream_2801_, v_x_2802_, v_acc_2803_);
stack->m_obj
 = v_res_2810_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed(lean_object* v_step_2811_, lean_object* v_stream_2812_, lean_object* v_x_2813_, lean_object* v_acc_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Std_Http_Body_Stream_forIn___redArg___lam__1(v_step_2811_, v_stream_2812_, v_x_2813_, v_acc_2814_);
return v_res_2816_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2(lean_object* v_a_2817_, lean_object* v_x_2818_){
_start:
{
if (lean_obj_tag(v_x_2818_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2828_; 
v_a_2820_ = lean_ctor_get(v_x_2818_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_x_2818_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2822_ = v_x_2818_;
v_isShared_2823_ = v_isSharedCheck_2828_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v_x_2818_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2828_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
}
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec_ref_known(v_x_2818_, 1);
v___x_2829_ = l_IO_Promise_result_x21___redArg(v_a_2817_);
v___x_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2817_ = stack[0].m_obj;
lean_object* v_x_2818_ = stack[1].m_obj;
lean_object* v_res_2831_;
v_res_2831_ = l_Std_Http_Body_Stream_forIn___redArg___lam__2(v_a_2817_, v_x_2818_);
stack->m_obj
 = v_res_2831_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed(lean_object* v_a_2832_, lean_object* v_x_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Std_Http_Body_Stream_forIn___redArg___lam__2(v_a_2832_, v_x_2833_);
lean_dec(v_a_2832_);
return v_res_2835_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3(lean_object* v___f_2836_, lean_object* v___x_2837_, lean_object* v_acc_2838_, lean_object* v_x_2839_){
_start:
{
if (lean_obj_tag(v_x_2839_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_acc_2838_);
lean_dec(v___x_2837_);
lean_dec_ref(v___f_2836_);
v_a_2841_ = lean_ctor_get(v_x_2839_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_x_2839_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2843_ = v_x_2839_;
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v_x_2839_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2862_; 
v_a_2850_ = lean_ctor_get(v_x_2839_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_x_2839_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2852_ = v_x_2839_;
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v_x_2839_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___f_2854_; uint8_t v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2858_; 
lean_inc(v_a_2850_);
v___f_2854_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2854_, 0, v_a_2850_);
v___x_2855_ = 0;
lean_inc(v___x_2837_);
v___x_2856_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_2836_, v___x_2837_, v_a_2850_, v_acc_2838_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2856_);
v___x_2858_ = v___x_2852_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
v___x_2860_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2837_, v___x_2855_, v___x_2859_, v___f_2854_);
return v___x_2860_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2836_ = stack[0].m_obj;
lean_object* v___x_2837_ = stack[1].m_obj;
lean_object* v_acc_2838_ = stack[2].m_obj;
lean_object* v_x_2839_ = stack[3].m_obj;
lean_object* v_res_2863_;
v_res_2863_ = l_Std_Http_Body_Stream_forIn___redArg___lam__3(v___f_2836_, v___x_2837_, v_acc_2838_, v_x_2839_);
stack->m_obj
 = v_res_2863_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed(lean_object* v___f_2864_, lean_object* v___x_2865_, lean_object* v_acc_2866_, lean_object* v_x_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Std_Http_Body_Stream_forIn___redArg___lam__3(v___f_2864_, v___x_2865_, v_acc_2866_, v_x_2867_);
return v_res_2869_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_2870_, lean_object* v_acc_2871_, lean_object* v_step_2872_){
_start:
{
lean_object* v___f_2874_; lean_object* v___x_2875_; lean_object* v___f_2876_; uint8_t v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___f_2874_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2874_, 0, v_step_2872_);
lean_closure_set(v___f_2874_, 1, v_stream_2870_);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___f_2876_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2876_, 0, v___f_2874_);
lean_closure_set(v___f_2876_, 1, v___x_2875_);
lean_closure_set(v___f_2876_, 2, v_acc_2871_);
v___x_2877_ = 0;
v___x_2878_ = lean_io_promise_new();
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
v___x_2881_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2875_, v___x_2877_, v___x_2880_, v___f_2876_);
return v___x_2881_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2870_ = stack[0].m_obj;
lean_object* v_acc_2871_ = stack[1].m_obj;
lean_object* v_step_2872_ = stack[2].m_obj;
lean_object* v_res_2882_;
v_res_2882_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_2870_, v_acc_2871_, v_step_2872_);
stack->m_obj
 = v_res_2882_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_2883_, lean_object* v_acc_2884_, lean_object* v_step_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_2883_, v_acc_2884_, v_step_2885_);
return v_res_2887_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_2888_, lean_object* v_stream_2889_, lean_object* v_acc_2890_, lean_object* v_step_2891_){
_start:
{
lean_object* v___f_2893_; lean_object* v___x_2894_; lean_object* v___f_2895_; uint8_t v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___f_2893_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2893_, 0, v_step_2891_);
lean_closure_set(v___f_2893_, 1, v_stream_2889_);
v___x_2894_ = lean_unsigned_to_nat(0u);
v___f_2895_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2895_, 0, v___f_2893_);
lean_closure_set(v___f_2895_, 1, v___x_2894_);
lean_closure_set(v___f_2895_, 2, v_acc_2890_);
v___x_2896_ = 0;
v___x_2897_ = lean_io_promise_new();
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
v___x_2900_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2894_, v___x_2896_, v___x_2899_, v___f_2895_);
return v___x_2900_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2889_ = stack[1].m_obj;
lean_object* v_acc_2890_ = stack[2].m_obj;
lean_object* v_step_2891_ = stack[3].m_obj;
lean_object* v_res_2901_;
v_res_2901_ = l_Std_Http_Body_Stream_forIn(lean_box(0), v_stream_2889_, v_acc_2890_, v_step_2891_);
stack->m_obj
 = v_res_2901_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_2902_, lean_object* v_stream_2903_, lean_object* v_acc_2904_, lean_object* v_step_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_2902_, v_stream_2903_, v_acc_2904_, v_step_2905_);
return v_res_2907_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___y_2908_);
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2908_ = stack[0].m_obj;
lean_object* v_res_2912_;
v_res_2912_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(v___y_2908_);
stack->m_obj
 = v_res_2912_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0___boxed(lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(v___y_2913_);
return v_res_2915_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(lean_object* v_x_2916_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___closed__0));
return v___x_2918_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2916_ = stack[0].m_obj;
lean_object* v_res_2919_;
v_res_2919_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(v_x_2916_);
stack->m_obj
 = v_res_2919_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1___boxed(lean_object* v_x_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(v_x_2920_);
return v_res_2922_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(lean_object* v_x_2923_){
_start:
{
if (lean_obj_tag(v_x_2923_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2933_; 
v_a_2925_ = lean_ctor_get(v_x_2923_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_x_2923_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2927_ = v_x_2923_;
v_isShared_2928_ = v_isSharedCheck_2933_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v_x_2923_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2933_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2944_; 
v_a_2934_ = lean_ctor_get(v_x_2923_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_x_2923_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2936_ = v_x_2923_;
v_isShared_2937_ = v_isSharedCheck_2944_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v_x_2923_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2944_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v_token_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
v_token_2938_ = lean_ctor_get(v_a_2934_, 1);
lean_inc_ref(v_token_2938_);
lean_dec(v_a_2934_);
v___x_2939_ = l_Std_CancellationToken_selector(v_token_2938_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v___x_2939_);
v___x_2941_ = v___x_2936_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2939_);
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
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2923_ = stack[0].m_obj;
lean_object* v_res_2945_;
v_res_2945_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(v_x_2923_);
stack->m_obj
 = v_res_2945_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2___boxed(lean_object* v_x_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(v_x_2946_);
return v_res_2948_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(lean_object* v_step_2949_, lean_object* v_b_2950_, lean_object* v_a_2951_, lean_object* v_x_2952_){
_start:
{
if (lean_obj_tag(v_x_2952_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v_b_2950_);
lean_dec_ref(v_step_2949_);
v_a_2954_ = lean_ctor_get(v_x_2952_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_x_2952_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2956_ = v_x_2952_;
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v_x_2952_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2974_; 
v_a_2963_ = lean_ctor_get(v_x_2952_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_x_2952_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2965_ = v_x_2952_;
v_isShared_2966_ = v_isSharedCheck_2974_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v_x_2952_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2974_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
if (lean_obj_tag(v_a_2963_) == 1)
{
lean_object* v_val_2967_; lean_object* v___x_2968_; 
lean_del_object(v___x_2965_);
v_val_2967_ = lean_ctor_get(v_a_2963_, 0);
lean_inc(v_val_2967_);
lean_dec_ref_known(v_a_2963_, 1);
lean_inc_ref(v_a_2951_);
v___x_2968_ = lean_apply_4(v_step_2949_, v_val_2967_, v_b_2950_, v_a_2951_, lean_box(0));
return v___x_2968_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
lean_dec(v_a_2963_);
lean_dec_ref(v_step_2949_);
v___x_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2969_, 0, v_b_2950_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 0, v___x_2969_);
v___x_2971_ = v___x_2965_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
return v___x_2972_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_step_2949_ = stack[0].m_obj;
lean_object* v_b_2950_ = stack[1].m_obj;
lean_object* v_a_2951_ = stack[2].m_obj;
lean_object* v_x_2952_ = stack[3].m_obj;
lean_object* v_res_2975_;
v_res_2975_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(v_step_2949_, v_b_2950_, v_a_2951_, v_x_2952_);
stack->m_obj
 = v_res_2975_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed(lean_object* v_step_2976_, lean_object* v_b_2977_, lean_object* v_a_2978_, lean_object* v_x_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(v_step_2976_, v_b_2977_, v_a_2978_, v_x_2979_);
lean_dec_ref(v_a_2978_);
return v_res_2981_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(lean_object* v_stream_2982_, lean_object* v___f_2983_, lean_object* v___f_2984_, lean_object* v___f_2985_, lean_object* v_x_2986_){
_start:
{
if (lean_obj_tag(v_x_2986_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v___f_2985_);
lean_dec_ref(v___f_2984_);
lean_dec_ref(v___f_2983_);
lean_dec_ref(v_stream_2982_);
v_a_2988_ = lean_ctor_get(v_x_2986_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_x_2986_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2990_ = v_x_2986_;
v_isShared_2991_ = v_isSharedCheck_2996_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v_x_2986_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2996_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_a_2997_ = lean_ctor_get(v_x_2986_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v_x_2986_, 1);
v___x_2998_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2982_);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v___f_2983_);
v___x_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3000_, 0, v_a_2997_);
lean_ctor_set(v___x_3000_, 1, v___f_2984_);
v___x_3001_ = lean_unsigned_to_nat(2u);
v___x_3002_ = lean_mk_empty_array_with_capacity(v___x_3001_);
v___x_3003_ = lean_array_push(v___x_3002_, v___x_2999_);
v___x_3004_ = lean_array_push(v___x_3003_, v___x_3000_);
v___x_3005_ = lean_unsigned_to_nat(0u);
v___x_3006_ = 0;
v___x_3007_ = l_Std_Async_Selectable_one___redArg(v___x_3004_);
v___x_3008_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3005_, v___x_3006_, v___x_3007_, v___f_2985_);
return v___x_3008_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_2982_ = stack[0].m_obj;
lean_object* v___f_2983_ = stack[1].m_obj;
lean_object* v___f_2984_ = stack[2].m_obj;
lean_object* v___f_2985_ = stack[3].m_obj;
lean_object* v_x_2986_ = stack[4].m_obj;
lean_object* v_res_3009_;
v_res_3009_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(v_stream_2982_, v___f_2983_, v___f_2984_, v___f_2985_, v_x_2986_);
stack->m_obj
 = v_res_3009_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed(lean_object* v_stream_3010_, lean_object* v___f_3011_, lean_object* v___f_3012_, lean_object* v___f_3013_, lean_object* v_x_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(v_stream_3010_, v___f_3011_, v___f_3012_, v___f_3013_, v_x_3014_);
return v_res_3016_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(lean_object* v_step_3017_, lean_object* v_a_3018_, lean_object* v_stream_3019_, lean_object* v___f_3020_, lean_object* v___f_3021_, lean_object* v___f_3022_, lean_object* v_u_3023_, lean_object* v_b_3024_){
_start:
{
lean_object* v___f_3026_; lean_object* v___f_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_inc_ref_n(v_a_3018_, 2);
v___f_3026_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3026_, 0, v_step_3017_);
lean_closure_set(v___f_3026_, 1, v_b_3024_);
lean_closure_set(v___f_3026_, 2, v_a_3018_);
v___f_3027_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3027_, 0, v_stream_3019_);
lean_closure_set(v___f_3027_, 1, v___f_3020_);
lean_closure_set(v___f_3027_, 2, v___f_3021_);
lean_closure_set(v___f_3027_, 3, v___f_3026_);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = 0;
v___x_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3030_, 0, v_a_3018_);
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
v___x_3032_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3028_, v___x_3029_, v___x_3031_, v___f_3022_);
v___x_3033_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3028_, v___x_3029_, v___x_3032_, v___f_3027_);
return v___x_3033_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_step_3017_ = stack[0].m_obj;
lean_object* v_a_3018_ = stack[1].m_obj;
lean_object* v_stream_3019_ = stack[2].m_obj;
lean_object* v___f_3020_ = stack[3].m_obj;
lean_object* v___f_3021_ = stack[4].m_obj;
lean_object* v___f_3022_ = stack[5].m_obj;
lean_object* v_u_3023_ = stack[6].m_obj;
lean_object* v_b_3024_ = stack[7].m_obj;
lean_object* v_res_3034_;
v_res_3034_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(v_step_3017_, v_a_3018_, v_stream_3019_, v___f_3020_, v___f_3021_, v___f_3022_, v_u_3023_, v_b_3024_);
stack->m_obj
 = v_res_3034_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed(lean_object* v_step_3035_, lean_object* v_a_3036_, lean_object* v_stream_3037_, lean_object* v___f_3038_, lean_object* v___f_3039_, lean_object* v___f_3040_, lean_object* v_u_3041_, lean_object* v_b_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(v_step_3035_, v_a_3036_, v_stream_3037_, v___f_3038_, v___f_3039_, v___f_3040_, v_u_3041_, v_b_3042_);
lean_dec_ref(v_a_3036_);
return v_res_3044_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_3048_, lean_object* v_acc_3049_, lean_object* v_step_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v___f_3053_; lean_object* v___f_3054_; lean_object* v___f_3055_; lean_object* v___f_3056_; lean_object* v___x_3057_; lean_object* v___f_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___f_3053_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_3054_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_3055_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_3051_);
v___f_3056_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_3056_, 0, v_step_3050_);
lean_closure_set(v___f_3056_, 1, v_a_3051_);
lean_closure_set(v___f_3056_, 2, v_stream_3048_);
lean_closure_set(v___f_3056_, 3, v___f_3053_);
lean_closure_set(v___f_3056_, 4, v___f_3054_);
lean_closure_set(v___f_3056_, 5, v___f_3055_);
v___x_3057_ = lean_unsigned_to_nat(0u);
v___f_3058_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3058_, 0, v___f_3056_);
lean_closure_set(v___f_3058_, 1, v___x_3057_);
lean_closure_set(v___f_3058_, 2, v_acc_3049_);
v___x_3059_ = 0;
v___x_3060_ = lean_io_promise_new();
v___x_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
v___x_3063_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3057_, v___x_3059_, v___x_3062_, v___f_3058_);
return v___x_3063_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_3048_ = stack[0].m_obj;
lean_object* v_acc_3049_ = stack[1].m_obj;
lean_object* v_step_3050_ = stack[2].m_obj;
lean_object* v_a_3051_ = stack[3].m_obj;
lean_object* v_res_3064_;
v_res_3064_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_3048_, v_acc_3049_, v_step_3050_, v_a_3051_);
stack->m_obj
 = v_res_3064_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_3065_, lean_object* v_acc_3066_, lean_object* v_step_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_3065_, v_acc_3066_, v_step_3067_, v_a_3068_);
lean_dec_ref(v_a_3068_);
return v_res_3070_;
}
}
lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_3071_, lean_object* v_stream_3072_, lean_object* v_acc_3073_, lean_object* v_step_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v___f_3077_; lean_object* v___f_3078_; lean_object* v___f_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; lean_object* v___f_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___f_3077_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_3078_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_3079_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_3075_);
v___f_3080_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_3080_, 0, v_step_3074_);
lean_closure_set(v___f_3080_, 1, v_a_3075_);
lean_closure_set(v___f_3080_, 2, v_stream_3072_);
lean_closure_set(v___f_3080_, 3, v___f_3077_);
lean_closure_set(v___f_3080_, 4, v___f_3078_);
lean_closure_set(v___f_3080_, 5, v___f_3079_);
v___x_3081_ = lean_unsigned_to_nat(0u);
v___f_3082_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3082_, 0, v___f_3080_);
lean_closure_set(v___f_3082_, 1, v___x_3081_);
lean_closure_set(v___f_3082_, 2, v_acc_3073_);
v___x_3083_ = 0;
v___x_3084_ = lean_io_promise_new();
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
v___x_3087_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3081_, v___x_3083_, v___x_3086_, v___f_3082_);
return v___x_3087_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_forIn_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_3072_ = stack[1].m_obj;
lean_object* v_acc_3073_ = stack[2].m_obj;
lean_object* v_step_3074_ = stack[3].m_obj;
lean_object* v_a_3075_ = stack[4].m_obj;
lean_object* v_res_3088_;
v_res_3088_ = l_Std_Http_Body_Stream_forIn_x27(lean_box(0), v_stream_3072_, v_acc_3073_, v_step_3074_, v_a_3075_);
stack->m_obj
 = v_res_3088_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_3089_, lean_object* v_stream_3090_, lean_object* v_acc_3091_, lean_object* v_step_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_3089_, v_stream_3090_, v_acc_3091_, v_step_3092_, v_a_3093_);
lean_dec_ref(v_a_3093_);
return v_res_3095_;
}
}
lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v_stream_3098_, lean_object* v___f_3099_, lean_object* v___f_3100_, lean_object* v_x_3101_){
_start:
{
if (lean_obj_tag(v_x_3101_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref(v___f_3100_);
lean_dec_ref(v___f_3099_);
lean_dec_ref(v_stream_3098_);
v_a_3103_ = lean_ctor_get(v_x_3101_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_x_3101_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3105_ = v_x_3101_;
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v_x_3101_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_a_3112_ = lean_ctor_get(v_x_3101_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v_x_3101_, 1);
v___x_3113_ = l_Std_Http_Body_Stream_recvSelector(v_stream_3098_);
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
lean_ctor_set(v___x_3114_, 1, v___f_3099_);
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_a_3112_);
lean_ctor_set(v___x_3115_, 1, v___f_3100_);
v___x_3116_ = lean_unsigned_to_nat(2u);
v___x_3117_ = lean_mk_empty_array_with_capacity(v___x_3116_);
v___x_3118_ = lean_array_push(v___x_3117_, v___x_3114_);
v___x_3119_ = lean_array_push(v___x_3118_, v___x_3115_);
v___x_3120_ = l_Std_Async_Selectable_one___redArg(v___x_3119_);
return v___x_3120_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_3098_ = stack[0].m_obj;
lean_object* v___f_3099_ = stack[1].m_obj;
lean_object* v___f_3100_ = stack[2].m_obj;
lean_object* v_x_3101_ = stack[3].m_obj;
lean_object* v_res_3121_;
v_res_3121_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_3098_, v___f_3099_, v___f_3100_, v_x_3101_);
stack->m_obj
 = v_res_3121_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v_stream_3122_, lean_object* v___f_3123_, lean_object* v___f_3124_, lean_object* v_x_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_3122_, v___f_3123_, v___f_3124_, v_x_3125_);
return v_res_3127_;
}
}
lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v___f_3128_, lean_object* v___f_3129_, lean_object* v___f_3130_, lean_object* v_stream_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___f_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___f_3134_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3134_, 0, v_stream_3131_);
lean_closure_set(v___f_3134_, 1, v___f_3128_);
lean_closure_set(v___f_3134_, 2, v___f_3129_);
v___x_3135_ = lean_unsigned_to_nat(0u);
v___x_3136_ = 0;
lean_inc_ref(v___y_3132_);
v___x_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___y_3132_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
v___x_3139_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3135_, v___x_3136_, v___x_3138_, v___f_3130_);
v___x_3140_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3135_, v___x_3136_, v___x_3139_, v___f_3134_);
return v___x_3140_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3128_ = stack[0].m_obj;
lean_object* v___f_3129_ = stack[1].m_obj;
lean_object* v___f_3130_ = stack[2].m_obj;
lean_object* v_stream_3131_ = stack[3].m_obj;
lean_object* v___y_3132_ = stack[4].m_obj;
lean_object* v_res_3141_;
v_res_3141_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v___f_3128_, v___f_3129_, v___f_3130_, v_stream_3131_, v___y_3132_);
stack->m_obj
 = v_res_3141_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v___f_3142_, lean_object* v___f_3143_, lean_object* v___f_3144_, lean_object* v_stream_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v___f_3142_, v___f_3143_, v___f_3144_, v_stream_3145_, v___y_3146_);
lean_dec_ref(v___y_3146_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v_toPure_3156_, lean_object* v_result_3157_, lean_object* v_maximumSize_3158_, lean_object* v_inst_3159_, lean_object* v_inst_3160_, lean_object* v_inst_3161_, lean_object* v_stream_3162_, lean_object* v_toBind_3163_, lean_object* v_____do__lift_3164_){
_start:
{
if (lean_obj_tag(v_____do__lift_3164_) == 0)
{
lean_object* v___x_3165_; 
lean_dec(v_toBind_3163_);
lean_dec_ref(v_stream_3162_);
lean_dec(v_inst_3161_);
lean_dec_ref(v_inst_3160_);
lean_dec_ref(v_inst_3159_);
lean_dec(v_maximumSize_3158_);
v___x_3165_ = lean_apply_2(v_toPure_3156_, lean_box(0), v_result_3157_);
return v___x_3165_;
}
else
{
lean_object* v_val_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_toPure_3156_);
v_val_3166_ = lean_ctor_get(v_____do__lift_3164_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_____do__lift_3164_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3168_ = v_____do__lift_3164_;
v_isShared_3169_ = v_isSharedCheck_3197_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_val_3166_);
lean_dec(v_____do__lift_3164_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3197_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v_data_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; lean_object* v_result_3175_; 
v_data_3170_ = lean_ctor_get(v_val_3166_, 0);
lean_inc_ref(v_data_3170_);
lean_dec(v_val_3166_);
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = lean_byte_array_size(v_result_3157_);
v___x_3173_ = lean_byte_array_size(v_data_3170_);
v___x_3174_ = 0;
v_result_3175_ = lean_byte_array_copy_slice(v_data_3170_, v___x_3171_, v_result_3157_, v___x_3172_, v___x_3173_, v___x_3174_);
lean_dec_ref(v_data_3170_);
if (lean_obj_tag(v_maximumSize_3158_) == 1)
{
lean_object* v_val_3176_; lean_object* v___x_3177_; uint64_t v___x_3178_; uint64_t v___x_3179_; uint8_t v___x_3180_; 
v_val_3176_ = lean_ctor_get(v_maximumSize_3158_, 0);
v___x_3177_ = lean_byte_array_size(v_result_3175_);
v___x_3178_ = lean_uint64_of_nat(v___x_3177_);
v___x_3179_ = lean_unbox_uint64(v_val_3176_);
v___x_3180_ = lean_uint64_dec_lt(v___x_3179_, v___x_3178_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
lean_del_object(v___x_3168_);
lean_dec(v_toBind_3163_);
v___x_3181_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3159_, v_inst_3160_, v_inst_3161_, v_stream_3162_, v_maximumSize_3158_, v_result_3175_);
return v___x_3181_;
}
else
{
lean_object* v_throw_3182_; lean_object* v___f_3183_; lean_object* v___x_3184_; uint64_t v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3192_; 
lean_inc(v_val_3176_);
v_throw_3182_ = lean_ctor_get(v_inst_3160_, 0);
lean_inc(v_throw_3182_);
v___f_3183_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0), 7, 6);
lean_closure_set(v___f_3183_, 0, v_inst_3159_);
lean_closure_set(v___f_3183_, 1, v_inst_3160_);
lean_closure_set(v___f_3183_, 2, v_inst_3161_);
lean_closure_set(v___f_3183_, 3, v_stream_3162_);
lean_closure_set(v___f_3183_, 4, v_maximumSize_3158_);
lean_closure_set(v___f_3183_, 5, v_result_3175_);
v___x_3184_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0));
v___x_3185_ = lean_unbox_uint64(v_val_3176_);
lean_dec(v_val_3176_);
v___x_3186_ = lean_uint64_to_nat(v___x_3185_);
v___x_3187_ = l_Nat_reprFast(v___x_3186_);
v___x_3188_ = lean_string_append(v___x_3184_, v___x_3187_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1));
v___x_3190_ = lean_string_append(v___x_3188_, v___x_3189_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set_tag(v___x_3168_, 18);
lean_ctor_set(v___x_3168_, 0, v___x_3190_);
v___x_3192_ = v___x_3168_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_apply_2(v_throw_3182_, lean_box(0), v___x_3192_);
v___x_3194_ = lean_apply_4(v_toBind_3163_, lean_box(0), lean_box(0), v___x_3193_, v___f_3183_);
return v___x_3194_;
}
}
}
else
{
lean_object* v___x_3196_; 
lean_del_object(v___x_3168_);
lean_dec(v_toBind_3163_);
v___x_3196_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3159_, v_inst_3160_, v_inst_3161_, v_stream_3162_, v_maximumSize_3158_, v_result_3175_);
return v___x_3196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_3198_, lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_stream_3201_, lean_object* v_maximumSize_3202_, lean_object* v_result_3203_){
_start:
{
lean_object* v_toApplicative_3204_; lean_object* v_toBind_3205_; lean_object* v_toPure_3206_; lean_object* v___x_3207_; lean_object* v___f_3208_; lean_object* v___x_3209_; 
v_toApplicative_3204_ = lean_ctor_get(v_inst_3198_, 0);
v_toBind_3205_ = lean_ctor_get(v_inst_3198_, 1);
lean_inc_n(v_toBind_3205_, 2);
v_toPure_3206_ = lean_ctor_get(v_toApplicative_3204_, 1);
lean_inc(v_toPure_3206_);
lean_inc(v_inst_3200_);
lean_inc_ref(v_stream_3201_);
v___x_3207_ = lean_apply_1(v_inst_3200_, v_stream_3201_);
v___f_3208_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 9, 8);
lean_closure_set(v___f_3208_, 0, v_toPure_3206_);
lean_closure_set(v___f_3208_, 1, v_result_3203_);
lean_closure_set(v___f_3208_, 2, v_maximumSize_3202_);
lean_closure_set(v___f_3208_, 3, v_inst_3198_);
lean_closure_set(v___f_3208_, 4, v_inst_3199_);
lean_closure_set(v___f_3208_, 5, v_inst_3200_);
lean_closure_set(v___f_3208_, 6, v_stream_3201_);
lean_closure_set(v___f_3208_, 7, v_toBind_3205_);
v___x_3209_ = lean_apply_4(v_toBind_3205_, lean_box(0), lean_box(0), v___x_3207_, v___f_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_stream_3213_, lean_object* v_maximumSize_3214_, lean_object* v_result_3215_, lean_object* v_____r_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3210_, v_inst_3211_, v_inst_3212_, v_stream_3213_, v_maximumSize_3214_, v_result_3215_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_3218_, lean_object* v_inst_3219_, lean_object* v_inst_3220_, lean_object* v_inst_3221_, lean_object* v_stream_3222_, lean_object* v_maximumSize_3223_, lean_object* v_result_3224_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3219_, v_inst_3220_, v_inst_3221_, v_stream_3222_, v_maximumSize_3223_, v_result_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_toPure_3228_, lean_object* v_result_3229_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_apply_1(v_inst_3226_, v_result_3229_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3240_; 
lean_dec(v_toPure_3228_);
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3240_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3240_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_throw_3235_; lean_object* v___x_3237_; 
v_throw_3235_ = lean_ctor_get(v_inst_3227_, 0);
lean_inc(v_throw_3235_);
lean_dec_ref(v_inst_3227_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 18);
v___x_3237_ = v___x_3233_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3231_);
v___x_3237_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_apply_2(v_throw_3235_, lean_box(0), v___x_3237_);
return v___x_3238_;
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3242_; 
lean_dec_ref(v_inst_3227_);
v_a_3241_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3241_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3242_ = lean_apply_2(v_toPure_3228_, lean_box(0), v_a_3241_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_stream_3247_, lean_object* v_maximumSize_3248_){
_start:
{
lean_object* v_toApplicative_3249_; lean_object* v_toBind_3250_; lean_object* v_toPure_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___f_3254_; lean_object* v___x_3255_; 
v_toApplicative_3249_ = lean_ctor_get(v_inst_3244_, 0);
v_toBind_3250_ = lean_ctor_get(v_inst_3244_, 1);
lean_inc(v_toBind_3250_);
v_toPure_3251_ = lean_ctor_get(v_toApplicative_3249_, 1);
lean_inc(v_toPure_3251_);
v___x_3252_ = l_ByteArray_empty;
lean_inc_ref(v_inst_3245_);
v___x_3253_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3244_, v_inst_3245_, v_inst_3246_, v_stream_3247_, v_maximumSize_3248_, v___x_3252_);
v___f_3254_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3254_, 0, v_inst_3243_);
lean_closure_set(v___f_3254_, 1, v_inst_3245_);
lean_closure_set(v___f_3254_, 2, v_toPure_3251_);
v___x_3255_ = lean_apply_4(v_toBind_3250_, lean_box(0), lean_box(0), v___x_3253_, v___f_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_3256_, lean_object* v_m_3257_, lean_object* v_inst_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_stream_3262_, lean_object* v_maximumSize_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_3258_, v_inst_3259_, v_inst_3260_, v_inst_3261_, v_stream_3262_, v_maximumSize_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0(lean_object* v_toPure_3265_, lean_object* v_____r_3266_){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_apply_2(v_toPure_3265_, lean_box(0), v___x_3267_);
return v___x_3268_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(lean_object* v_toPure_3269_, uint64_t v_consumed_3270_, lean_object* v_drainLimit_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_stream_3274_, lean_object* v_closeStream_3275_, lean_object* v_toBind_3276_, lean_object* v___f_3277_, lean_object* v_____do__lift_3278_){
_start:
{
if (lean_obj_tag(v_____do__lift_3278_) == 0)
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_dec(v___f_3277_);
lean_dec(v_toBind_3276_);
lean_dec(v_closeStream_3275_);
lean_dec_ref(v_stream_3274_);
lean_dec(v_inst_3273_);
lean_dec_ref(v_inst_3272_);
lean_dec(v_drainLimit_3271_);
v___x_3279_ = lean_box(0);
v___x_3280_ = lean_apply_2(v_toPure_3269_, lean_box(0), v___x_3279_);
return v___x_3280_;
}
else
{
lean_object* v_val_3281_; lean_object* v_data_3282_; lean_object* v___x_3283_; uint64_t v___x_3284_; uint64_t v_consumed_3285_; 
lean_dec(v_toPure_3269_);
v_val_3281_ = lean_ctor_get(v_____do__lift_3278_, 0);
v_data_3282_ = lean_ctor_get(v_val_3281_, 0);
v___x_3283_ = lean_byte_array_size(v_data_3282_);
v___x_3284_ = lean_uint64_of_nat(v___x_3283_);
v_consumed_3285_ = lean_uint64_add(v_consumed_3270_, v___x_3284_);
if (lean_obj_tag(v_drainLimit_3271_) == 1)
{
lean_object* v_val_3286_; uint64_t v___x_3287_; uint8_t v___x_3288_; 
v_val_3286_ = lean_ctor_get(v_drainLimit_3271_, 0);
v___x_3287_ = lean_unbox_uint64(v_val_3286_);
v___x_3288_ = lean_uint64_dec_lt(v___x_3287_, v_consumed_3285_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
lean_dec(v___f_3277_);
lean_dec(v_toBind_3276_);
v___x_3289_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3272_, v_inst_3273_, v_stream_3274_, v_drainLimit_3271_, v_closeStream_3275_, v_consumed_3285_);
return v___x_3289_;
}
else
{
lean_object* v___x_3290_; 
lean_dec_ref_known(v_drainLimit_3271_, 1);
lean_dec_ref(v_stream_3274_);
lean_dec(v_inst_3273_);
lean_dec_ref(v_inst_3272_);
v___x_3290_ = lean_apply_4(v_toBind_3276_, lean_box(0), lean_box(0), v_closeStream_3275_, v___f_3277_);
return v___x_3290_;
}
}
else
{
lean_object* v___x_3291_; 
lean_dec(v___f_3277_);
lean_dec(v_toBind_3276_);
v___x_3291_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3272_, v_inst_3273_, v_stream_3274_, v_drainLimit_3271_, v_closeStream_3275_, v_consumed_3285_);
return v___x_3291_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3269_ = stack[0].m_obj;
uint64_t v_consumed_3270_ = stack[1].m_num;
lean_object* v_drainLimit_3271_ = stack[2].m_obj;
lean_object* v_inst_3272_ = stack[3].m_obj;
lean_object* v_inst_3273_ = stack[4].m_obj;
lean_object* v_stream_3274_ = stack[5].m_obj;
lean_object* v_closeStream_3275_ = stack[6].m_obj;
lean_object* v_toBind_3276_ = stack[7].m_obj;
lean_object* v___f_3277_ = stack[8].m_obj;
lean_object* v_____do__lift_3278_ = stack[9].m_obj;
lean_object* v_res_3292_;
v_res_3292_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(v_toPure_3269_, v_consumed_3270_, v_drainLimit_3271_, v_inst_3272_, v_inst_3273_, v_stream_3274_, v_closeStream_3275_, v_toBind_3276_, v___f_3277_, v_____do__lift_3278_);
stack->m_obj
 = v_res_3292_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed(lean_object* v_toPure_3293_, lean_object* v_consumed_3294_, lean_object* v_drainLimit_3295_, lean_object* v_inst_3296_, lean_object* v_inst_3297_, lean_object* v_stream_3298_, lean_object* v_closeStream_3299_, lean_object* v_toBind_3300_, lean_object* v___f_3301_, lean_object* v_____do__lift_3302_){
_start:
{
uint64_t v_consumed_boxed_3303_; lean_object* v_res_3304_; 
v_consumed_boxed_3303_ = lean_unbox_uint64(v_consumed_3294_);
lean_dec_ref(v_consumed_3294_);
v_res_3304_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(v_toPure_3293_, v_consumed_boxed_3303_, v_drainLimit_3295_, v_inst_3296_, v_inst_3297_, v_stream_3298_, v_closeStream_3299_, v_toBind_3300_, v___f_3301_, v_____do__lift_3302_);
lean_dec(v_____do__lift_3302_);
return v_res_3304_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(lean_object* v_inst_3305_, lean_object* v_inst_3306_, lean_object* v_stream_3307_, lean_object* v_drainLimit_3308_, lean_object* v_closeStream_3309_, uint64_t v_consumed_3310_){
_start:
{
lean_object* v_toApplicative_3311_; lean_object* v_toBind_3312_; lean_object* v_toPure_3313_; lean_object* v___x_3314_; lean_object* v___f_3315_; lean_object* v___x_3316_; lean_object* v___f_3317_; lean_object* v___x_3318_; 
v_toApplicative_3311_ = lean_ctor_get(v_inst_3305_, 0);
v_toBind_3312_ = lean_ctor_get(v_inst_3305_, 1);
lean_inc_n(v_toBind_3312_, 2);
v_toPure_3313_ = lean_ctor_get(v_toApplicative_3311_, 1);
lean_inc_n(v_toPure_3313_, 2);
lean_inc(v_inst_3306_);
lean_inc_ref(v_stream_3307_);
v___x_3314_ = lean_apply_1(v_inst_3306_, v_stream_3307_);
v___f_3315_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3315_, 0, v_toPure_3313_);
v___x_3316_ = lean_box_uint64(v_consumed_3310_);
v___f_3317_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3317_, 0, v_toPure_3313_);
lean_closure_set(v___f_3317_, 1, v___x_3316_);
lean_closure_set(v___f_3317_, 2, v_drainLimit_3308_);
lean_closure_set(v___f_3317_, 3, v_inst_3305_);
lean_closure_set(v___f_3317_, 4, v_inst_3306_);
lean_closure_set(v___f_3317_, 5, v_stream_3307_);
lean_closure_set(v___f_3317_, 6, v_closeStream_3309_);
lean_closure_set(v___f_3317_, 7, v_toBind_3312_);
lean_closure_set(v___f_3317_, 8, v___f_3315_);
v___x_3318_ = lean_apply_4(v_toBind_3312_, lean_box(0), lean_box(0), v___x_3314_, v___f_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3305_ = stack[0].m_obj;
lean_object* v_inst_3306_ = stack[1].m_obj;
lean_object* v_stream_3307_ = stack[2].m_obj;
lean_object* v_drainLimit_3308_ = stack[3].m_obj;
lean_object* v_closeStream_3309_ = stack[4].m_obj;
uint64_t v_consumed_3310_ = stack[5].m_num;
lean_object* v_res_3319_;
v_res_3319_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3305_, v_inst_3306_, v_stream_3307_, v_drainLimit_3308_, v_closeStream_3309_, v_consumed_3310_);
stack->m_obj
 = v_res_3319_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___boxed(lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_stream_3322_, lean_object* v_drainLimit_3323_, lean_object* v_closeStream_3324_, lean_object* v_consumed_3325_){
_start:
{
uint64_t v_consumed_boxed_3326_; lean_object* v_res_3327_; 
v_consumed_boxed_3326_ = lean_unbox_uint64(v_consumed_3325_);
lean_dec_ref(v_consumed_3325_);
v_res_3327_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3320_, v_inst_3321_, v_stream_3322_, v_drainLimit_3323_, v_closeStream_3324_, v_consumed_boxed_3326_);
return v_res_3327_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_object* v_m_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_stream_3331_, lean_object* v_drainLimit_3332_, lean_object* v_closeStream_3333_, uint64_t v_consumed_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3329_, v_inst_3330_, v_stream_3331_, v_drainLimit_3332_, v_closeStream_3333_, v_consumed_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3329_ = stack[1].m_obj;
lean_object* v_inst_3330_ = stack[2].m_obj;
lean_object* v_stream_3331_ = stack[3].m_obj;
lean_object* v_drainLimit_3332_ = stack[4].m_obj;
lean_object* v_closeStream_3333_ = stack[5].m_obj;
uint64_t v_consumed_3334_ = stack[6].m_num;
lean_object* v_res_3336_;
v_res_3336_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_box(0), v_inst_3329_, v_inst_3330_, v_stream_3331_, v_drainLimit_3332_, v_closeStream_3333_, v_consumed_3334_);
stack->m_obj
 = v_res_3336_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___boxed(lean_object* v_m_3337_, lean_object* v_inst_3338_, lean_object* v_inst_3339_, lean_object* v_stream_3340_, lean_object* v_drainLimit_3341_, lean_object* v_closeStream_3342_, lean_object* v_consumed_3343_){
_start:
{
uint64_t v_consumed_boxed_3344_; lean_object* v_res_3345_; 
v_consumed_boxed_3344_ = lean_unbox_uint64(v_consumed_3343_);
lean_dec_ref(v_consumed_3343_);
v_res_3345_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(v_m_3337_, v_inst_3338_, v_inst_3339_, v_stream_3340_, v_drainLimit_3341_, v_closeStream_3342_, v_consumed_boxed_3344_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain___redArg(lean_object* v_inst_3346_, lean_object* v_inst_3347_, lean_object* v_stream_3348_, lean_object* v_drainLimit_3349_, lean_object* v_closeStream_3350_){
_start:
{
uint64_t v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = 0ULL;
v___x_3352_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3346_, v_inst_3347_, v_stream_3348_, v_drainLimit_3349_, v_closeStream_3350_, v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain(lean_object* v_m_3353_, lean_object* v_inst_3354_, lean_object* v_inst_3355_, lean_object* v_stream_3356_, lean_object* v_drainLimit_3357_, lean_object* v_closeStream_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Std_Http_Body_Stream_drain___redArg(v_inst_3354_, v_inst_3355_, v_stream_3356_, v_drainLimit_3357_, v_closeStream_3358_);
return v___x_3359_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t v_incomplete_3365_, lean_object* v_chunk_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v_pendingProducer_3371_; lean_object* v_pendingConsumer_3372_; lean_object* v_interestWaiter_3373_; uint8_t v_closed_3374_; lean_object* v_knownSize_3375_; lean_object* v_pendingIncompleteChunk_3376_; lean_object* v_closeError_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3418_; 
v___x_3369_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_3367_);
v___x_3370_ = lean_st_ref_get(v___y_3367_);
v_pendingProducer_3371_ = lean_ctor_get(v___x_3370_, 0);
v_pendingConsumer_3372_ = lean_ctor_get(v___x_3370_, 1);
v_interestWaiter_3373_ = lean_ctor_get(v___x_3370_, 2);
v_closed_3374_ = lean_ctor_get_uint8(v___x_3370_, sizeof(void*)*6);
v_knownSize_3375_ = lean_ctor_get(v___x_3370_, 3);
v_pendingIncompleteChunk_3376_ = lean_ctor_get(v___x_3370_, 4);
v_closeError_3377_ = lean_ctor_get(v___x_3370_, 5);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3379_ = v___x_3370_;
v_isShared_3380_ = v_isSharedCheck_3418_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_closeError_3377_);
lean_inc(v_pendingIncompleteChunk_3376_);
lean_inc(v_knownSize_3375_);
lean_inc(v_interestWaiter_3373_);
lean_inc(v_pendingConsumer_3372_);
lean_inc(v_pendingProducer_3371_);
lean_dec(v___x_3370_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3418_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___y_3382_; 
if (v_closed_3374_ == 0)
{
if (lean_obj_tag(v_pendingIncompleteChunk_3376_) == 0)
{
v___y_3382_ = v_chunk_3366_;
goto v___jp_3381_;
}
else
{
lean_object* v_val_3396_; lean_object* v_data_3397_; lean_object* v_extensions_3398_; lean_object* v_data_3399_; lean_object* v_extensions_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3416_; 
v_val_3396_ = lean_ctor_get(v_pendingIncompleteChunk_3376_, 0);
lean_inc(v_val_3396_);
lean_dec_ref_known(v_pendingIncompleteChunk_3376_, 1);
v_data_3397_ = lean_ctor_get(v_val_3396_, 0);
lean_inc_ref(v_data_3397_);
v_extensions_3398_ = lean_ctor_get(v_val_3396_, 1);
lean_inc_ref(v_extensions_3398_);
lean_dec(v_val_3396_);
v_data_3399_ = lean_ctor_get(v_chunk_3366_, 0);
v_extensions_3400_ = lean_ctor_get(v_chunk_3366_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_chunk_3366_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3402_ = v_chunk_3366_;
v_isShared_3403_ = v_isSharedCheck_3416_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_extensions_3400_);
lean_inc(v_data_3399_);
lean_dec(v_chunk_3366_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3416_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_byte_array_size(v_data_3397_);
v___x_3406_ = lean_byte_array_size(v_data_3399_);
v___x_3407_ = lean_byte_array_copy_slice(v_data_3399_, v___x_3404_, v_data_3397_, v___x_3405_, v___x_3406_, v_closed_3374_);
lean_dec_ref(v_data_3399_);
v___x_3408_ = lean_array_get_size(v_extensions_3398_);
v___x_3409_ = lean_nat_dec_eq(v___x_3408_, v___x_3404_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3411_; 
lean_dec_ref(v_extensions_3400_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 1, v_extensions_3398_);
lean_ctor_set(v___x_3402_, 0, v___x_3407_);
v___x_3411_ = v___x_3402_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3407_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_extensions_3398_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
v___y_3382_ = v___x_3411_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3414_; 
lean_dec_ref(v_extensions_3398_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v___x_3407_);
v___x_3414_ = v___x_3402_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3407_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_extensions_3400_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
v___y_3382_ = v___x_3414_;
goto v___jp_3381_;
}
}
}
}
}
else
{
lean_object* v___x_3417_; 
lean_del_object(v___x_3379_);
lean_dec(v_closeError_3377_);
lean_dec(v_pendingIncompleteChunk_3376_);
lean_dec(v_knownSize_3375_);
lean_dec(v_interestWaiter_3373_);
lean_dec(v_pendingConsumer_3372_);
lean_dec(v_pendingProducer_3371_);
lean_dec_ref(v_chunk_3366_);
v___x_3417_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_3417_;
}
v___jp_3381_:
{
if (v_incomplete_3365_ == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3383_ = lean_box(0);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 4, v___x_3383_);
v___x_3385_ = v___x_3379_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_pendingProducer_3371_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_pendingConsumer_3372_);
lean_ctor_set(v_reuseFailAlloc_3389_, 2, v_interestWaiter_3373_);
lean_ctor_set(v_reuseFailAlloc_3389_, 3, v_knownSize_3375_);
lean_ctor_set(v_reuseFailAlloc_3389_, 4, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3389_, 5, v_closeError_3377_);
lean_ctor_set_uint8(v_reuseFailAlloc_3389_, sizeof(void*)*6, v_closed_3374_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = lean_st_ref_swap(v___y_3367_, v___x_3385_);
lean_dec(v___x_3386_);
v___x_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___y_3382_);
v___x_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___y_3382_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 4, v___x_3390_);
v___x_3392_ = v___x_3379_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_pendingProducer_3371_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_pendingConsumer_3372_);
lean_ctor_set(v_reuseFailAlloc_3395_, 2, v_interestWaiter_3373_);
lean_ctor_set(v_reuseFailAlloc_3395_, 3, v_knownSize_3375_);
lean_ctor_set(v_reuseFailAlloc_3395_, 4, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3395_, 5, v_closeError_3377_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, sizeof(void*)*6, v_closed_3374_);
v___x_3392_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = lean_st_ref_swap(v___y_3367_, v___x_3392_);
lean_dec(v___x_3393_);
v___x_3394_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
return v___x_3394_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_incomplete_3365_ = stack[0].m_num;
lean_object* v_chunk_3366_ = stack[1].m_obj;
lean_object* v___y_3367_ = stack[2].m_obj;
lean_object* v_res_3419_;
v_res_3419_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_incomplete_3365_, v_chunk_3366_, v___y_3367_);
stack->m_obj
 = v_res_3419_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_incomplete_3420_, lean_object* v_chunk_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
uint8_t v_incomplete_boxed_3424_; lean_object* v_res_3425_; 
v_incomplete_boxed_3424_ = lean_unbox(v_incomplete_3420_);
v_res_3425_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_incomplete_boxed_3424_, v_chunk_3421_, v___y_3422_);
lean_dec(v___y_3422_);
return v_res_3425_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_3426_, lean_object* v_chunk_3427_, uint8_t v_incomplete_3428_){
_start:
{
lean_object* v___x_3430_; lean_object* v___f_3431_; lean_object* v___x_3432_; 
v___x_3430_ = lean_box(v_incomplete_3428_);
v___f_3431_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3431_, 0, v___x_3430_);
lean_closure_set(v___f_3431_, 1, v_chunk_3427_);
v___x_3432_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_3426_, v___f_3431_);
return v___x_3432_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_3426_ = stack[0].m_obj;
lean_object* v_chunk_3427_ = stack[1].m_obj;
uint8_t v_incomplete_3428_ = stack[2].m_num;
lean_object* v_res_3433_;
v_res_3433_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3426_, v_chunk_3427_, v_incomplete_3428_);
stack->m_obj
 = v_res_3433_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_3434_, lean_object* v_chunk_3435_, lean_object* v_incomplete_3436_, lean_object* v_a_3437_){
_start:
{
uint8_t v_incomplete_boxed_3438_; lean_object* v_res_3439_; 
v_incomplete_boxed_3438_ = lean_unbox(v_incomplete_3436_);
v_res_3439_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3434_, v_chunk_3435_, v_incomplete_boxed_3438_);
return v_res_3439_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_3446_){
_start:
{
if (lean_obj_tag(v_x_3446_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3456_; 
v_a_3448_ = lean_ctor_get(v_x_3446_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_x_3446_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3450_ = v_x_3446_;
v_isShared_3451_ = v_isSharedCheck_3456_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v_x_3446_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3456_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
return v___x_3454_;
}
}
}
else
{
lean_object* v___x_3457_; 
lean_dec_ref_known(v_x_3446_, 1);
v___x_3457_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_3457_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3446_ = stack[0].m_obj;
lean_object* v_res_3458_;
v_res_3458_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_3446_);
stack->m_obj
 = v_res_3458_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_3459_);
return v_res_3461_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___3462_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3464_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_00___3462_ = stack[0].m_obj;
lean_object* v_res_3465_;
v_res_3465_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___3462_);
stack->m_obj
 = v_res_3465_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___3466_);
return v_res_3468_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_3473_, lean_object* v_x_3474_){
_start:
{
if (lean_obj_tag(v_x_3474_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref(v___f_3473_);
v_a_3478_ = lean_ctor_get(v_x_3474_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_x_3474_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3480_ = v_x_3474_;
v_isShared_3481_ = v_isSharedCheck_3486_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v_x_3474_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3486_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
return v___x_3484_;
}
}
}
else
{
lean_object* v_a_3487_; 
v_a_3487_ = lean_ctor_get(v_x_3474_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v_x_3474_, 1);
if (lean_obj_tag(v_a_3487_) == 1)
{
lean_object* v_val_3488_; uint8_t v___x_3489_; 
v_val_3488_ = lean_ctor_get(v_a_3487_, 0);
lean_inc(v_val_3488_);
lean_dec_ref_known(v_a_3487_, 1);
v___x_3489_ = lean_unbox(v_val_3488_);
lean_dec(v_val_3488_);
if (v___x_3489_ == 1)
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = lean_box(0);
v___x_3491_ = lean_apply_2(v___f_3473_, v___x_3490_, lean_box(0));
return v___x_3491_;
}
else
{
lean_dec_ref(v___f_3473_);
goto v___jp_3476_;
}
}
else
{
lean_dec(v_a_3487_);
lean_dec_ref(v___f_3473_);
goto v___jp_3476_;
}
}
v___jp_3476_:
{
lean_object* v___x_3477_; 
v___x_3477_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_3477_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3473_ = stack[0].m_obj;
lean_object* v_x_3474_ = stack[1].m_obj;
lean_object* v_res_3492_;
v_res_3492_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_3473_, v_x_3474_);
stack->m_obj
 = v_res_3492_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_3493_, lean_object* v_x_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_3493_, v_x_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_3497_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_a_3497_);
return v___x_3498_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_3499_, lean_object* v_x_3500_){
_start:
{
if (lean_obj_tag(v_x_3500_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3510_; 
v_a_3502_ = lean_ctor_get(v_x_3500_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_x_3500_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3504_ = v_x_3500_;
v_isShared_3505_ = v_isSharedCheck_3510_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v_x_3500_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3510_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
return v___x_3508_;
}
}
}
else
{
lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3521_; 
v_isSharedCheck_3521_ = !lean_is_exclusive(v_x_3500_);
if (v_isSharedCheck_3521_ == 0)
{
lean_object* v_unused_3522_; 
v_unused_3522_ = lean_ctor_get(v_x_3500_, 0);
lean_dec(v_unused_3522_);
v___x_3512_ = v_x_3500_;
v_isShared_3513_ = v_isSharedCheck_3521_;
goto v_resetjp_3511_;
}
else
{
lean_dec(v_x_3500_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3521_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3514_ = lean_box(v___x_3499_);
v___x_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3515_);
v___x_3517_ = v___x_3512_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
v___x_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
return v___x_3519_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3499_ = stack[0].m_num;
lean_object* v_x_3500_ = stack[1].m_obj;
lean_object* v_res_3523_;
v_res_3523_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_3499_, v_x_3500_);
stack->m_obj
 = v_res_3523_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_3524_, lean_object* v_x_3525_, lean_object* v___y_3526_){
_start:
{
uint8_t v___x_5142__boxed_3527_; lean_object* v_res_3528_; 
v___x_5142__boxed_3527_ = lean_unbox(v___x_3524_);
v_res_3528_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5142__boxed_3527_, v_x_3525_);
return v_res_3528_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_3529_, lean_object* v_x_3530_){
_start:
{
if (lean_obj_tag(v_x_3530_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3540_; 
v_a_3532_ = lean_ctor_get(v_x_3530_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_x_3530_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3534_ = v_x_3530_;
v_isShared_3535_ = v_isSharedCheck_3540_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v_x_3530_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3540_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
return v___x_3538_;
}
}
}
else
{
lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3551_; 
v_isSharedCheck_3551_ = !lean_is_exclusive(v_x_3530_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; 
v_unused_3552_ = lean_ctor_get(v_x_3530_, 0);
lean_dec(v_unused_3552_);
v___x_3542_ = v_x_3530_;
v_isShared_3543_ = v_isSharedCheck_3551_;
goto v_resetjp_3541_;
}
else
{
lean_dec(v_x_3530_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3551_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3544_ = lean_box(v_a_3529_);
v___x_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3545_);
v___x_3547_ = v___x_3542_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
return v___x_3549_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_3529_ = stack[0].m_num;
lean_object* v_x_3530_ = stack[1].m_obj;
lean_object* v_res_3553_;
v_res_3553_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_3529_, v_x_3530_);
stack->m_obj
 = v_res_3553_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_3554_, lean_object* v_x_3555_, lean_object* v___y_3556_){
_start:
{
uint8_t v_a_5221__boxed_3557_; lean_object* v_res_3558_; 
v_a_5221__boxed_3557_ = lean_unbox(v_a_3554_);
v_res_3558_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5221__boxed_3557_, v_x_3555_);
return v_res_3558_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_3559_, lean_object* v_interestWaiter_3560_, uint8_t v_closed_3561_, lean_object* v_knownSize_3562_, lean_object* v_pendingIncompleteChunk_3563_, lean_object* v_closeError_3564_, lean_object* v___y_3565_, lean_object* v_chunk_3566_, lean_object* v___f_3567_, lean_object* v_x_3568_){
_start:
{
if (lean_obj_tag(v_x_3568_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3578_; 
lean_dec_ref(v___f_3567_);
lean_dec(v_closeError_3564_);
lean_dec(v_pendingIncompleteChunk_3563_);
lean_dec(v_knownSize_3562_);
lean_dec(v_interestWaiter_3560_);
lean_dec(v_pendingProducer_3559_);
v_a_3570_ = lean_ctor_get(v_x_3568_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_x_3568_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3572_ = v_x_3568_;
v_isShared_3573_ = v_isSharedCheck_3578_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v_x_3568_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3578_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
return v___x_3576_;
}
}
}
else
{
lean_object* v_a_3579_; uint8_t v___x_3580_; 
v_a_3579_ = lean_ctor_get(v_x_3568_, 0);
lean_inc(v_a_3579_);
lean_dec_ref_known(v_x_3568_, 1);
v___x_3580_ = lean_unbox(v_a_3579_);
if (v___x_3580_ == 0)
{
lean_object* v___f_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; lean_object* v___x_3588_; 
lean_dec_ref(v___f_3567_);
lean_inc(v_a_3579_);
v___f_3581_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3581_, 0, v_a_3579_);
v___x_3582_ = lean_box(0);
v___x_3583_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3583_, 0, v_pendingProducer_3559_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
lean_ctor_set(v___x_3583_, 2, v_interestWaiter_3560_);
lean_ctor_set(v___x_3583_, 3, v_knownSize_3562_);
lean_ctor_set(v___x_3583_, 4, v_pendingIncompleteChunk_3563_);
lean_ctor_set(v___x_3583_, 5, v_closeError_3564_);
lean_ctor_set_uint8(v___x_3583_, sizeof(void*)*6, v_closed_3561_);
v___x_3584_ = lean_unsigned_to_nat(0u);
v___x_3585_ = lean_st_ref_swap(v___y_3565_, v___x_3583_);
lean_dec(v___x_3585_);
v___x_3586_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3587_ = lean_unbox(v_a_3579_);
lean_dec(v_a_3579_);
v___x_3588_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3584_, v___x_3587_, v___x_3586_, v___f_3581_);
return v___x_3588_;
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
lean_dec(v_a_3579_);
v___x_3589_ = lean_box(0);
v___x_3590_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_3562_, v_chunk_3566_);
v___x_3591_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3591_, 0, v_pendingProducer_3559_);
lean_ctor_set(v___x_3591_, 1, v___x_3589_);
lean_ctor_set(v___x_3591_, 2, v_interestWaiter_3560_);
lean_ctor_set(v___x_3591_, 3, v___x_3590_);
lean_ctor_set(v___x_3591_, 4, v_pendingIncompleteChunk_3563_);
lean_ctor_set(v___x_3591_, 5, v_closeError_3564_);
lean_ctor_set_uint8(v___x_3591_, sizeof(void*)*6, v_closed_3561_);
v___x_3592_ = lean_unsigned_to_nat(0u);
v___x_3593_ = lean_st_ref_swap(v___y_3565_, v___x_3591_);
lean_dec(v___x_3593_);
v___x_3594_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3595_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3592_, v_closed_3561_, v___x_3594_, v___f_3567_);
return v___x_3595_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_pendingProducer_3559_ = stack[0].m_obj;
lean_object* v_interestWaiter_3560_ = stack[1].m_obj;
uint8_t v_closed_3561_ = stack[2].m_num;
lean_object* v_knownSize_3562_ = stack[3].m_obj;
lean_object* v_pendingIncompleteChunk_3563_ = stack[4].m_obj;
lean_object* v_closeError_3564_ = stack[5].m_obj;
lean_object* v___y_3565_ = stack[6].m_obj;
lean_object* v_chunk_3566_ = stack[7].m_obj;
lean_object* v___f_3567_ = stack[8].m_obj;
lean_object* v_x_3568_ = stack[9].m_obj;
lean_object* v_res_3596_;
v_res_3596_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_3559_, v_interestWaiter_3560_, v_closed_3561_, v_knownSize_3562_, v_pendingIncompleteChunk_3563_, v_closeError_3564_, v___y_3565_, v_chunk_3566_, v___f_3567_, v_x_3568_);
stack->m_obj
 = v_res_3596_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_3597_, lean_object* v_interestWaiter_3598_, lean_object* v_closed_3599_, lean_object* v_knownSize_3600_, lean_object* v_pendingIncompleteChunk_3601_, lean_object* v_closeError_3602_, lean_object* v___y_3603_, lean_object* v_chunk_3604_, lean_object* v___f_3605_, lean_object* v_x_3606_, lean_object* v___y_3607_){
_start:
{
uint8_t v_closed_boxed_3608_; lean_object* v_res_3609_; 
v_closed_boxed_3608_ = lean_unbox(v_closed_3599_);
v_res_3609_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_3597_, v_interestWaiter_3598_, v_closed_boxed_3608_, v_knownSize_3600_, v_pendingIncompleteChunk_3601_, v_closeError_3602_, v___y_3603_, v_chunk_3604_, v___f_3605_, v_x_3606_);
lean_dec_ref(v_chunk_3604_);
lean_dec(v___y_3603_);
return v_res_3609_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v___y_3628_, lean_object* v_chunk_3629_, lean_object* v_a_3630_, lean_object* v___f_3631_, lean_object* v_x_3632_){
_start:
{
if (lean_obj_tag(v_x_3632_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v___f_3631_);
lean_dec(v_a_3630_);
lean_dec_ref(v_chunk_3629_);
v_a_3634_ = lean_ctor_get(v_x_3632_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_x_3632_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3636_ = v_x_3632_;
v_isShared_3637_ = v_isSharedCheck_3642_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v_x_3632_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3642_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
return v___x_3640_;
}
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3696_; 
v_a_3643_ = lean_ctor_get(v_x_3632_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_x_3632_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3645_ = v_x_3632_;
v_isShared_3646_ = v_isSharedCheck_3696_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v_x_3632_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3696_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
uint8_t v_closed_3647_; 
v_closed_3647_ = lean_ctor_get_uint8(v_a_3643_, sizeof(void*)*6);
if (v_closed_3647_ == 0)
{
lean_object* v_pendingConsumer_3648_; 
v_pendingConsumer_3648_ = lean_ctor_get(v_a_3643_, 1);
lean_inc(v_pendingConsumer_3648_);
if (lean_obj_tag(v_pendingConsumer_3648_) == 1)
{
lean_object* v_pendingProducer_3649_; lean_object* v_interestWaiter_3650_; lean_object* v_knownSize_3651_; lean_object* v_pendingIncompleteChunk_3652_; lean_object* v_closeError_3653_; lean_object* v_val_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3673_; 
lean_dec_ref(v___f_3631_);
lean_dec(v_a_3630_);
v_pendingProducer_3649_ = lean_ctor_get(v_a_3643_, 0);
lean_inc(v_pendingProducer_3649_);
v_interestWaiter_3650_ = lean_ctor_get(v_a_3643_, 2);
lean_inc(v_interestWaiter_3650_);
v_knownSize_3651_ = lean_ctor_get(v_a_3643_, 3);
lean_inc(v_knownSize_3651_);
v_pendingIncompleteChunk_3652_ = lean_ctor_get(v_a_3643_, 4);
lean_inc(v_pendingIncompleteChunk_3652_);
v_closeError_3653_ = lean_ctor_get(v_a_3643_, 5);
lean_inc(v_closeError_3653_);
lean_dec(v_a_3643_);
v_val_3654_ = lean_ctor_get(v_pendingConsumer_3648_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_pendingConsumer_3648_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3656_ = v_pendingConsumer_3648_;
v_isShared_3657_ = v_isSharedCheck_3673_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_val_3654_);
lean_dec(v_pendingConsumer_3648_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3673_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___f_3658_; lean_object* v___x_3659_; lean_object* v___f_3660_; lean_object* v___x_3662_; 
v___f_3658_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_3659_ = lean_box(v_closed_3647_);
lean_inc_ref(v_chunk_3629_);
lean_inc(v___y_3628_);
v___f_3660_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 11, 9);
lean_closure_set(v___f_3660_, 0, v_pendingProducer_3649_);
lean_closure_set(v___f_3660_, 1, v_interestWaiter_3650_);
lean_closure_set(v___f_3660_, 2, v___x_3659_);
lean_closure_set(v___f_3660_, 3, v_knownSize_3651_);
lean_closure_set(v___f_3660_, 4, v_pendingIncompleteChunk_3652_);
lean_closure_set(v___f_3660_, 5, v_closeError_3653_);
lean_closure_set(v___f_3660_, 6, v___y_3628_);
lean_closure_set(v___f_3660_, 7, v_chunk_3629_);
lean_closure_set(v___f_3660_, 8, v___f_3658_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v_chunk_3629_);
v___x_3662_ = v___x_3656_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_chunk_3629_);
v___x_3662_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3662_);
v___x_3664_ = v___x_3645_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; uint8_t v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3665_ = lean_unsigned_to_nat(0u);
v___x_3666_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_3654_, v___x_3664_);
lean_dec(v_val_3654_);
v___x_3667_ = lean_box(v___x_3666_);
v___x_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
v___x_3670_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3665_, v_closed_3647_, v___x_3669_, v___f_3660_);
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_pendingProducer_3674_; 
lean_del_object(v___x_3645_);
v_pendingProducer_3674_ = lean_ctor_get(v_a_3643_, 0);
if (lean_obj_tag(v_pendingProducer_3674_) == 0)
{
lean_object* v_interestWaiter_3675_; lean_object* v_knownSize_3676_; lean_object* v_pendingIncompleteChunk_3677_; lean_object* v_closeError_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3691_; 
v_interestWaiter_3675_ = lean_ctor_get(v_a_3643_, 2);
v_knownSize_3676_ = lean_ctor_get(v_a_3643_, 3);
v_pendingIncompleteChunk_3677_ = lean_ctor_get(v_a_3643_, 4);
v_closeError_3678_ = lean_ctor_get(v_a_3643_, 5);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_a_3643_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; lean_object* v_unused_3693_; 
v_unused_3692_ = lean_ctor_get(v_a_3643_, 1);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_a_3643_, 0);
lean_dec(v_unused_3693_);
v___x_3680_ = v_a_3643_;
v_isShared_3681_ = v_isSharedCheck_3691_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_closeError_3678_);
lean_inc(v_pendingIncompleteChunk_3677_);
lean_inc(v_knownSize_3676_);
lean_inc(v_interestWaiter_3675_);
lean_dec(v_a_3643_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3691_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v_chunk_3629_);
lean_ctor_set(v___x_3682_, 1, v_a_3630_);
v___x_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3683_);
v___x_3685_ = v___x_3680_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_pendingConsumer_3648_);
lean_ctor_set(v_reuseFailAlloc_3690_, 2, v_interestWaiter_3675_);
lean_ctor_set(v_reuseFailAlloc_3690_, 3, v_knownSize_3676_);
lean_ctor_set(v_reuseFailAlloc_3690_, 4, v_pendingIncompleteChunk_3677_);
lean_ctor_set(v_reuseFailAlloc_3690_, 5, v_closeError_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, sizeof(void*)*6, v_closed_3647_);
v___x_3685_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3686_ = lean_unsigned_to_nat(0u);
v___x_3687_ = lean_st_ref_swap(v___y_3628_, v___x_3685_);
lean_dec(v___x_3687_);
v___x_3688_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3689_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3686_, v_closed_3647_, v___x_3688_, v___f_3631_);
return v___x_3689_;
}
}
}
else
{
lean_object* v___x_3694_; 
lean_dec(v_pendingConsumer_3648_);
lean_dec(v_a_3643_);
lean_dec_ref(v___f_3631_);
lean_dec(v_a_3630_);
lean_dec_ref(v_chunk_3629_);
v___x_3694_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_3694_;
}
}
}
else
{
lean_object* v___x_3695_; 
lean_del_object(v___x_3645_);
lean_dec(v_a_3643_);
lean_dec_ref(v___f_3631_);
lean_dec(v_a_3630_);
lean_dec_ref(v_chunk_3629_);
v___x_3695_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_3695_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3628_ = stack[0].m_obj;
lean_object* v_chunk_3629_ = stack[1].m_obj;
lean_object* v_a_3630_ = stack[2].m_obj;
lean_object* v___f_3631_ = stack[3].m_obj;
lean_object* v_x_3632_ = stack[4].m_obj;
lean_object* v_res_3697_;
v_res_3697_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v___y_3628_, v_chunk_3629_, v_a_3630_, v___f_3631_, v_x_3632_);
stack->m_obj
 = v_res_3697_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v___y_3698_, lean_object* v_chunk_3699_, lean_object* v_a_3700_, lean_object* v___f_3701_, lean_object* v_x_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v___y_3698_, v_chunk_3699_, v_a_3700_, v___f_3701_, v_x_3702_);
lean_dec(v___y_3698_);
return v_res_3704_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_3705_, lean_object* v___f_3706_, lean_object* v_x_3707_){
_start:
{
if (lean_obj_tag(v_x_3707_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3717_; 
lean_dec_ref(v___f_3706_);
v_a_3709_ = lean_ctor_get(v_x_3707_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_x_3707_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3711_ = v_x_3707_;
v_isShared_3712_ = v_isSharedCheck_3717_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v_x_3707_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3717_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
return v___x_3715_;
}
}
}
else
{
lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3729_; 
v_isSharedCheck_3729_ = !lean_is_exclusive(v_x_3707_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v_x_3707_, 0);
lean_dec(v_unused_3730_);
v___x_3719_ = v_x_3707_;
v_isShared_3720_ = v_isSharedCheck_3729_;
goto v_resetjp_3718_;
}
else
{
lean_dec(v_x_3707_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3729_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; uint8_t v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3725_; 
v___x_3721_ = lean_unsigned_to_nat(0u);
v___x_3722_ = 0;
v___x_3723_ = lean_st_ref_get(v___y_3705_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v___x_3723_);
v___x_3725_ = v___x_3719_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
v___x_3727_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3721_, v___x_3722_, v___x_3726_, v___f_3706_);
return v___x_3727_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3705_ = stack[0].m_obj;
lean_object* v___f_3706_ = stack[1].m_obj;
lean_object* v_x_3707_ = stack[2].m_obj;
lean_object* v_res_3731_;
v_res_3731_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_3705_, v___f_3706_, v_x_3707_);
stack->m_obj
 = v_res_3731_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_3732_, lean_object* v___f_3733_, lean_object* v_x_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_3732_, v___f_3733_, v_x_3734_);
lean_dec(v___y_3732_);
return v_res_3736_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_3737_, lean_object* v_a_3738_, lean_object* v___f_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v___f_3742_; lean_object* v___f_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
lean_inc_n(v___y_3740_, 2);
v___f_3742_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_3742_, 0, v___y_3740_);
lean_closure_set(v___f_3742_, 1, v_chunk_3737_);
lean_closure_set(v___f_3742_, 2, v_a_3738_);
lean_closure_set(v___f_3742_, 3, v___f_3739_);
v___f_3743_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_3743_, 0, v___y_3740_);
lean_closure_set(v___f_3743_, 1, v___f_3742_);
v___x_3744_ = lean_unsigned_to_nat(0u);
v___x_3745_ = 0;
v___x_3746_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3740_);
v___x_3747_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3744_, v___x_3745_, v___x_3746_, v___f_3743_);
return v___x_3747_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_chunk_3737_ = stack[0].m_obj;
lean_object* v_a_3738_ = stack[1].m_obj;
lean_object* v___f_3739_ = stack[2].m_obj;
lean_object* v___y_3740_ = stack[3].m_obj;
lean_object* v_res_3748_;
v_res_3748_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_3737_, v_a_3738_, v___f_3739_, v___y_3740_);
stack->m_obj
 = v_res_3748_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_3749_, lean_object* v_a_3750_, lean_object* v___f_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_3749_, v_a_3750_, v___f_3751_, v___y_3752_);
lean_dec(v___y_3752_);
return v_res_3754_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_3760_, lean_object* v___f_3761_, lean_object* v___f_3762_, lean_object* v_stream_3763_, lean_object* v_chunk_3764_, lean_object* v___f_3765_, lean_object* v_x_3766_){
_start:
{
if (lean_obj_tag(v_x_3766_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3776_; 
lean_dec_ref(v___f_3765_);
lean_dec_ref(v_chunk_3764_);
lean_dec_ref(v_stream_3763_);
lean_dec_ref(v___f_3762_);
lean_dec_ref(v___f_3761_);
v_a_3768_ = lean_ctor_get(v_x_3766_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_x_3766_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3770_ = v_x_3766_;
v_isShared_3771_ = v_isSharedCheck_3776_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v_x_3766_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3776_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
return v___x_3774_;
}
}
}
else
{
lean_object* v_a_3777_; 
v_a_3777_ = lean_ctor_get(v_x_3766_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v_x_3766_, 1);
if (lean_obj_tag(v_a_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v___f_3765_);
lean_dec_ref(v_chunk_3764_);
lean_dec_ref(v_stream_3763_);
lean_dec_ref(v___f_3762_);
lean_dec_ref(v___f_3761_);
v_a_3778_ = lean_ctor_get(v_a_3777_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_a_3777_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3780_ = v_a_3777_;
v_isShared_3781_ = v_isSharedCheck_3786_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v_a_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3786_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
return v___x_3784_;
}
}
}
else
{
lean_object* v_a_3787_; 
v_a_3787_ = lean_ctor_get(v_a_3777_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v_a_3777_, 1);
if (lean_obj_tag(v_a_3787_) == 0)
{
lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
lean_dec_ref(v___f_3765_);
lean_dec_ref(v_chunk_3764_);
lean_dec_ref(v_stream_3763_);
v___x_3788_ = lean_io_promise_result_opt(v_a_3760_);
v___x_3789_ = lean_unsigned_to_nat(0u);
v___x_3790_ = 0;
v___x_3791_ = lean_task_map(v___f_3761_, v___x_3788_, v___x_3789_, v___x_3790_);
v___x_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
v___x_3793_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3789_, v___x_3790_, v___x_3792_, v___f_3762_);
return v___x_3793_;
}
else
{
lean_object* v_val_3794_; uint8_t v___x_3795_; 
lean_dec_ref(v___f_3762_);
lean_dec_ref(v___f_3761_);
v_val_3794_ = lean_ctor_get(v_a_3787_, 0);
lean_inc(v_val_3794_);
lean_dec_ref_known(v_a_3787_, 1);
v___x_3795_ = lean_unbox(v_val_3794_);
lean_dec(v_val_3794_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; 
lean_dec_ref(v___f_3765_);
v___x_3796_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3763_, v_chunk_3764_);
return v___x_3796_;
}
else
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_dec_ref(v_chunk_3764_);
lean_dec_ref(v_stream_3763_);
v___x_3797_ = lean_box(0);
v___x_3798_ = lean_apply_2(v___f_3765_, v___x_3797_, lean_box(0));
return v___x_3798_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3760_ = stack[0].m_obj;
lean_object* v___f_3761_ = stack[1].m_obj;
lean_object* v___f_3762_ = stack[2].m_obj;
lean_object* v_stream_3763_ = stack[3].m_obj;
lean_object* v_chunk_3764_ = stack[4].m_obj;
lean_object* v___f_3765_ = stack[5].m_obj;
lean_object* v_x_3766_ = stack[6].m_obj;
lean_object* v_res_3799_;
v_res_3799_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_3760_, v___f_3761_, v___f_3762_, v_stream_3763_, v_chunk_3764_, v___f_3765_, v_x_3766_);
stack->m_obj
 = v_res_3799_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_3800_, lean_object* v___f_3801_, lean_object* v___f_3802_, lean_object* v_stream_3803_, lean_object* v_chunk_3804_, lean_object* v___f_3805_, lean_object* v_x_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_3800_, v___f_3801_, v___f_3802_, v_stream_3803_, v_chunk_3804_, v___f_3805_, v_x_3806_);
lean_dec(v_a_3800_);
return v_res_3808_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_3809_, lean_object* v___f_3810_, lean_object* v___f_3811_, lean_object* v___f_3812_, lean_object* v_stream_3813_, lean_object* v___f_3814_, lean_object* v_x_3815_){
_start:
{
if (lean_obj_tag(v_x_3815_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v___f_3814_);
lean_dec_ref(v_stream_3813_);
lean_dec_ref(v___f_3812_);
lean_dec_ref(v___f_3811_);
lean_dec_ref(v___f_3810_);
lean_dec_ref(v_chunk_3809_);
v_a_3817_ = lean_ctor_get(v_x_3815_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_x_3815_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3819_ = v_x_3815_;
v_isShared_3820_ = v_isSharedCheck_3825_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v_x_3815_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3825_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3823_; 
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
return v___x_3823_;
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___f_3827_; lean_object* v___f_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_a_3826_ = lean_ctor_get(v_x_3815_, 0);
lean_inc_n(v_a_3826_, 2);
lean_dec_ref_known(v_x_3815_, 1);
lean_inc_ref(v_chunk_3809_);
v___f_3827_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_3827_, 0, v_chunk_3809_);
lean_closure_set(v___f_3827_, 1, v_a_3826_);
lean_closure_set(v___f_3827_, 2, v___f_3810_);
lean_inc_ref(v_stream_3813_);
v___f_3828_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3828_, 0, v_a_3826_);
lean_closure_set(v___f_3828_, 1, v___f_3811_);
lean_closure_set(v___f_3828_, 2, v___f_3812_);
lean_closure_set(v___f_3828_, 3, v_stream_3813_);
lean_closure_set(v___f_3828_, 4, v_chunk_3809_);
lean_closure_set(v___f_3828_, 5, v___f_3814_);
v___x_3829_ = lean_unsigned_to_nat(0u);
v___x_3830_ = 0;
v___x_3831_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3813_, v___f_3827_);
v___x_3832_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3829_, v___x_3830_, v___x_3831_, v___f_3828_);
return v___x_3832_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_chunk_3809_ = stack[0].m_obj;
lean_object* v___f_3810_ = stack[1].m_obj;
lean_object* v___f_3811_ = stack[2].m_obj;
lean_object* v___f_3812_ = stack[3].m_obj;
lean_object* v_stream_3813_ = stack[4].m_obj;
lean_object* v___f_3814_ = stack[5].m_obj;
lean_object* v_x_3815_ = stack[6].m_obj;
lean_object* v_res_3833_;
v_res_3833_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_3809_, v___f_3810_, v___f_3811_, v___f_3812_, v_stream_3813_, v___f_3814_, v_x_3815_);
stack->m_obj
 = v_res_3833_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_3834_, lean_object* v___f_3835_, lean_object* v___f_3836_, lean_object* v___f_3837_, lean_object* v_stream_3838_, lean_object* v___f_3839_, lean_object* v_x_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_3834_, v___f_3835_, v___f_3836_, v___f_3837_, v_stream_3838_, v___f_3839_, v_x_3840_);
return v_res_3842_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_3843_, lean_object* v_chunk_3844_){
_start:
{
lean_object* v___f_3846_; lean_object* v___f_3847_; lean_object* v___f_3848_; lean_object* v___f_3849_; lean_object* v___f_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___f_3846_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_3847_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_3848_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_3849_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_3850_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_3850_, 0, v_chunk_3844_);
lean_closure_set(v___f_3850_, 1, v___f_3846_);
lean_closure_set(v___f_3850_, 2, v___f_3849_);
lean_closure_set(v___f_3850_, 3, v___f_3848_);
lean_closure_set(v___f_3850_, 4, v_stream_3843_);
lean_closure_set(v___f_3850_, 5, v___f_3847_);
v___x_3851_ = lean_unsigned_to_nat(0u);
v___x_3852_ = 0;
v___x_3853_ = lean_io_promise_new();
v___x_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
v___x_3856_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3851_, v___x_3852_, v___x_3855_, v___f_3850_);
return v___x_3856_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_3843_ = stack[0].m_obj;
lean_object* v_chunk_3844_ = stack[1].m_obj;
lean_object* v_res_3857_;
v_res_3857_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3843_, v_chunk_3844_);
stack->m_obj
 = v_res_3857_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_3858_, lean_object* v_chunk_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3858_, v_chunk_3859_);
return v_res_3861_;
}
}
lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_3862_, lean_object* v_x_3863_){
_start:
{
if (lean_obj_tag(v_x_3863_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3873_; 
lean_dec_ref(v_stream_3862_);
v_a_3865_ = lean_ctor_get(v_x_3863_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_x_3863_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3867_ = v_x_3863_;
v_isShared_3868_ = v_isSharedCheck_3873_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v_x_3863_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3873_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
return v___x_3871_;
}
}
}
else
{
lean_object* v_a_3874_; 
v_a_3874_ = lean_ctor_get(v_x_3863_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v_x_3863_, 1);
if (lean_obj_tag(v_a_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3883_; 
lean_dec_ref(v_stream_3862_);
v_a_3875_ = lean_ctor_get(v_a_3874_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_a_3874_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3877_ = v_a_3874_;
v_isShared_3878_ = v_isSharedCheck_3883_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v_a_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3883_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
return v___x_3881_;
}
}
}
else
{
lean_object* v_a_3884_; 
v_a_3884_ = lean_ctor_get(v_a_3874_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v_a_3874_, 1);
if (lean_obj_tag(v_a_3884_) == 0)
{
lean_object* v___x_3885_; 
lean_dec_ref(v_stream_3862_);
v___x_3885_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3885_;
}
else
{
lean_object* v_val_3886_; uint8_t v___y_3888_; lean_object* v_data_3891_; lean_object* v_extensions_3892_; uint8_t v___x_3893_; 
v_val_3886_ = lean_ctor_get(v_a_3884_, 0);
lean_inc(v_val_3886_);
lean_dec_ref_known(v_a_3884_, 1);
v_data_3891_ = lean_ctor_get(v_val_3886_, 0);
v_extensions_3892_ = lean_ctor_get(v_val_3886_, 1);
v___x_3893_ = l_ByteArray_isEmpty(v_data_3891_);
if (v___x_3893_ == 0)
{
v___y_3888_ = v___x_3893_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; 
v___x_3894_ = lean_array_get_size(v_extensions_3892_);
v___x_3895_ = lean_unsigned_to_nat(0u);
v___x_3896_ = lean_nat_dec_eq(v___x_3894_, v___x_3895_);
v___y_3888_ = v___x_3896_;
goto v___jp_3887_;
}
v___jp_3887_:
{
if (v___y_3888_ == 0)
{
lean_object* v___x_3889_; 
v___x_3889_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3862_, v_val_3886_);
return v___x_3889_;
}
else
{
lean_object* v___x_3890_; 
lean_dec(v_val_3886_);
lean_dec_ref(v_stream_3862_);
v___x_3890_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3890_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_send___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_3862_ = stack[0].m_obj;
lean_object* v_x_3863_ = stack[1].m_obj;
lean_object* v_res_3897_;
v_res_3897_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_3862_, v_x_3863_);
stack->m_obj
 = v_res_3897_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object* v_stream_3898_, lean_object* v_x_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_3898_, v_x_3899_);
return v_res_3901_;
}
}
lean_object* l_Std_Http_Body_Stream_send(lean_object* v_stream_3902_, lean_object* v_chunk_3903_, uint8_t v_incomplete_3904_){
_start:
{
lean_object* v___f_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
lean_inc_ref(v_stream_3902_);
v___f_3906_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3906_, 0, v_stream_3902_);
v___x_3907_ = lean_unsigned_to_nat(0u);
v___x_3908_ = 0;
v___x_3909_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3902_, v_chunk_3903_, v_incomplete_3904_);
v___x_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
v___x_3912_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3907_, v___x_3908_, v___x_3911_, v___f_3906_);
return v___x_3912_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_3902_ = stack[0].m_obj;
lean_object* v_chunk_3903_ = stack[1].m_obj;
uint8_t v_incomplete_3904_ = stack[2].m_num;
lean_object* v_res_3913_;
v_res_3913_ = l_Std_Http_Body_Stream_send(v_stream_3902_, v_chunk_3903_, v_incomplete_3904_);
stack->m_obj
 = v_res_3913_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object* v_stream_3914_, lean_object* v_chunk_3915_, lean_object* v_incomplete_3916_, lean_object* v_a_3917_){
_start:
{
uint8_t v_incomplete_boxed_3918_; lean_object* v_res_3919_; 
v_incomplete_boxed_3918_ = lean_unbox(v_incomplete_3916_);
v_res_3919_ = l_Std_Http_Body_Stream_send(v_stream_3914_, v_chunk_3915_, v_incomplete_boxed_3918_);
return v_res_3919_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object* v_x_3920_){
_start:
{
uint8_t v___y_3923_; 
if (lean_obj_tag(v_x_3920_) == 0)
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3935_; 
v_a_3927_ = lean_ctor_get(v_x_3920_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_x_3920_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3929_ = v_x_3920_;
v_isShared_3930_ = v_isSharedCheck_3935_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v_x_3920_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3935_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3933_; 
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
return v___x_3933_;
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v_pendingConsumer_3937_; 
v_a_3936_ = lean_ctor_get(v_x_3920_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v_x_3920_, 1);
v_pendingConsumer_3937_ = lean_ctor_get(v_a_3936_, 1);
lean_inc(v_pendingConsumer_3937_);
lean_dec(v_a_3936_);
if (lean_obj_tag(v_pendingConsumer_3937_) == 0)
{
uint8_t v___x_3938_; 
v___x_3938_ = 0;
v___y_3923_ = v___x_3938_;
goto v___jp_3922_;
}
else
{
uint8_t v___x_3939_; 
lean_dec_ref_known(v_pendingConsumer_3937_, 1);
v___x_3939_ = 1;
v___y_3923_ = v___x_3939_;
goto v___jp_3922_;
}
}
v___jp_3922_:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3924_ = lean_box(v___y_3923_);
v___x_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
v___x_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
return v___x_3926_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3920_ = stack[0].m_obj;
lean_object* v_res_3940_;
v_res_3940_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_3920_);
stack->m_obj
 = v_res_3940_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object* v_x_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_3941_);
return v_res_3943_;
}
}
lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object* v_a_3945_){
_start:
{
lean_object* v___f_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___f_3947_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_3948_ = lean_unsigned_to_nat(0u);
v___x_3949_ = 0;
v___x_3950_ = lean_st_ref_get(v_a_3945_);
v___x_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
v___x_3953_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3948_, v___x_3949_, v___x_3952_, v___f_3947_);
return v___x_3953_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3945_ = stack[0].m_obj;
lean_object* v_res_3954_;
v_res_3954_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_3945_);
stack->m_obj
 = v_res_3954_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object* v_a_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_3955_);
lean_dec(v_a_3955_);
return v_res_3957_;
}
}
lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object* v___y_3958_, lean_object* v_x_3959_){
_start:
{
if (lean_obj_tag(v_x_3959_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3969_; 
v_a_3961_ = lean_ctor_get(v_x_3959_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v_x_3959_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3963_ = v_x_3959_;
v_isShared_3964_ = v_isSharedCheck_3969_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v_x_3959_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3969_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3961_);
v___x_3966_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
return v___x_3967_;
}
}
}
else
{
lean_object* v___x_3970_; 
lean_dec_ref_known(v_x_3959_, 1);
v___x_3970_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_3958_);
return v___x_3970_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_hasInterest___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3958_ = stack[0].m_obj;
lean_object* v_x_3959_ = stack[1].m_obj;
lean_object* v_res_3971_;
v_res_3971_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_3958_, v_x_3959_);
stack->m_obj
 = v_res_3971_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object* v___y_3972_, lean_object* v_x_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_3972_, v_x_3973_);
lean_dec(v___y_3972_);
return v_res_3975_;
}
}
lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object* v___y_3976_){
_start:
{
lean_object* v___f_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_inc(v___y_3976_);
v___f_3978_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3978_, 0, v___y_3976_);
v___x_3979_ = lean_unsigned_to_nat(0u);
v___x_3980_ = 0;
v___x_3981_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3976_);
v___x_3982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3979_, v___x_3980_, v___x_3981_, v___f_3978_);
return v___x_3982_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_hasInterest___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3976_ = stack[0].m_obj;
lean_object* v_res_3983_;
v_res_3983_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_3976_);
stack->m_obj
 = v_res_3983_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_3984_);
lean_dec(v___y_3984_);
return v_res_3986_;
}
}
lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object* v_stream_3988_){
_start:
{
lean_object* v___f_3990_; lean_object* v___x_3991_; 
v___f_3990_ = ((lean_object*)(l_Std_Http_Body_Stream_hasInterest___closed__0));
v___x_3991_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3988_, v___f_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_hasInterest_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_3988_ = stack[0].m_obj;
lean_object* v_res_3992_;
v_res_3992_ = l_Std_Http_Body_Stream_hasInterest(v_stream_3988_);
stack->m_obj
 = v_res_3992_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object* v_stream_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Std_Http_Body_Stream_hasInterest(v_stream_3993_);
return v_res_3995_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object* v_lose_3996_, lean_object* v___y_3997_, uint8_t v___x_3998_, lean_object* v_promise_3999_, lean_object* v_x_4000_){
_start:
{
if (lean_obj_tag(v_x_4000_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v_lose_3996_);
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
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4024_; 
v_a_4011_ = lean_ctor_get(v_x_4000_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v_x_4000_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4013_ = v_x_4000_;
v_isShared_4014_ = v_isSharedCheck_4024_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v_x_4000_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4024_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
uint8_t v___x_4015_; 
v___x_4015_ = lean_unbox(v_a_4011_);
lean_dec(v_a_4011_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; 
lean_del_object(v___x_4013_);
lean_inc(v___y_3997_);
v___x_4016_ = lean_apply_2(v_lose_3996_, v___y_3997_, lean_box(0));
return v___x_4016_;
}
else
{
lean_object* v___x_4017_; lean_object* v___x_4019_; 
lean_dec_ref(v_lose_3996_);
v___x_4017_ = lean_box(v___x_3998_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4017_);
v___x_4019_ = v___x_4013_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4017_);
v___x_4019_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4020_ = lean_io_promise_resolve(v___x_4019_, v_promise_3999_);
v___x_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
return v___x_4022_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lose_3996_ = stack[0].m_obj;
lean_object* v___y_3997_ = stack[1].m_obj;
uint8_t v___x_3998_ = stack[2].m_num;
lean_object* v_promise_3999_ = stack[3].m_obj;
lean_object* v_x_4000_ = stack[4].m_obj;
lean_object* v_res_4025_;
v_res_4025_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_3996_, v___y_3997_, v___x_3998_, v_promise_3999_, v_x_4000_);
stack->m_obj
 = v_res_4025_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object* v_lose_4026_, lean_object* v___y_4027_, lean_object* v___x_4028_, lean_object* v_promise_4029_, lean_object* v_x_4030_, lean_object* v___y_4031_){
_start:
{
uint8_t v___x_4067__boxed_4032_; lean_object* v_res_4033_; 
v___x_4067__boxed_4032_ = lean_unbox(v___x_4028_);
v_res_4033_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_4026_, v___y_4027_, v___x_4067__boxed_4032_, v_promise_4029_, v_x_4030_);
lean_dec(v_promise_4029_);
lean_dec(v___y_4027_);
return v_res_4033_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_4034_, lean_object* v_lose_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v_finished_4038_; lean_object* v_promise_4039_; uint8_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___f_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; uint8_t v___y_4046_; uint8_t v___x_4054_; 
v_finished_4038_ = lean_ctor_get(v_w_4034_, 0);
lean_inc(v_finished_4038_);
v_promise_4039_ = lean_ctor_get(v_w_4034_, 1);
lean_inc(v_promise_4039_);
lean_dec_ref(v_w_4034_);
v___x_4040_ = 0;
v___x_4041_ = lean_box(v___x_4040_);
lean_inc(v___y_4036_);
v___f_4042_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4042_, 0, v_lose_4035_);
lean_closure_set(v___f_4042_, 1, v___y_4036_);
lean_closure_set(v___f_4042_, 2, v___x_4041_);
lean_closure_set(v___f_4042_, 3, v_promise_4039_);
v___x_4043_ = lean_unsigned_to_nat(0u);
v___x_4044_ = lean_st_ref_take(v_finished_4038_);
v___x_4054_ = lean_unbox(v___x_4044_);
lean_dec(v___x_4044_);
if (v___x_4054_ == 0)
{
uint8_t v___x_4055_; 
v___x_4055_ = 1;
v___y_4046_ = v___x_4055_;
goto v___jp_4045_;
}
else
{
v___y_4046_ = v___x_4040_;
goto v___jp_4045_;
}
v___jp_4045_:
{
uint8_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4047_ = 1;
v___x_4048_ = lean_box(v___x_4047_);
v___x_4049_ = lean_st_ref_put(v_finished_4038_, v___x_4048_);
lean_dec(v_finished_4038_);
v___x_4050_ = lean_box(v___y_4046_);
v___x_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
v___x_4053_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4043_, v___x_4040_, v___x_4052_, v___f_4042_);
return v___x_4053_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_4034_ = stack[0].m_obj;
lean_object* v_lose_4035_ = stack[1].m_obj;
lean_object* v___y_4036_ = stack[2].m_obj;
lean_object* v_res_4056_;
v_res_4056_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_4034_, v_lose_4035_, v___y_4036_);
stack->m_obj
 = v_res_4056_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object* v_w_4057_, lean_object* v_lose_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_4057_, v_lose_4058_, v___y_4059_);
lean_dec(v___y_4059_);
return v_res_4061_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object* v_w_4062_, lean_object* v_lose_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_finished_4066_; lean_object* v_promise_4067_; uint8_t v___x_4068_; lean_object* v___x_4069_; lean_object* v___f_4070_; lean_object* v___x_4071_; uint8_t v___x_4072_; lean_object* v___x_4073_; uint8_t v___y_4075_; uint8_t v___x_4082_; 
v_finished_4066_ = lean_ctor_get(v_w_4062_, 0);
lean_inc(v_finished_4066_);
v_promise_4067_ = lean_ctor_get(v_w_4062_, 1);
lean_inc(v_promise_4067_);
lean_dec_ref(v_w_4062_);
v___x_4068_ = 1;
v___x_4069_ = lean_box(v___x_4068_);
lean_inc(v___y_4064_);
v___f_4070_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_4070_, 0, v_lose_4063_);
lean_closure_set(v___f_4070_, 1, v___y_4064_);
lean_closure_set(v___f_4070_, 2, v___x_4069_);
lean_closure_set(v___f_4070_, 3, v_promise_4067_);
v___x_4071_ = lean_unsigned_to_nat(0u);
v___x_4072_ = 0;
v___x_4073_ = lean_st_ref_take(v_finished_4066_);
v___x_4082_ = lean_unbox(v___x_4073_);
lean_dec(v___x_4073_);
if (v___x_4082_ == 0)
{
v___y_4075_ = v___x_4068_;
goto v___jp_4074_;
}
else
{
v___y_4075_ = v___x_4072_;
goto v___jp_4074_;
}
v___jp_4074_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4076_ = lean_box(v___x_4068_);
v___x_4077_ = lean_st_ref_put(v_finished_4066_, v___x_4076_);
lean_dec(v_finished_4066_);
v___x_4078_ = lean_box(v___y_4075_);
v___x_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
v___x_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
v___x_4081_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4071_, v___x_4072_, v___x_4080_, v___f_4070_);
return v___x_4081_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_4062_ = stack[0].m_obj;
lean_object* v_lose_4063_ = stack[1].m_obj;
lean_object* v___y_4064_ = stack[2].m_obj;
lean_object* v_res_4083_;
v_res_4083_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_4062_, v_lose_4063_, v___y_4064_);
stack->m_obj
 = v_res_4083_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_4084_, lean_object* v_lose_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_4084_, v_lose_4085_, v___y_4086_);
lean_dec(v___y_4086_);
return v_res_4088_;
}
}
lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_4105_){
_start:
{
if (lean_obj_tag(v_x_4105_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4115_; 
v_a_4107_ = lean_ctor_get(v_x_4105_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v_x_4105_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4109_ = v_x_4105_;
v_isShared_4110_ = v_isSharedCheck_4115_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v_x_4105_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4115_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
return v___x_4113_;
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v_pendingConsumer_4117_; 
v_a_4116_ = lean_ctor_get(v_x_4105_, 0);
lean_inc(v_a_4116_);
lean_dec_ref_known(v_x_4105_, 1);
v_pendingConsumer_4117_ = lean_ctor_get(v_a_4116_, 1);
if (lean_obj_tag(v_pendingConsumer_4117_) == 0)
{
uint8_t v_closed_4118_; 
v_closed_4118_ = lean_ctor_get_uint8(v_a_4116_, sizeof(void*)*6);
lean_dec(v_a_4116_);
if (v_closed_4118_ == 0)
{
lean_object* v___x_4119_; 
v___x_4119_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_4119_;
}
else
{
lean_object* v___x_4120_; 
v___x_4120_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_4120_;
}
}
else
{
lean_object* v___x_4121_; 
lean_dec(v_a_4116_);
v___x_4121_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_4121_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_interestSelector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4105_ = stack[0].m_obj;
lean_object* v_res_4122_;
v_res_4122_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_4105_);
stack->m_obj
 = v_res_4122_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_4123_);
return v_res_4125_;
}
}
lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_4133_, lean_object* v___y_4134_, lean_object* v_x_4135_){
_start:
{
if (lean_obj_tag(v_x_4135_) == 0)
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v_waiter_4133_);
v_a_4137_ = lean_ctor_get(v_x_4135_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_x_4135_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4139_ = v_x_4135_;
v_isShared_4140_ = v_isSharedCheck_4145_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v_x_4135_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4145_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_object* v___x_4143_; 
v___x_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
return v___x_4143_;
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v_pendingConsumer_4147_; 
v_a_4146_ = lean_ctor_get(v_x_4135_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v_x_4135_, 1);
v_pendingConsumer_4147_ = lean_ctor_get(v_a_4146_, 1);
lean_inc(v_pendingConsumer_4147_);
if (lean_obj_tag(v_pendingConsumer_4147_) == 0)
{
uint8_t v_closed_4148_; 
v_closed_4148_ = lean_ctor_get_uint8(v_a_4146_, sizeof(void*)*6);
if (v_closed_4148_ == 0)
{
lean_object* v_interestWaiter_4149_; 
v_interestWaiter_4149_ = lean_ctor_get(v_a_4146_, 2);
if (lean_obj_tag(v_interestWaiter_4149_) == 0)
{
lean_object* v_pendingProducer_4150_; lean_object* v_knownSize_4151_; lean_object* v_pendingIncompleteChunk_4152_; lean_object* v_closeError_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4163_; 
v_pendingProducer_4150_ = lean_ctor_get(v_a_4146_, 0);
v_knownSize_4151_ = lean_ctor_get(v_a_4146_, 3);
v_pendingIncompleteChunk_4152_ = lean_ctor_get(v_a_4146_, 4);
v_closeError_4153_ = lean_ctor_get(v_a_4146_, 5);
v_isSharedCheck_4163_ = !lean_is_exclusive(v_a_4146_);
if (v_isSharedCheck_4163_ == 0)
{
lean_object* v_unused_4164_; lean_object* v_unused_4165_; 
v_unused_4164_ = lean_ctor_get(v_a_4146_, 2);
lean_dec(v_unused_4164_);
v_unused_4165_ = lean_ctor_get(v_a_4146_, 1);
lean_dec(v_unused_4165_);
v___x_4155_ = v_a_4146_;
v_isShared_4156_ = v_isSharedCheck_4163_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_closeError_4153_);
lean_inc(v_pendingIncompleteChunk_4152_);
lean_inc(v_knownSize_4151_);
lean_inc(v_pendingProducer_4150_);
lean_dec(v_a_4146_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4163_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4157_; lean_object* v___x_4159_; 
v___x_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_waiter_4133_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 2, v___x_4157_);
v___x_4159_ = v___x_4155_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_pendingProducer_4150_);
lean_ctor_set(v_reuseFailAlloc_4162_, 1, v_pendingConsumer_4147_);
lean_ctor_set(v_reuseFailAlloc_4162_, 2, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4162_, 3, v_knownSize_4151_);
lean_ctor_set(v_reuseFailAlloc_4162_, 4, v_pendingIncompleteChunk_4152_);
lean_ctor_set(v_reuseFailAlloc_4162_, 5, v_closeError_4153_);
lean_ctor_set_uint8(v_reuseFailAlloc_4162_, sizeof(void*)*6, v_closed_4148_);
v___x_4159_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4160_ = lean_st_ref_swap(v___y_4134_, v___x_4159_);
lean_dec(v___x_4160_);
v___x_4161_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4161_;
}
}
}
else
{
lean_object* v___x_4166_; 
lean_dec(v_a_4146_);
lean_dec_ref(v_waiter_4133_);
v___x_4166_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_4166_;
}
}
else
{
lean_object* v___f_4167_; lean_object* v___x_4168_; 
lean_dec(v_a_4146_);
v___f_4167_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4168_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_4133_, v___f_4167_, v___y_4134_);
return v___x_4168_;
}
}
else
{
lean_object* v___f_4169_; lean_object* v___x_4170_; 
lean_dec_ref_known(v_pendingConsumer_4147_, 1);
lean_dec(v_a_4146_);
v___f_4169_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_4170_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_4133_, v___f_4169_, v___y_4134_);
return v___x_4170_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_interestSelector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_4133_ = stack[0].m_obj;
lean_object* v___y_4134_ = stack[1].m_obj;
lean_object* v_x_4135_ = stack[2].m_obj;
lean_object* v_res_4171_;
v_res_4171_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_4133_, v___y_4134_, v_x_4135_);
stack->m_obj
 = v_res_4171_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_4172_, lean_object* v___y_4173_, lean_object* v_x_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_4172_, v___y_4173_, v_x_4174_);
lean_dec(v___y_4173_);
return v_res_4176_;
}
}
lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_4177_, lean_object* v___f_4178_, lean_object* v_x_4179_){
_start:
{
if (lean_obj_tag(v_x_4179_) == 0)
{
lean_object* v___x_4181_; 
lean_dec_ref(v___f_4178_);
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v_x_4179_);
return v___x_4181_;
}
else
{
lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4193_; 
v_isSharedCheck_4193_ = !lean_is_exclusive(v_x_4179_);
if (v_isSharedCheck_4193_ == 0)
{
lean_object* v_unused_4194_; 
v_unused_4194_ = lean_ctor_get(v_x_4179_, 0);
lean_dec(v_unused_4194_);
v___x_4183_ = v_x_4179_;
v_isShared_4184_ = v_isSharedCheck_4193_;
goto v_resetjp_4182_;
}
else
{
lean_dec(v_x_4179_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4193_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4185_; uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4189_; 
v___x_4185_ = lean_unsigned_to_nat(0u);
v___x_4186_ = 0;
v___x_4187_ = lean_st_ref_get(v___y_4177_);
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 0, v___x_4187_);
v___x_4189_ = v___x_4183_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
v___x_4191_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4185_, v___x_4186_, v___x_4190_, v___f_4178_);
return v___x_4191_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_interestSelector___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4177_ = stack[0].m_obj;
lean_object* v___f_4178_ = stack[1].m_obj;
lean_object* v_x_4179_ = stack[2].m_obj;
lean_object* v_res_4195_;
v_res_4195_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_4177_, v___f_4178_, v_x_4179_);
stack->m_obj
 = v_res_4195_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_4196_, lean_object* v___f_4197_, lean_object* v_x_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_4196_, v___f_4197_, v_x_4198_);
lean_dec(v___y_4196_);
return v_res_4200_;
}
}
lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v___f_4204_; lean_object* v___f_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
lean_inc_n(v___y_4202_, 2);
v___f_4204_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_4204_, 0, v_waiter_4201_);
lean_closure_set(v___f_4204_, 1, v___y_4202_);
v___f_4205_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4205_, 0, v___y_4202_);
lean_closure_set(v___f_4205_, 1, v___f_4204_);
v___x_4206_ = lean_unsigned_to_nat(0u);
v___x_4207_ = 0;
v___x_4208_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4202_);
v___x_4209_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4206_, v___x_4207_, v___x_4208_, v___f_4205_);
return v___x_4209_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_interestSelector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_4201_ = stack[0].m_obj;
lean_object* v___y_4202_ = stack[1].m_obj;
lean_object* v_res_4210_;
v_res_4210_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_4201_, v___y_4202_);
stack->m_obj
 = v_res_4210_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_4211_, v___y_4212_);
lean_dec(v___y_4212_);
return v_res_4214_;
}
}
lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_4215_, lean_object* v_waiter_4216_){
_start:
{
lean_object* v___f_4218_; lean_object* v___x_4219_; 
v___f_4218_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4218_, 0, v_waiter_4216_);
v___x_4219_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_4215_, v___f_4218_);
return v___x_4219_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_interestSelector___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_4215_ = stack[0].m_obj;
lean_object* v_waiter_4216_ = stack[1].m_obj;
lean_object* v_res_4220_;
v_res_4220_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_4215_, v_waiter_4216_);
stack->m_obj
 = v_res_4220_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_4221_, lean_object* v_waiter_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_4221_, v_waiter_4222_);
return v_res_4224_;
}
}
lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_4225_, lean_object* v___f_4226_, lean_object* v_x_4227_){
_start:
{
if (lean_obj_tag(v_x_4227_) == 0)
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4237_; 
lean_dec_ref(v___f_4226_);
v_a_4229_ = lean_ctor_get(v_x_4227_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_x_4227_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4231_ = v_x_4227_;
v_isShared_4232_ = v_isSharedCheck_4237_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v_x_4227_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4237_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4235_; 
v___x_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4234_);
return v___x_4235_;
}
}
}
else
{
lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4249_; 
v_isSharedCheck_4249_ = !lean_is_exclusive(v_x_4227_);
if (v_isSharedCheck_4249_ == 0)
{
lean_object* v_unused_4250_; 
v_unused_4250_ = lean_ctor_get(v_x_4227_, 0);
lean_dec(v_unused_4250_);
v___x_4239_ = v_x_4227_;
v_isShared_4240_ = v_isSharedCheck_4249_;
goto v_resetjp_4238_;
}
else
{
lean_dec(v_x_4227_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4249_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; uint8_t v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4245_; 
v___x_4241_ = lean_unsigned_to_nat(0u);
v___x_4242_ = 0;
v___x_4243_ = lean_st_ref_get(v___y_4225_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4243_);
v___x_4245_ = v___x_4239_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4243_);
v___x_4245_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
v___x_4247_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4241_, v___x_4242_, v___x_4246_, v___f_4226_);
return v___x_4247_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_interestSelector___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4225_ = stack[0].m_obj;
lean_object* v___f_4226_ = stack[1].m_obj;
lean_object* v_x_4227_ = stack[2].m_obj;
lean_object* v_res_4251_;
v_res_4251_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_4225_, v___f_4226_, v_x_4227_);
stack->m_obj
 = v_res_4251_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_4252_, lean_object* v___f_4253_, lean_object* v_x_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_4252_, v___f_4253_, v_x_4254_);
lean_dec(v___y_4252_);
return v_res_4256_;
}
}
lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___f_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
lean_inc(v___y_4258_);
v___f_4260_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_4260_, 0, v___y_4258_);
lean_closure_set(v___f_4260_, 1, v___f_4257_);
v___x_4261_ = lean_unsigned_to_nat(0u);
v___x_4262_ = 0;
v___x_4263_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4258_);
v___x_4264_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4261_, v___x_4262_, v___x_4263_, v___f_4260_);
return v___x_4264_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Stream_interestSelector___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4257_ = stack[0].m_obj;
lean_object* v___y_4258_ = stack[1].m_obj;
lean_object* v_res_4265_;
v_res_4265_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_4257_, v___y_4258_);
stack->m_obj
 = v_res_4265_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_4266_, v___y_4267_);
lean_dec(v___y_4267_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_4273_){
_start:
{
lean_object* v___f_4274_; lean_object* v___f_4275_; lean_object* v___f_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___f_4274_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_4273_, 2);
v___f_4275_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_4275_, 0, v_stream_4273_);
v___f_4276_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_4277_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4277_, 0, lean_box(0));
lean_closure_set(v___x_4277_, 1, lean_box(0));
lean_closure_set(v___x_4277_, 2, v_stream_4273_);
lean_closure_set(v___x_4277_, 3, v___f_4276_);
v___x_4278_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4278_, 0, lean_box(0));
lean_closure_set(v___x_4278_, 1, lean_box(0));
lean_closure_set(v___x_4278_, 2, v_stream_4273_);
lean_closure_set(v___x_4278_, 3, v___f_4274_);
v___x_4279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___f_4275_);
lean_ctor_set(v___x_4279_, 2, v___x_4278_);
return v___x_4279_;
}
}
lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v_x_4280_, lean_object* v_x_4281_){
_start:
{
if (lean_obj_tag(v_x_4281_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref(v_x_4280_);
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
lean_object* v___x_4292_; 
lean_dec_ref_known(v_x_4281_, 1);
v___x_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4292_, 0, v_x_4280_);
return v___x_4292_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_stream___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4280_ = stack[0].m_obj;
lean_object* v_x_4281_ = stack[1].m_obj;
lean_object* v_res_4293_;
v_res_4293_ = l_Std_Http_Body_stream___lam__0(v_x_4280_, v_x_4281_);
stack->m_obj
 = v_res_4293_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0___boxed(lean_object* v_x_4294_, lean_object* v_x_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Std_Http_Body_stream___lam__0(v_x_4294_, v_x_4295_);
return v_res_4297_;
}
}
lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_a_4298_, lean_object* v_x_4299_){
_start:
{
if (lean_obj_tag(v_x_4299_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4302_; 
v_a_4301_ = lean_ctor_get(v_x_4299_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v_x_4299_, 1);
v___x_4302_ = l_Std_Http_Body_Stream_closeWithError(v_a_4298_, v_a_4301_);
return v___x_4302_;
}
else
{
lean_object* v___x_4303_; 
lean_dec_ref(v_a_4298_);
v___x_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4303_, 0, v_x_4299_);
return v___x_4303_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_stream___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4298_ = stack[0].m_obj;
lean_object* v_x_4299_ = stack[1].m_obj;
lean_object* v_res_4304_;
v_res_4304_ = l_Std_Http_Body_stream___lam__1(v_a_4298_, v_x_4299_);
stack->m_obj
 = v_res_4304_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_a_4305_, lean_object* v_x_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_Std_Http_Body_stream___lam__1(v_a_4305_, v_x_4306_);
return v_res_4308_;
}
}
lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v_a_4309_, lean_object* v_x_4310_){
_start:
{
if (lean_obj_tag(v_x_4310_) == 0)
{
lean_object* v___x_4312_; 
lean_dec_ref(v_a_4309_);
v___x_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4312_, 0, v_x_4310_);
return v___x_4312_;
}
else
{
lean_object* v___x_4313_; 
lean_dec_ref_known(v_x_4310_, 1);
v___x_4313_ = l_Std_Http_Body_Stream_close(v_a_4309_);
return v___x_4313_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_stream___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4309_ = stack[0].m_obj;
lean_object* v_x_4310_ = stack[1].m_obj;
lean_object* v_res_4314_;
v_res_4314_ = l_Std_Http_Body_stream___lam__2(v_a_4309_, v_x_4310_);
stack->m_obj
 = v_res_4314_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v_a_4315_, lean_object* v_x_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_Std_Http_Body_stream___lam__2(v_a_4315_, v_x_4316_);
return v_res_4318_;
}
}
lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_gen_4319_, lean_object* v_a_4320_, lean_object* v___x_4321_, uint8_t v___x_4322_, lean_object* v___f_4323_, lean_object* v___f_4324_){
_start:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4326_ = lean_apply_2(v_gen_4319_, v_a_4320_, lean_box(0));
lean_inc(v___x_4321_);
v___x_4327_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4321_, v___x_4322_, v___x_4326_, v___f_4323_);
v___x_4328_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4321_, v___x_4322_, v___x_4327_, v___f_4324_);
return v___x_4328_;
}
}
LEAN_EXPORT void l_Std_Http_Body_stream___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_gen_4319_ = stack[0].m_obj;
lean_object* v_a_4320_ = stack[1].m_obj;
lean_object* v___x_4321_ = stack[2].m_obj;
uint8_t v___x_4322_ = stack[3].m_num;
lean_object* v___f_4323_ = stack[4].m_obj;
lean_object* v___f_4324_ = stack[5].m_obj;
lean_object* v_res_4329_;
v_res_4329_ = l_Std_Http_Body_stream___lam__3(v_gen_4319_, v_a_4320_, v___x_4321_, v___x_4322_, v___f_4323_, v___f_4324_);
stack->m_obj
 = v_res_4329_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_gen_4330_, lean_object* v_a_4331_, lean_object* v___x_4332_, lean_object* v___x_4333_, lean_object* v___f_4334_, lean_object* v___f_4335_, lean_object* v___y_4336_){
_start:
{
uint8_t v___x_1099__boxed_4337_; lean_object* v_res_4338_; 
v___x_1099__boxed_4337_ = lean_unbox(v___x_4333_);
v_res_4338_ = l_Std_Http_Body_stream___lam__3(v_gen_4330_, v_a_4331_, v___x_4332_, v___x_1099__boxed_4337_, v___f_4334_, v___f_4335_);
return v_res_4338_;
}
}
lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_4339_, lean_object* v_a_4340_, lean_object* v___f_4341_, lean_object* v___f_4342_, lean_object* v___f_4343_, lean_object* v_x_4344_){
_start:
{
if (lean_obj_tag(v_x_4344_) == 0)
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4354_; 
lean_dec_ref(v___f_4343_);
lean_dec_ref(v___f_4342_);
lean_dec_ref(v___f_4341_);
lean_dec_ref(v_a_4340_);
lean_dec_ref(v_gen_4339_);
v_a_4346_ = lean_ctor_get(v_x_4344_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v_x_4344_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4348_ = v_x_4344_;
v_isShared_4349_ = v_isSharedCheck_4354_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v_x_4344_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4354_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
return v___x_4352_;
}
}
}
else
{
lean_object* v___x_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; lean_object* v___f_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
lean_dec_ref_known(v_x_4344_, 1);
v___x_4355_ = lean_unsigned_to_nat(0u);
v___x_4356_ = 0;
v___x_4357_ = lean_box(v___x_4356_);
v___f_4358_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 7, 6);
lean_closure_set(v___f_4358_, 0, v_gen_4339_);
lean_closure_set(v___f_4358_, 1, v_a_4340_);
lean_closure_set(v___f_4358_, 2, v___x_4355_);
lean_closure_set(v___f_4358_, 3, v___x_4357_);
lean_closure_set(v___f_4358_, 4, v___f_4341_);
lean_closure_set(v___f_4358_, 5, v___f_4342_);
v___x_4359_ = lean_io_as_task(v___f_4358_, v___x_4355_);
lean_dec_ref(v___x_4359_);
v___x_4360_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4355_, v___x_4356_, v___x_4360_, v___f_4343_);
return v___x_4361_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_stream___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_gen_4339_ = stack[0].m_obj;
lean_object* v_a_4340_ = stack[1].m_obj;
lean_object* v___f_4341_ = stack[2].m_obj;
lean_object* v___f_4342_ = stack[3].m_obj;
lean_object* v___f_4343_ = stack[4].m_obj;
lean_object* v_x_4344_ = stack[5].m_obj;
lean_object* v_res_4362_;
v_res_4362_ = l_Std_Http_Body_stream___lam__4(v_gen_4339_, v_a_4340_, v___f_4341_, v___f_4342_, v___f_4343_, v_x_4344_);
stack->m_obj
 = v_res_4362_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_4363_, lean_object* v_a_4364_, lean_object* v___f_4365_, lean_object* v___f_4366_, lean_object* v___f_4367_, lean_object* v_x_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Std_Http_Body_stream___lam__4(v_gen_4363_, v_a_4364_, v___f_4365_, v___f_4366_, v___f_4367_, v_x_4368_);
return v_res_4370_;
}
}
lean_object* l_Std_Http_Body_stream___lam__5(lean_object* v___x_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; lean_object* v_pendingProducer_4375_; lean_object* v_pendingConsumer_4376_; lean_object* v_interestWaiter_4377_; uint8_t v_closed_4378_; lean_object* v_pendingIncompleteChunk_4379_; lean_object* v_closeError_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4389_; 
v___x_4374_ = lean_st_ref_take(v___y_4372_);
v_pendingProducer_4375_ = lean_ctor_get(v___x_4374_, 0);
v_pendingConsumer_4376_ = lean_ctor_get(v___x_4374_, 1);
v_interestWaiter_4377_ = lean_ctor_get(v___x_4374_, 2);
v_closed_4378_ = lean_ctor_get_uint8(v___x_4374_, sizeof(void*)*6);
v_pendingIncompleteChunk_4379_ = lean_ctor_get(v___x_4374_, 4);
v_closeError_4380_ = lean_ctor_get(v___x_4374_, 5);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4389_ == 0)
{
lean_object* v_unused_4390_; 
v_unused_4390_ = lean_ctor_get(v___x_4374_, 3);
lean_dec(v_unused_4390_);
v___x_4382_ = v___x_4374_;
v_isShared_4383_ = v_isSharedCheck_4389_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_closeError_4380_);
lean_inc(v_pendingIncompleteChunk_4379_);
lean_inc(v_interestWaiter_4377_);
lean_inc(v_pendingConsumer_4376_);
lean_inc(v_pendingProducer_4375_);
lean_dec(v___x_4374_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4389_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 3, v___x_4371_);
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_pendingProducer_4375_);
lean_ctor_set(v_reuseFailAlloc_4388_, 1, v_pendingConsumer_4376_);
lean_ctor_set(v_reuseFailAlloc_4388_, 2, v_interestWaiter_4377_);
lean_ctor_set(v_reuseFailAlloc_4388_, 3, v___x_4371_);
lean_ctor_set(v_reuseFailAlloc_4388_, 4, v_pendingIncompleteChunk_4379_);
lean_ctor_set(v_reuseFailAlloc_4388_, 5, v_closeError_4380_);
lean_ctor_set_uint8(v_reuseFailAlloc_4388_, sizeof(void*)*6, v_closed_4378_);
v___x_4385_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = lean_st_ref_put(v___y_4372_, v___x_4385_);
v___x_4387_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4387_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_stream___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4371_ = stack[0].m_obj;
lean_object* v___y_4372_ = stack[1].m_obj;
lean_object* v_res_4391_;
v_res_4391_ = l_Std_Http_Body_stream___lam__5(v___x_4371_, v___y_4372_);
stack->m_obj
 = v_res_4391_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object* v___x_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Std_Http_Body_stream___lam__5(v___x_4392_, v___y_4393_);
lean_dec(v___y_4393_);
return v_res_4395_;
}
}
lean_object* l_Std_Http_Body_stream___lam__6(lean_object* v_gen_4400_, lean_object* v_x_4401_){
_start:
{
if (lean_obj_tag(v_x_4401_) == 0)
{
lean_object* v___x_4403_; 
lean_dec_ref(v_gen_4400_);
v___x_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4403_, 0, v_x_4401_);
return v___x_4403_;
}
else
{
lean_object* v_a_4404_; lean_object* v___f_4405_; lean_object* v___f_4406_; lean_object* v___f_4407_; lean_object* v___f_4408_; lean_object* v___f_4409_; lean_object* v___x_4410_; uint8_t v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_a_4404_ = lean_ctor_get(v_x_4401_, 0);
lean_inc_n(v_a_4404_, 4);
v___f_4405_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4405_, 0, v_x_4401_);
v___f_4406_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4406_, 0, v_a_4404_);
v___f_4407_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4407_, 0, v_a_4404_);
v___f_4408_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 7, 5);
lean_closure_set(v___f_4408_, 0, v_gen_4400_);
lean_closure_set(v___f_4408_, 1, v_a_4404_);
lean_closure_set(v___f_4408_, 2, v___f_4407_);
lean_closure_set(v___f_4408_, 3, v___f_4406_);
lean_closure_set(v___f_4408_, 4, v___f_4405_);
v___f_4409_ = ((lean_object*)(l_Std_Http_Body_stream___lam__6___closed__1));
v___x_4410_ = lean_unsigned_to_nat(0u);
v___x_4411_ = 0;
v___x_4412_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4404_, v___f_4409_);
v___x_4413_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4410_, v___x_4411_, v___x_4412_, v___f_4408_);
return v___x_4413_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_stream___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_gen_4400_ = stack[0].m_obj;
lean_object* v_x_4401_ = stack[1].m_obj;
lean_object* v_res_4414_;
v_res_4414_ = l_Std_Http_Body_stream___lam__6(v_gen_4400_, v_x_4401_);
stack->m_obj
 = v_res_4414_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object* v_gen_4415_, lean_object* v_x_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Std_Http_Body_stream___lam__6(v_gen_4415_, v_x_4416_);
return v_res_4418_;
}
}
lean_object* l_Std_Http_Body_stream(lean_object* v_gen_4419_){
_start:
{
lean_object* v___f_4421_; lean_object* v___x_4422_; uint8_t v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___f_4421_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4421_, 0, v_gen_4419_);
v___x_4422_ = lean_unsigned_to_nat(0u);
v___x_4423_ = 0;
v___x_4424_ = l_Std_Http_Body_mkStream();
v___x_4425_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4422_, v___x_4423_, v___x_4424_, v___f_4421_);
return v___x_4425_;
}
}
LEAN_EXPORT void l_Std_Http_Body_stream_0interp(lean_interpreter_value* stack)
{
lean_object* v_gen_4419_ = stack[0].m_obj;
lean_object* v_res_4426_;
v_res_4426_ = l_Std_Http_Body_stream(v_gen_4419_);
stack->m_obj
 = v_res_4426_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_4427_, lean_object* v_a_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Std_Http_Body_stream(v_gen_4427_);
return v_res_4429_;
}
}
lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v___x_4430_, lean_object* v_content_4431_, lean_object* v_s_4432_, lean_object* v_x_4433_){
_start:
{
if (lean_obj_tag(v_x_4433_) == 0)
{
lean_object* v___x_4435_; 
lean_dec_ref(v_s_4432_);
lean_dec_ref(v_content_4431_);
v___x_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4435_, 0, v_x_4433_);
return v___x_4435_;
}
else
{
lean_object* v___x_4436_; uint8_t v___x_4437_; 
lean_dec_ref_known(v_x_4433_, 1);
v___x_4436_ = lean_unsigned_to_nat(0u);
v___x_4437_ = lean_nat_dec_lt(v___x_4436_, v___x_4430_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; 
lean_dec_ref(v_s_4432_);
lean_dec_ref(v_content_4431_);
v___x_4438_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4438_;
}
else
{
lean_object* v___x_4439_; uint8_t v___x_4440_; lean_object* v___x_4441_; 
v___x_4439_ = l_Std_Http_Chunk_ofByteArray(v_content_4431_);
v___x_4440_ = 0;
v___x_4441_ = l_Std_Http_Body_Stream_send(v_s_4432_, v___x_4439_, v___x_4440_);
return v___x_4441_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_fromBytes___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4430_ = stack[0].m_obj;
lean_object* v_content_4431_ = stack[1].m_obj;
lean_object* v_s_4432_ = stack[2].m_obj;
lean_object* v_x_4433_ = stack[3].m_obj;
lean_object* v_res_4442_;
v_res_4442_ = l_Std_Http_Body_fromBytes___lam__0(v___x_4430_, v_content_4431_, v_s_4432_, v_x_4433_);
stack->m_obj
 = v_res_4442_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v___x_4443_, lean_object* v_content_4444_, lean_object* v_s_4445_, lean_object* v_x_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Std_Http_Body_fromBytes___lam__0(v___x_4443_, v_content_4444_, v_s_4445_, v_x_4446_);
lean_dec(v___x_4443_);
return v_res_4448_;
}
}
lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object* v_content_4449_, lean_object* v_s_4450_){
_start:
{
lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___f_4456_; lean_object* v___x_4457_; uint8_t v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4452_ = lean_byte_array_size(v_content_4449_);
lean_inc_ref(v_s_4450_);
v___f_4453_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4453_, 0, v___x_4452_);
lean_closure_set(v___f_4453_, 1, v_content_4449_);
lean_closure_set(v___f_4453_, 2, v_s_4450_);
v___x_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4452_);
v___x_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4454_);
v___f_4456_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4456_, 0, v___x_4455_);
v___x_4457_ = lean_unsigned_to_nat(0u);
v___x_4458_ = 0;
v___x_4459_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_4450_, v___f_4456_);
v___x_4460_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4457_, v___x_4458_, v___x_4459_, v___f_4453_);
return v___x_4460_;
}
}
LEAN_EXPORT void l_Std_Http_Body_fromBytes___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_content_4449_ = stack[0].m_obj;
lean_object* v_s_4450_ = stack[1].m_obj;
lean_object* v_res_4461_;
v_res_4461_ = l_Std_Http_Body_fromBytes___lam__2(v_content_4449_, v_s_4450_);
stack->m_obj
 = v_res_4461_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object* v_content_4462_, lean_object* v_s_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_Std_Http_Body_fromBytes___lam__2(v_content_4462_, v_s_4463_);
return v_res_4465_;
}
}
lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_4466_){
_start:
{
lean_object* v___f_4468_; lean_object* v___x_4469_; 
v___f_4468_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4468_, 0, v_content_4466_);
v___x_4469_ = l_Std_Http_Body_stream(v___f_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT void l_Std_Http_Body_fromBytes_0interp(lean_interpreter_value* stack)
{
lean_object* v_content_4466_ = stack[0].m_obj;
lean_object* v_res_4470_;
v_res_4470_ = l_Std_Http_Body_fromBytes(v_content_4466_);
stack->m_obj
 = v_res_4470_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Std_Http_Body_fromBytes(v_content_4471_);
return v_res_4473_;
}
}
lean_object* l_Std_Http_Body_empty___lam__1(lean_object* v_a_4474_, lean_object* v___f_4475_, lean_object* v_x_4476_){
_start:
{
if (lean_obj_tag(v_x_4476_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4486_; 
lean_dec_ref(v___f_4475_);
lean_dec_ref(v_a_4474_);
v_a_4478_ = lean_ctor_get(v_x_4476_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_x_4476_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4480_ = v_x_4476_;
v_isShared_4481_ = v_isSharedCheck_4486_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v_x_4476_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4486_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
return v___x_4484_;
}
}
}
else
{
lean_object* v___x_4487_; uint8_t v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
lean_dec_ref_known(v_x_4476_, 1);
v___x_4487_ = lean_unsigned_to_nat(0u);
v___x_4488_ = 0;
v___x_4489_ = l_Std_Http_Body_Stream_close(v_a_4474_);
v___x_4490_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4487_, v___x_4488_, v___x_4489_, v___f_4475_);
return v___x_4490_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_empty___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4474_ = stack[0].m_obj;
lean_object* v___f_4475_ = stack[1].m_obj;
lean_object* v_x_4476_ = stack[2].m_obj;
lean_object* v_res_4491_;
v_res_4491_ = l_Std_Http_Body_empty___lam__1(v_a_4474_, v___f_4475_, v_x_4476_);
stack->m_obj
 = v_res_4491_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1___boxed(lean_object* v_a_4492_, lean_object* v___f_4493_, lean_object* v_x_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Std_Http_Body_empty___lam__1(v_a_4492_, v___f_4493_, v_x_4494_);
return v_res_4496_;
}
}
lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_x_4503_){
_start:
{
if (lean_obj_tag(v_x_4503_) == 0)
{
lean_object* v___x_4505_; 
v___x_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4505_, 0, v_x_4503_);
return v___x_4505_;
}
else
{
lean_object* v_a_4506_; lean_object* v___f_4507_; lean_object* v___f_4508_; lean_object* v___x_4509_; lean_object* v___f_4510_; uint8_t v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v_a_4506_ = lean_ctor_get(v_x_4503_, 0);
lean_inc_n(v_a_4506_, 2);
v___f_4507_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4507_, 0, v_x_4503_);
v___f_4508_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4508_, 0, v_a_4506_);
lean_closure_set(v___f_4508_, 1, v___f_4507_);
v___x_4509_ = lean_unsigned_to_nat(0u);
v___f_4510_ = ((lean_object*)(l_Std_Http_Body_empty___lam__2___closed__2));
v___x_4511_ = 0;
v___x_4512_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_4506_, v___f_4510_);
v___x_4513_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4509_, v___x_4511_, v___x_4512_, v___f_4508_);
return v___x_4513_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_empty___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4503_ = stack[0].m_obj;
lean_object* v_res_4514_;
v_res_4514_ = l_Std_Http_Body_empty___lam__2(v_x_4503_);
stack->m_obj
 = v_res_4514_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_x_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Std_Http_Body_empty___lam__2(v_x_4515_);
return v_res_4517_;
}
}
lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___f_4520_; lean_object* v___x_4521_; uint8_t v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___f_4520_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_4521_ = lean_unsigned_to_nat(0u);
v___x_4522_ = 0;
v___x_4523_ = l_Std_Http_Body_mkStream();
v___x_4524_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4521_, v___x_4522_, v___x_4523_, v___f_4520_);
return v___x_4524_;
}
}
LEAN_EXPORT void l_Std_Http_Body_empty_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4525_;
v_res_4525_ = l_Std_Http_Body_empty();
stack->m_obj
 = v_res_4525_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Std_Http_Body_empty();
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_4550_, lean_object* v_f_4551_){
_start:
{
lean_object* v_line_4552_; lean_object* v_body_4553_; lean_object* v_extensions_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4562_; 
v_line_4552_ = lean_ctor_get(v_f_4551_, 0);
v_body_4553_ = lean_ctor_get(v_f_4551_, 1);
v_extensions_4554_ = lean_ctor_get(v_f_4551_, 2);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_f_4551_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4556_ = v_f_4551_;
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_extensions_4554_);
lean_inc(v_body_4553_);
lean_inc(v_line_4552_);
lean_dec(v_f_4551_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4558_; lean_object* v___x_4560_; 
v___x_4558_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4550_, v_body_4553_);
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 1, v___x_4558_);
v___x_4560_ = v___x_4556_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_line_4552_);
lean_ctor_set(v_reuseFailAlloc_4561_, 1, v___x_4558_);
lean_ctor_set(v_reuseFailAlloc_4561_, 2, v_extensions_4554_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_4566_, lean_object* v_x_4567_){
_start:
{
if (lean_obj_tag(v_x_4567_) == 0)
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4577_; 
lean_dec_ref(v___x_4566_);
v_a_4569_ = lean_ctor_get(v_x_4567_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_x_4567_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4571_ = v_x_4567_;
v_isShared_4572_ = v_isSharedCheck_4577_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v_x_4567_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4577_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
lean_object* v___x_4575_; 
v___x_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
return v___x_4575_;
}
}
}
else
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4597_; 
v_a_4578_ = lean_ctor_get(v_x_4567_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v_x_4567_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4580_ = v_x_4567_;
v_isShared_4581_ = v_isSharedCheck_4597_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v_x_4567_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4597_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v_line_4582_; lean_object* v_body_4583_; lean_object* v_extensions_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4596_; 
v_line_4582_ = lean_ctor_get(v_a_4578_, 0);
v_body_4583_ = lean_ctor_get(v_a_4578_, 1);
v_extensions_4584_ = lean_ctor_get(v_a_4578_, 2);
v_isSharedCheck_4596_ = !lean_is_exclusive(v_a_4578_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4586_ = v_a_4578_;
v_isShared_4587_ = v_isSharedCheck_4596_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_extensions_4584_);
lean_inc(v_body_4583_);
lean_inc(v_line_4582_);
lean_dec(v_a_4578_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4596_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4588_; lean_object* v___x_4590_; 
v___x_4588_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_4566_, v_body_4583_);
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 1, v___x_4588_);
v___x_4590_ = v___x_4586_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_line_4582_);
lean_ctor_set(v_reuseFailAlloc_4595_, 1, v___x_4588_);
lean_ctor_set(v_reuseFailAlloc_4595_, 2, v_extensions_4584_);
v___x_4590_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
lean_object* v___x_4592_; 
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 0, v___x_4590_);
v___x_4592_ = v___x_4580_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4590_);
v___x_4592_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4593_; 
v___x_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
return v___x_4593_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4566_ = stack[0].m_obj;
lean_object* v_x_4567_ = stack[1].m_obj;
lean_object* v_res_4598_;
v_res_4598_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_4566_, v_x_4567_);
stack->m_obj
 = v_res_4598_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_4599_, lean_object* v_x_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_4599_, v_x_4600_);
return v_res_4602_;
}
}
lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_4603_, lean_object* v_action_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v___x_4607_; uint8_t v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4607_ = lean_unsigned_to_nat(0u);
v___x_4608_ = 0;
lean_inc_ref(v___y_4605_);
v___x_4609_ = lean_apply_2(v_action_4604_, v___y_4605_, lean_box(0));
v___x_4610_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4607_, v___x_4608_, v___x_4609_, v___f_4603_);
return v___x_4610_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4603_ = stack[0].m_obj;
lean_object* v_action_4604_ = stack[1].m_obj;
lean_object* v___y_4605_ = stack[2].m_obj;
lean_object* v_res_4611_;
v_res_4611_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_4603_, v_action_4604_, v___y_4605_);
stack->m_obj
 = v_res_4611_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_4612_, lean_object* v_action_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_4612_, v_action_4613_, v___y_4614_);
lean_dec_ref(v___y_4614_);
return v_res_4616_;
}
}
lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_4622_, lean_object* v_action_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v___x_4626_; uint8_t v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4626_ = lean_unsigned_to_nat(0u);
v___x_4627_ = 0;
v___x_4628_ = lean_apply_1(v_action_4623_, lean_box(0));
v___x_4629_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4626_, v___x_4627_, v___x_4628_, v___f_4622_);
return v___x_4629_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4622_ = stack[0].m_obj;
lean_object* v_action_4623_ = stack[1].m_obj;
lean_object* v___y_4624_ = stack[2].m_obj;
lean_object* v_res_4630_;
v_res_4630_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_4622_, v_action_4623_, v___y_4624_);
stack->m_obj
 = v_res_4630_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_4631_, lean_object* v_action_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_4631_, v_action_4632_, v___y_4633_);
lean_dec_ref(v___y_4633_);
return v_res_4635_;
}
}
lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_4639_, lean_object* v_x_4640_){
_start:
{
if (lean_obj_tag(v_x_4640_) == 0)
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4650_; 
v_a_4642_ = lean_ctor_get(v_x_4640_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v_x_4640_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4644_ = v_x_4640_;
v_isShared_4645_ = v_isSharedCheck_4650_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v_x_4640_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4650_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4647_; 
if (v_isShared_4645_ == 0)
{
v___x_4647_ = v___x_4644_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4642_);
v___x_4647_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
lean_object* v___x_4648_; 
v___x_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
return v___x_4648_;
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4660_; 
v_a_4651_ = lean_ctor_get(v_x_4640_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v_x_4640_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4653_ = v_x_4640_;
v_isShared_4654_ = v_isSharedCheck_4660_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v_x_4640_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4660_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4655_; lean_object* v___x_4657_; 
v___x_4655_ = l_Std_Http_Request_Builder_body___redArg(v_builder_4639_, v_a_4651_);
if (v_isShared_4654_ == 0)
{
lean_ctor_set(v___x_4653_, 0, v___x_4655_);
v___x_4657_ = v___x_4653_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4655_);
v___x_4657_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4658_; 
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
return v___x_4658_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_stream___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_4639_ = stack[0].m_obj;
lean_object* v_x_4640_ = stack[1].m_obj;
lean_object* v_res_4661_;
v_res_4661_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_4639_, v_x_4640_);
stack->m_obj
 = v_res_4661_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_4662_, lean_object* v_x_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_4662_, v_x_4663_);
lean_dec_ref(v_builder_4662_);
return v_res_4665_;
}
}
lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_4666_, lean_object* v_gen_4667_){
_start:
{
lean_object* v___f_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___f_4669_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4669_, 0, v_builder_4666_);
v___x_4670_ = lean_unsigned_to_nat(0u);
v___x_4671_ = 0;
v___x_4672_ = l_Std_Http_Body_stream(v_gen_4667_);
v___x_4673_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4670_, v___x_4671_, v___x_4672_, v___f_4669_);
return v___x_4673_;
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_stream_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_4666_ = stack[0].m_obj;
lean_object* v_gen_4667_ = stack[1].m_obj;
lean_object* v_res_4674_;
v_res_4674_ = l_Std_Http_Request_Builder_stream(v_builder_4666_, v_gen_4667_);
stack->m_obj
 = v_res_4674_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_4675_, lean_object* v_gen_4676_, lean_object* v_a_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l_Std_Http_Request_Builder_stream(v_builder_4675_, v_gen_4676_);
return v_res_4678_;
}
}
lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_4679_, lean_object* v_x_4680_){
_start:
{
if (lean_obj_tag(v_x_4680_) == 0)
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4690_; 
v_a_4682_ = lean_ctor_get(v_x_4680_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v_x_4680_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4684_ = v_x_4680_;
v_isShared_4685_ = v_isSharedCheck_4690_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v_x_4680_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4690_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
lean_object* v___x_4688_; 
v___x_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4687_);
return v___x_4688_;
}
}
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4700_; 
v_a_4691_ = lean_ctor_get(v_x_4680_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v_x_4680_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4693_ = v_x_4680_;
v_isShared_4694_ = v_isSharedCheck_4700_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v_x_4680_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4700_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4695_; lean_object* v___x_4697_; 
v___x_4695_ = l_Std_Http_Response_Builder_body___redArg(v_builder_4679_, v_a_4691_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 0, v___x_4695_);
v___x_4697_ = v___x_4693_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
lean_object* v___x_4698_; 
v___x_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
return v___x_4698_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Response_Builder_stream___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_4679_ = stack[0].m_obj;
lean_object* v_x_4680_ = stack[1].m_obj;
lean_object* v_res_4701_;
v_res_4701_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_4679_, v_x_4680_);
stack->m_obj
 = v_res_4701_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_4702_, lean_object* v_x_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_4702_, v_x_4703_);
lean_dec_ref(v_builder_4702_);
return v_res_4705_;
}
}
lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_4706_, lean_object* v_gen_4707_){
_start:
{
lean_object* v___f_4709_; lean_object* v___x_4710_; uint8_t v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___f_4709_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4709_, 0, v_builder_4706_);
v___x_4710_ = lean_unsigned_to_nat(0u);
v___x_4711_ = 0;
v___x_4712_ = l_Std_Http_Body_stream(v_gen_4707_);
v___x_4713_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4710_, v___x_4711_, v___x_4712_, v___f_4709_);
return v___x_4713_;
}
}
LEAN_EXPORT void l_Std_Http_Response_Builder_stream_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_4706_ = stack[0].m_obj;
lean_object* v_gen_4707_ = stack[1].m_obj;
lean_object* v_res_4714_;
v_res_4714_ = l_Std_Http_Response_Builder_stream(v_builder_4706_, v_gen_4707_);
stack->m_obj
 = v_res_4714_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_4715_, lean_object* v_gen_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Std_Http_Response_Builder_stream(v_builder_4715_, v_gen_4716_);
return v_res_4718_;
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

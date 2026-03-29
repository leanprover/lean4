// Lean compiler output
// Module: Std.Internal.Http.Data.Body.Stream
// Imports: public import Std.Sync public import Std.Internal.Async public import Std.Internal.Http.Data.Request public import Std.Internal.Http.Data.Response public import Std.Internal.Http.Data.Chunk public import Std.Internal.Http.Data.Body.Basic public import Std.Internal.Http.Data.Body.Any public import Init.Data.ByteArray
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
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonad(lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonadFinally___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody___redArg(lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Http_Chunk_ofByteArray(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0_value;
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
static const lean_string_object l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Http"};
static const lean_object* l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
static const lean_string_object l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Body"};
static const lean_object* l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
static const lean_string_object l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Stream"};
static const lean_object* l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_0),((lean_object*)&l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(62, 74, 245, 198, 196, 207, 141, 173)}};
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_1),((lean_object*)&l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(80, 237, 62, 34, 135, 9, 103, 192)}};
static const lean_ctor_object l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_2),((lean_object*)&l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(35, 197, 133, 196, 74, 182, 137, 145)}};
static const lean_object* l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instImpl_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_ = (const lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instTypeNameStream = (const lean_object*)&l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Internal_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value;
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_mkStream___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 8, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_Body_mkStream___closed__0 = (const lean_object*)&l_Std_Http_Body_mkStream___closed__0_value;
static const lean_closure_object l_Std_Http_Body_mkStream___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_mkStream___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_mkStream___closed__1 = (const lean_object*)&l_Std_Http_Body_mkStream___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream();
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "the promise linked to the consumer was dropped"};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "only one blocked consumer is allowed"};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value)} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_recv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_recv___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_recv___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_recv___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_close___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_close___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_close___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_isClosed___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__0_value;
static lean_once_cell_t l_Std_Http_Body_Stream_isClosed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_isClosed___closed__1;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__2_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__3 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__3_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__3_value),((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__2_value)} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__4 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__4_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_EAsync_instMonadFinally___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__5 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__5_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__6 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__6_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__3_value),((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__6_value)} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__7 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__7_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__7_value),((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__2_value)} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__8 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__8_value;
static const lean_closure_object l_Std_Http_Body_Stream_isClosed___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_get___boxed, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__8_value)} };
static const lean_object* l_Std_Http_Body_Stream_isClosed___closed__9 = (const lean_object*)&l_Std_Http_Body_Stream_isClosed___closed__9_value;
static lean_once_cell_t l_Std_Http_Body_Stream_isClosed___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Stream_isClosed___closed__10;
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_recvSelector___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_recvSelector___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_recvSelector___lam__3___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Stream_recvSelector___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Stream_recvSelector___lam__9___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__9___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_recvSelector___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__9___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_recvSelector___lam__9___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___lam__9___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__11___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_recvSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_recvSelector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_recvSelector___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Stream_recvSelector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_recvSelector___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___closed__1_value;
static const lean_closure_object l_Std_Http_Body_Stream_recvSelector___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_recvSelector___lam__11___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_recvSelector___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Stream_recvSelector___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_recvSelector___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "body exceeded maximum size of "};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " bytes"};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "channel closed"};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "only one blocked producer is allowed"};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1_value)} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_hasInterest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_hasInterest___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_hasInterest___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_hasInterest___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value)}};
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
static const lean_closure_object l_Std_Http_Body_instStream___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_getKnownSize___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instStream___closed__3 = (const lean_object*)&l_Std_Http_Body_instStream___closed__3_value;
static const lean_closure_object l_Std_Http_Body_instStream___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_setKnownSize___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instStream___closed__4 = (const lean_object*)&l_Std_Http_Body_instStream___closed__4_value;
static const lean_ctor_object l_Std_Http_Body_instStream___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value),((lean_object*)&l_Std_Http_Body_instStream___closed__0_value),((lean_object*)&l_Std_Http_Body_instStream___closed__1_value),((lean_object*)&l_Std_Http_Body_instStream___closed__2_value),((lean_object*)&l_Std_Http_Body_instStream___closed__3_value),((lean_object*)&l_Std_Http_Body_instStream___closed__4_value)}};
static const lean_object* l_Std_Http_Body_instStream___closed__5 = (const lean_object*)&l_Std_Http_Body_instStream___closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instStream = (const lean_object*)&l_Std_Http_Body_instStream___closed__5_value;
static const lean_closure_object l_Std_Http_Body_instCoeStreamAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Any_ofBody, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instStream___closed__5_value)} };
static const lean_object* l_Std_Http_Body_instCoeStreamAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeStreamAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeStreamAny = (const lean_object*)&l_Std_Http_Body_instCoeStreamAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeResponseStreamAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeResponseStreamAny___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instStream___closed__5_value)} };
static const lean_object* l_Std_Http_Body_instCoeResponseStreamAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeResponseStreamAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeResponseStreamAny = (const lean_object*)&l_Std_Http_Body_instCoeResponseStreamAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instStream___closed__5_value)} };
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim___redArg(lean_object* v_t_24_, lean_object* v_normal_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_24_, v_normal_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_normal_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_28_, v_normal_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim___redArg(lean_object* v_t_32_, lean_object* v_select_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_32_, v_select_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_select_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(v_t_36_, v_select_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(lean_object* v_x_40_, lean_object* v_w_41_, lean_object* v_lose_42_){
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0___boxed(lean_object* v_x_59_, lean_object* v_w_60_, lean_object* v_lose_61_, lean_object* v___y_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_59_, v_w_60_, v_lose_61_);
lean_dec_ref(v_w_60_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(uint8_t v___x_65_){
_start:
{
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed(lean_object* v___x_67_, lean_object* v___y_68_){
_start:
{
uint8_t v___x_390__boxed_69_; uint8_t v_res_70_; lean_object* v_r_71_; 
v___x_390__boxed_69_ = lean_unbox(v___x_67_);
v_res_70_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(v___x_390__boxed_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(lean_object* v_c_75_, lean_object* v_x_76_){
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
v_lose_82_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_83_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_76_, v_finished_81_, v_lose_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed(lean_object* v_c_84_, lean_object* v_x_85_, lean_object* v_a_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_c_84_, v_x_85_);
lean_dec_ref(v_c_84_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(uint8_t v_x_89_, lean_object* v_w_90_, lean_object* v_lose_91_){
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0___boxed(lean_object* v_x_109_, lean_object* v_w_110_, lean_object* v_lose_111_, lean_object* v___y_112_){
_start:
{
uint8_t v_x_boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_x_boxed_113_ = lean_unbox(v_x_109_);
v_res_114_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_boxed_113_, v_w_110_, v_lose_111_);
lean_dec_ref(v_w_110_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(lean_object* v_waiter_116_, uint8_t v_x_117_){
_start:
{
lean_object* v_lose_119_; uint8_t v___x_120_; 
v_lose_119_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_120_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_117_, v_waiter_116_, v_lose_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed(lean_object* v_waiter_121_, lean_object* v_x_122_, lean_object* v_a_123_){
_start:
{
uint8_t v_x_boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_x_boxed_124_ = lean_unbox(v_x_122_);
v_res_125_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_waiter_121_, v_x_boxed_124_);
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
v___x_173_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_172_, v___x_166_, v___x_171_, v___f_169_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object* v_knownSize_176_, lean_object* v_chunk_177_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object* v_knownSize_198_, lean_object* v_chunk_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_198_, v_chunk_199_);
lean_dec_ref(v_chunk_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object* v_pendingProducer_201_, lean_object* v_pendingConsumer_202_, uint8_t v_closed_203_, lean_object* v_knownSize_204_, lean_object* v_pendingIncompleteChunk_205_, lean_object* v_inst_206_, lean_object* v_interestWaiter_207_, lean_object* v___y_208_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object* v_pendingProducer_212_, lean_object* v_pendingConsumer_213_, lean_object* v_closed_214_, lean_object* v_knownSize_215_, lean_object* v_pendingIncompleteChunk_216_, lean_object* v_inst_217_, lean_object* v_interestWaiter_218_, lean_object* v___y_219_){
_start:
{
uint8_t v_closed_boxed_220_; lean_object* v_res_221_; 
v_closed_boxed_220_ = lean_unbox(v_closed_214_);
v_res_221_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(v_pendingProducer_212_, v_pendingConsumer_213_, v_closed_boxed_220_, v_knownSize_215_, v_pendingIncompleteChunk_216_, v_inst_217_, v_interestWaiter_218_, v___y_219_);
lean_dec(v___y_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object* v___f_222_, lean_object* v___y_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; 
lean_inc(v___y_223_);
v___x_225_ = lean_apply_2(v___f_222_, v_a_224_, v___y_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object* v___f_226_, lean_object* v___y_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(v___f_226_, v___y_227_, v_a_228_);
lean_dec(v___y_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object* v_toApplicative_230_, lean_object* v_interestWaiter_231_, lean_object* v_toBind_232_, lean_object* v___f_233_, lean_object* v___f_234_, uint8_t v_a_235_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object* v_toApplicative_243_, lean_object* v_interestWaiter_244_, lean_object* v_toBind_245_, lean_object* v___f_246_, lean_object* v___f_247_, lean_object* v_a_248_){
_start:
{
uint8_t v_a_boxed_249_; lean_object* v_res_250_; 
v_a_boxed_249_ = lean_unbox(v_a_248_);
v_res_250_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(v_toApplicative_243_, v_interestWaiter_244_, v_toBind_245_, v___f_246_, v___f_247_, v_a_boxed_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object* v_pendingProducer_251_, uint8_t v_closed_252_, lean_object* v_knownSize_253_, lean_object* v_pendingIncompleteChunk_254_, lean_object* v_inst_255_, lean_object* v_interestWaiter_256_, lean_object* v_toApplicative_257_, lean_object* v_toBind_258_, lean_object* v_pendingConsumer_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___f_262_; 
v___x_261_ = lean_box(v_closed_252_);
lean_inc(v_inst_255_);
v___f_262_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed), 8, 6);
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
v___f_264_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
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
v___f_269_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_269_, 0, v___f_262_);
lean_closure_set(v___f_269_, 1, v___y_260_);
lean_inc_ref(v___f_269_);
lean_inc(v_toBind_258_);
v___f_270_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object* v_pendingProducer_274_, lean_object* v_closed_275_, lean_object* v_knownSize_276_, lean_object* v_pendingIncompleteChunk_277_, lean_object* v_inst_278_, lean_object* v_interestWaiter_279_, lean_object* v_toApplicative_280_, lean_object* v_toBind_281_, lean_object* v_pendingConsumer_282_, lean_object* v___y_283_){
_start:
{
uint8_t v_closed_boxed_284_; lean_object* v_res_285_; 
v_closed_boxed_284_ = lean_unbox(v_closed_275_);
v_res_285_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(v_pendingProducer_274_, v_closed_boxed_284_, v_knownSize_276_, v_pendingIncompleteChunk_277_, v_inst_278_, v_interestWaiter_279_, v_toApplicative_280_, v_toBind_281_, v_pendingConsumer_282_, v___y_283_);
lean_dec(v___y_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(lean_object* v___f_286_, lean_object* v___y_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_289_; 
lean_inc(v___y_287_);
v___x_289_ = lean_apply_2(v___f_286_, v_a_288_, v___y_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(lean_object* v___f_290_, lean_object* v___y_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(v___f_290_, v___y_291_, v_a_292_);
lean_dec(v___y_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(lean_object* v___f_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_297_; 
lean_inc(v_a_295_);
v___x_297_ = lean_apply_2(v___f_294_, v_a_296_, v_a_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(lean_object* v___f_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(v___f_298_, v_a_299_, v_a_300_);
lean_dec(v_a_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(lean_object* v_toApplicative_302_, lean_object* v_pendingConsumer_303_, lean_object* v_toBind_304_, lean_object* v___f_305_, lean_object* v___f_306_, uint8_t v_a_307_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(lean_object* v_toApplicative_315_, lean_object* v_pendingConsumer_316_, lean_object* v_toBind_317_, lean_object* v___f_318_, lean_object* v___f_319_, lean_object* v_a_320_){
_start:
{
uint8_t v_a_boxed_321_; lean_object* v_res_322_; 
v_a_boxed_321_ = lean_unbox(v_a_320_);
v_res_322_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(v_toApplicative_315_, v_pendingConsumer_316_, v_toBind_317_, v___f_318_, v___f_319_, v_a_boxed_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(lean_object* v_inst_323_, lean_object* v_toApplicative_324_, lean_object* v_toBind_325_, lean_object* v_a_326_, lean_object* v_a_327_){
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
v___f_335_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed), 10, 8);
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
v___f_345_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_345_, 0, v___f_335_);
lean_closure_set(v___f_345_, 1, v_a_326_);
lean_inc_ref(v___f_345_);
lean_inc(v_toBind_325_);
v___f_346_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed), 6, 5);
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
v___f_339_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_339_, 0, v___f_335_);
lean_closure_set(v___f_339_, 1, v___y_337_);
v___x_340_ = lean_apply_2(v_toPure_338_, lean_box(0), v_pendingConsumer_329_);
v___x_341_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_340_, v___f_339_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(lean_object* v_inst_350_, lean_object* v_toApplicative_351_, lean_object* v_toBind_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(v_inst_350_, v_toApplicative_351_, v_toBind_352_, v_a_353_, v_a_354_);
lean_dec(v_a_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_a_358_){
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
v___f_361_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed), 5, 4);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_365_, v_inst_366_, v_a_367_);
lean_dec(v_a_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(lean_object* v_m_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_370_, v_inst_371_, v_a_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(lean_object* v_m_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(v_m_374_, v_inst_375_, v_inst_376_, v_a_377_);
lean_dec(v_a_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object* v_pendingProducer_379_, lean_object* v_pendingConsumer_380_, uint8_t v_closed_381_, lean_object* v_knownSize_382_, lean_object* v_pendingIncompleteChunk_383_, lean_object* v_a_384_, lean_object* v_inst_385_, lean_object* v_a_386_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object* v_pendingProducer_391_, lean_object* v_pendingConsumer_392_, lean_object* v_closed_393_, lean_object* v_knownSize_394_, lean_object* v_pendingIncompleteChunk_395_, lean_object* v_a_396_, lean_object* v_inst_397_, lean_object* v_a_398_){
_start:
{
uint8_t v_closed_boxed_399_; lean_object* v_res_400_; 
v_closed_boxed_399_ = lean_unbox(v_closed_393_);
v_res_400_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(v_pendingProducer_391_, v_pendingConsumer_392_, v_closed_boxed_399_, v_knownSize_394_, v_pendingIncompleteChunk_395_, v_a_396_, v_inst_397_, v_a_398_);
lean_dec(v_a_396_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(lean_object* v_toApplicative_401_, lean_object* v_a_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_toBind_405_, lean_object* v_a_406_){
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
v___f_417_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_417_, 0, v_pendingProducer_409_);
lean_closure_set(v___f_417_, 1, v_pendingConsumer_410_);
lean_closure_set(v___f_417_, 2, v___x_416_);
lean_closure_set(v___f_417_, 3, v_knownSize_412_);
lean_closure_set(v___f_417_, 4, v_pendingIncompleteChunk_413_);
lean_closure_set(v___f_417_, 5, v_a_402_);
lean_closure_set(v___f_417_, 6, v_inst_403_);
v___x_418_ = 1;
v___x_419_ = lean_box(v___x_418_);
v___x_420_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(lean_object* v_toApplicative_428_, lean_object* v_a_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_toBind_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(v_toApplicative_428_, v_a_429_, v_inst_430_, v_inst_431_, v_toBind_432_, v_a_433_);
lean_dec(v_a_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_a_438_){
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
v___f_441_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_445_, v_inst_446_, v_inst_447_, v_a_448_);
lean_dec(v_a_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(lean_object* v_m_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_451_, v_inst_452_, v_inst_453_, v_a_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(lean_object* v_m_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(v_m_456_, v_inst_457_, v_inst_458_, v_inst_459_, v_a_460_);
lean_dec(v_a_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_462_, lean_object* v_a_463_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(v_toApplicative_472_, v_a_473_);
lean_dec_ref(v_a_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_toApplicative_478_; lean_object* v_toBind_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_toApplicative_478_ = lean_ctor_get(v_inst_475_, 0);
lean_inc_ref(v_toApplicative_478_);
v_toBind_479_ = lean_ctor_get(v_inst_475_, 1);
lean_inc(v_toBind_479_);
lean_dec_ref(v_inst_475_);
v___f_480_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed), 2, 1);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_484_, v_inst_485_, v_a_486_);
lean_dec(v_a_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(lean_object* v_m_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_489_, v_inst_490_, v_a_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(lean_object* v_m_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(v_m_493_, v_inst_494_, v_inst_495_, v_a_496_);
lean_dec(v_a_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(lean_object* v_toApplicative_498_, lean_object* v_a_499_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(v_toApplicative_508_, v_a_509_);
lean_dec_ref(v_a_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_toApplicative_514_; lean_object* v_toBind_515_; lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_toApplicative_514_ = lean_ctor_get(v_inst_511_, 0);
lean_inc_ref(v_toApplicative_514_);
v_toBind_515_ = lean_ctor_get(v_inst_511_, 1);
lean_inc(v_toBind_515_);
lean_dec_ref(v_inst_511_);
v___f_516_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed), 2, 1);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_520_, v_inst_521_, v_a_522_);
lean_dec(v_a_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(lean_object* v_m_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_525_, v_inst_526_, v_a_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(lean_object* v_m_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(v_m_529_, v_inst_530_, v_inst_531_, v_a_532_);
lean_dec(v_a_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_534_, lean_object* v_chunk_535_, lean_object* v_a_536_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_540_, lean_object* v_done_541_, lean_object* v_inst_542_, lean_object* v_toBind_543_, lean_object* v___f_544_, lean_object* v_a_545_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_555_, lean_object* v_inst_556_, lean_object* v_toBind_557_, lean_object* v_a_558_, lean_object* v_inst_559_, lean_object* v_a_560_){
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
v___f_574_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_574_, 0, v_toApplicative_555_);
lean_closure_set(v___f_574_, 1, v_chunk_571_);
lean_inc(v_toBind_557_);
v___f_575_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_575_, 0, v_toApplicative_555_);
lean_closure_set(v___f_575_, 1, v_done_572_);
lean_closure_set(v___f_575_, 2, v_inst_556_);
lean_closure_set(v___f_575_, 3, v_toBind_557_);
lean_closure_set(v___f_575_, 4, v___f_574_);
v___x_576_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_566_, v_chunk_571_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_toApplicative_588_, lean_object* v_inst_589_, lean_object* v_toBind_590_, lean_object* v_a_591_, lean_object* v_inst_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(v_toApplicative_588_, v_inst_589_, v_toBind_590_, v_a_591_, v_inst_592_, v_a_593_);
lean_dec(v_a_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_a_598_){
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
v___f_601_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_605_, v_inst_606_, v_inst_607_, v_a_608_);
lean_dec(v_a_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(lean_object* v_m_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_611_, v_inst_612_, v_inst_613_, v_a_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(lean_object* v_m_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(v_m_616_, v_inst_617_, v_inst_618_, v_inst_619_, v_a_620_);
lean_dec(v_a_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(uint8_t v___x_622_, lean_object* v_knownSize_623_, lean_object* v_inst_624_, lean_object* v_____r_625_, lean_object* v___y_626_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed(lean_object* v___x_631_, lean_object* v_knownSize_632_, lean_object* v_inst_633_, lean_object* v_____r_634_, lean_object* v___y_635_){
_start:
{
uint8_t v___x_781__boxed_636_; lean_object* v_res_637_; 
v___x_781__boxed_636_ = lean_unbox(v___x_631_);
v_res_637_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(v___x_781__boxed_636_, v_knownSize_632_, v_inst_633_, v_____r_634_, v___y_635_);
lean_dec(v___y_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(lean_object* v___f_638_, lean_object* v___y_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_641_; 
lean_inc(v___y_639_);
v___x_641_ = lean_apply_2(v___f_638_, v_a_640_, v___y_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object* v___f_642_, lean_object* v___y_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(v___f_642_, v___y_643_, v_a_644_);
lean_dec(v___y_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object* v_pendingProducer_646_, lean_object* v_toApplicative_647_, lean_object* v___f_648_, uint8_t v_closed_649_, lean_object* v_inst_650_, lean_object* v_toBind_651_, lean_object* v_____r_652_, lean_object* v___y_653_){
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
v___f_658_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed(lean_object* v_pendingProducer_667_, lean_object* v_toApplicative_668_, lean_object* v___f_669_, lean_object* v_closed_670_, lean_object* v_inst_671_, lean_object* v_toBind_672_, lean_object* v_____r_673_, lean_object* v___y_674_){
_start:
{
uint8_t v_closed_boxed_675_; lean_object* v_res_676_; 
v_closed_boxed_675_ = lean_unbox(v_closed_670_);
v_res_676_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(v_pendingProducer_667_, v_toApplicative_668_, v___f_669_, v_closed_boxed_675_, v_inst_671_, v_toBind_672_, v_____r_673_, v___y_674_);
lean_dec(v___y_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object* v_interestWaiter_677_, lean_object* v_toApplicative_678_, lean_object* v___f_679_, uint8_t v_closed_680_, lean_object* v_inst_681_, lean_object* v_toBind_682_, lean_object* v_____r_683_, lean_object* v___y_684_){
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
v___f_688_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_688_, 0, v___f_679_);
lean_closure_set(v___f_688_, 1, v___y_684_);
v___x_689_ = lean_box(v_closed_680_);
v___x_690_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object* v_interestWaiter_697_, lean_object* v_toApplicative_698_, lean_object* v___f_699_, lean_object* v_closed_700_, lean_object* v_inst_701_, lean_object* v_toBind_702_, lean_object* v_____r_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_closed_boxed_705_; lean_object* v_res_706_; 
v_closed_boxed_705_ = lean_unbox(v_closed_700_);
v_res_706_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_697_, v_toApplicative_698_, v___f_699_, v_closed_boxed_705_, v_inst_701_, v_toBind_702_, v_____r_703_, v___y_704_);
lean_dec(v___y_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(lean_object* v___f_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_710_; 
lean_inc(v_a_708_);
v___x_710_ = lean_apply_2(v___f_707_, v_a_709_, v_a_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object* v___f_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(v___f_711_, v_a_712_, v_a_713_);
lean_dec(v_a_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object* v_inst_715_, lean_object* v_toApplicative_716_, lean_object* v_inst_717_, lean_object* v_toBind_718_, lean_object* v_a_719_, lean_object* v_a_720_){
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
v___f_728_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_728_, 0, v___x_727_);
lean_closure_set(v___f_728_, 1, v_knownSize_725_);
lean_closure_set(v___f_728_, 2, v_inst_715_);
v___x_729_ = lean_box(v_closed_721_);
lean_inc_n(v_toBind_718_, 2);
lean_inc_n(v_inst_717_, 2);
lean_inc_ref_n(v_toApplicative_716_, 2);
v___f_730_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_730_, 0, v_pendingProducer_722_);
lean_closure_set(v___f_730_, 1, v_toApplicative_716_);
lean_closure_set(v___f_730_, 2, v___f_728_);
lean_closure_set(v___f_730_, 3, v___x_729_);
lean_closure_set(v___f_730_, 4, v_inst_717_);
lean_closure_set(v___f_730_, 5, v_toBind_718_);
v___x_731_ = lean_box(v_closed_721_);
lean_inc_ref(v___f_730_);
v___f_732_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed), 8, 6);
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
v___f_736_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_736_, 0, v___f_732_);
lean_closure_set(v___f_736_, 1, v_a_719_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed), 3, 2);
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
v___x_744_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_724_, v_toApplicative_716_, v___f_730_, v_closed_721_, v_inst_717_, v_toBind_718_, v___x_743_, v_a_719_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object* v_inst_748_, lean_object* v_toApplicative_749_, lean_object* v_inst_750_, lean_object* v_toBind_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(v_inst_748_, v_toApplicative_749_, v_inst_750_, v_toBind_751_, v_a_752_, v_a_753_);
lean_dec(v_a_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_a_758_){
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
v___f_761_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_765_, v_inst_766_, v_inst_767_, v_a_768_);
lean_dec(v_a_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object* v_m_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_771_, v_inst_772_, v_inst_773_, v_a_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object* v_m_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(v_m_776_, v_inst_777_, v_inst_778_, v_inst_779_, v_a_780_);
lean_dec(v_a_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object* v_chunk_782_, lean_object* v_x_783_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object* v_chunk_804_, lean_object* v_x_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_chunk_804_, v_x_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object* v_done_812_, lean_object* v___f_813_, lean_object* v_x_814_){
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
v___x_828_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = 0;
v___x_831_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_829_, v___x_830_, v___x_828_, v___f_813_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object* v_done_832_, lean_object* v___f_833_, lean_object* v_x_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_done_832_, v___f_833_, v_x_834_);
lean_dec(v_done_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2(lean_object* v_a_841_, lean_object* v_x_842_){
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
v___x_873_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_865_, v_chunk_870_);
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
v___f_877_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_877_, 0, v_chunk_870_);
v___f_878_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed), 4, 2);
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
v___x_885_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_883_, v___x_884_, v___x_882_, v___f_878_);
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
v___x_892_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1));
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___boxed(lean_object* v_a_894_, lean_object* v_x_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2(v_a_894_, v_x_895_);
lean_dec(v_a_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; 
v___x_900_ = lean_st_ref_get(v_a_898_);
lean_inc(v_a_898_);
v___f_901_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___boxed), 3, 1);
lean_closure_set(v___f_901_, 0, v_a_898_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = 0;
v___x_906_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_904_, v___x_905_, v___x_903_, v___f_901_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object* v_a_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_907_);
lean_dec(v_a_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object* v_pendingProducer_910_, lean_object* v_pendingConsumer_911_, uint8_t v_closed_912_, lean_object* v_knownSize_913_, lean_object* v_pendingIncompleteChunk_914_, lean_object* v_interestWaiter_915_, lean_object* v___y_916_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object* v_pendingProducer_922_, lean_object* v_pendingConsumer_923_, lean_object* v_closed_924_, lean_object* v_knownSize_925_, lean_object* v_pendingIncompleteChunk_926_, lean_object* v_interestWaiter_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v_closed_boxed_930_; lean_object* v_res_931_; 
v_closed_boxed_930_ = lean_unbox(v_closed_924_);
v_res_931_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_922_, v_pendingConsumer_923_, v_closed_boxed_930_, v_knownSize_925_, v_pendingIncompleteChunk_926_, v_interestWaiter_927_, v___y_928_);
lean_dec(v___y_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object* v___f_932_, lean_object* v___y_933_, lean_object* v_x_934_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object* v___f_947_, lean_object* v___y_948_, lean_object* v_x_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_947_, v___y_948_, v_x_949_);
lean_dec(v___y_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object* v_interestWaiter_956_, lean_object* v___f_957_, lean_object* v___f_958_, lean_object* v_x_959_){
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
v___x_980_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_978_, v___x_979_, v___x_977_, v___f_957_);
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
v___x_982_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1));
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_984_ = 0;
v___x_985_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_983_, v___x_984_, v___x_982_, v___f_958_);
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object* v_interestWaiter_987_, lean_object* v___f_988_, lean_object* v___f_989_, lean_object* v_x_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_987_, v___f_988_, v___f_989_, v_x_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object* v_pendingProducer_993_, uint8_t v_closed_994_, lean_object* v_knownSize_995_, lean_object* v_pendingIncompleteChunk_996_, lean_object* v_interestWaiter_997_, lean_object* v_pendingConsumer_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___f_1002_; 
v___x_1001_ = lean_box(v_closed_994_);
v___f_1002_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed), 8, 5);
lean_closure_set(v___f_1002_, 0, v_pendingProducer_993_);
lean_closure_set(v___f_1002_, 1, v_pendingConsumer_998_);
lean_closure_set(v___f_1002_, 2, v___x_1001_);
lean_closure_set(v___f_1002_, 3, v_knownSize_995_);
lean_closure_set(v___f_1002_, 4, v_pendingIncompleteChunk_996_);
if (lean_obj_tag(v_interestWaiter_997_) == 0)
{
lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; 
lean_inc(v___y_999_);
v___f_1003_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1003_, 0, v___f_1002_);
lean_closure_set(v___f_1003_, 1, v___y_999_);
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_interestWaiter_997_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = 0;
v___x_1008_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1006_, v___x_1007_, v___x_1005_, v___f_1003_);
return v___x_1008_;
}
else
{
lean_object* v_val_1009_; lean_object* v_finished_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; 
v_val_1009_ = lean_ctor_get(v_interestWaiter_997_, 0);
v_finished_1010_ = lean_ctor_get(v_val_1009_, 0);
v___x_1011_ = lean_st_ref_get(v_finished_1010_);
lean_inc(v___y_999_);
v___f_1012_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1012_, 0, v___f_1002_);
lean_closure_set(v___f_1012_, 1, v___y_999_);
lean_inc_ref(v___f_1012_);
v___f_1013_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1013_, 0, v_interestWaiter_997_);
lean_closure_set(v___f_1013_, 1, v___f_1012_);
lean_closure_set(v___f_1013_, 2, v___f_1012_);
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1011_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = 0;
v___x_1018_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1016_, v___x_1017_, v___x_1015_, v___f_1013_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object* v_pendingProducer_1019_, lean_object* v_closed_1020_, lean_object* v_knownSize_1021_, lean_object* v_pendingIncompleteChunk_1022_, lean_object* v_interestWaiter_1023_, lean_object* v_pendingConsumer_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
uint8_t v_closed_boxed_1027_; lean_object* v_res_1028_; 
v_closed_boxed_1027_ = lean_unbox(v_closed_1020_);
v_res_1028_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_1019_, v_closed_boxed_1027_, v_knownSize_1021_, v_pendingIncompleteChunk_1022_, v_interestWaiter_1023_, v_pendingConsumer_1024_, v___y_1025_);
lean_dec(v___y_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object* v___f_1029_, lean_object* v___y_1030_, lean_object* v_x_1031_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object* v___f_1044_, lean_object* v___y_1045_, lean_object* v_x_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_1044_, v___y_1045_, v_x_1046_);
lean_dec(v___y_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object* v___f_1049_, lean_object* v_a_1050_, lean_object* v_x_1051_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object* v___f_1064_, lean_object* v_a_1065_, lean_object* v_x_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_1064_, v_a_1065_, v_x_1066_);
lean_dec(v_a_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object* v_pendingConsumer_1073_, lean_object* v___f_1074_, lean_object* v___f_1075_, lean_object* v_x_1076_){
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
v___x_1097_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1095_, v___x_1096_, v___x_1094_, v___f_1074_);
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
v___x_1099_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1));
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = 0;
v___x_1102_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1100_, v___x_1101_, v___x_1099_, v___f_1075_);
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object* v_pendingConsumer_1104_, lean_object* v___f_1105_, lean_object* v___f_1106_, lean_object* v_x_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_1104_, v___f_1105_, v___f_1106_, v_x_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object* v_a_1110_, lean_object* v_x_1111_){
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
v___f_1133_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed), 8, 5);
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
v___f_1151_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1151_, 0, v___f_1133_);
lean_closure_set(v___f_1151_, 1, v_a_1110_);
lean_inc_ref(v___f_1151_);
v___f_1152_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed), 5, 3);
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
v___x_1158_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1156_, v___x_1157_, v___x_1155_, v___f_1152_);
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
v___f_1136_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed), 4, 2);
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
v___x_1142_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1140_, v___x_1141_, v___x_1139_, v___f_1136_);
return v___x_1142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object* v_a_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_1162_, v_x_1163_);
lean_dec(v_a_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; 
v___x_1168_ = lean_st_ref_get(v_a_1166_);
lean_inc(v_a_1166_);
v___f_1169_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1169_, 0, v_a_1166_);
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = 0;
v___x_1174_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1172_, v___x_1173_, v___x_1171_, v___f_1169_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object* v_a_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_1175_);
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
v___x_1215_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1213_, v___x_1214_, v___x_1212_, v___f_1208_);
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
v___x_1249_ = l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(v___f_1246_, v___f_1244_, v___x_1247_, v___x_1248_);
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
v___x_1309_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1297_);
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
v___x_1316_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_1314_);
lean_inc(v___y_1314_);
v___f_1317_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecv___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1317_, 0, v___y_1314_);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = 0;
v___x_1320_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1318_, v___x_1319_, v___x_1316_, v___f_1317_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object* v_a_1332_){
_start:
{
lean_object* v___x_1334_; lean_object* v_pendingProducer_1335_; lean_object* v_pendingConsumer_1336_; lean_object* v_interestWaiter_1337_; uint8_t v_closed_1338_; lean_object* v_knownSize_1339_; lean_object* v_pendingIncompleteChunk_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1366_; 
v___x_1334_ = lean_st_ref_get(v_a_1332_);
v_pendingProducer_1335_ = lean_ctor_get(v___x_1334_, 0);
v_pendingConsumer_1336_ = lean_ctor_get(v___x_1334_, 1);
v_interestWaiter_1337_ = lean_ctor_get(v___x_1334_, 2);
v_closed_1338_ = lean_ctor_get_uint8(v___x_1334_, sizeof(void*)*5);
v_knownSize_1339_ = lean_ctor_get(v___x_1334_, 3);
v_pendingIncompleteChunk_1340_ = lean_ctor_get(v___x_1334_, 4);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1342_ = v___x_1334_;
v_isShared_1343_ = v_isSharedCheck_1366_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1340_);
lean_inc(v_knownSize_1339_);
lean_inc(v_interestWaiter_1337_);
lean_inc(v_pendingConsumer_1336_);
lean_inc(v_pendingProducer_1335_);
lean_dec(v___x_1334_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1366_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___y_1345_; lean_object* v_interestWaiter_1346_; lean_object* v___y_1347_; lean_object* v_pendingConsumer_1353_; lean_object* v___y_1354_; 
if (lean_obj_tag(v_pendingConsumer_1336_) == 1)
{
lean_object* v_val_1360_; 
v_val_1360_ = lean_ctor_get(v_pendingConsumer_1336_, 0);
if (lean_obj_tag(v_val_1360_) == 1)
{
lean_object* v_finished_1361_; lean_object* v_finished_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_finished_1361_ = lean_ctor_get(v_val_1360_, 0);
v_finished_1362_ = lean_ctor_get(v_finished_1361_, 0);
v___x_1363_ = lean_st_ref_get(v_finished_1362_);
v___x_1364_ = lean_unbox(v___x_1363_);
lean_dec(v___x_1363_);
if (v___x_1364_ == 0)
{
v_pendingConsumer_1353_ = v_pendingConsumer_1336_;
v___y_1354_ = v_a_1332_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1365_; 
lean_dec_ref(v_pendingConsumer_1336_);
v___x_1365_ = lean_box(0);
v_pendingConsumer_1353_ = v___x_1365_;
v___y_1354_ = v_a_1332_;
goto v___jp_1352_;
}
}
else
{
v_pendingConsumer_1353_ = v_pendingConsumer_1336_;
v___y_1354_ = v_a_1332_;
goto v___jp_1352_;
}
}
else
{
v_pendingConsumer_1353_ = v_pendingConsumer_1336_;
v___y_1354_ = v_a_1332_;
goto v___jp_1352_;
}
v___jp_1344_:
{
lean_object* v___x_1349_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 2, v_interestWaiter_1346_);
lean_ctor_set(v___x_1342_, 1, v___y_1345_);
v___x_1349_ = v___x_1342_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_pendingProducer_1335_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v___y_1345_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_interestWaiter_1346_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_knownSize_1339_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_pendingIncompleteChunk_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*5, v_closed_1338_);
v___x_1349_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_st_ref_set(v___y_1347_, v___x_1349_);
return v___x_1350_;
}
}
v___jp_1352_:
{
if (lean_obj_tag(v_interestWaiter_1337_) == 0)
{
v___y_1345_ = v_pendingConsumer_1353_;
v_interestWaiter_1346_ = v_interestWaiter_1337_;
v___y_1347_ = v___y_1354_;
goto v___jp_1344_;
}
else
{
lean_object* v_val_1355_; lean_object* v_finished_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_val_1355_ = lean_ctor_get(v_interestWaiter_1337_, 0);
v_finished_1356_ = lean_ctor_get(v_val_1355_, 0);
v___x_1357_ = lean_st_ref_get(v_finished_1356_);
v___x_1358_ = lean_unbox(v___x_1357_);
lean_dec(v___x_1357_);
if (v___x_1358_ == 0)
{
v___y_1345_ = v_pendingConsumer_1353_;
v_interestWaiter_1346_ = v_interestWaiter_1337_;
v___y_1347_ = v___y_1354_;
goto v___jp_1344_;
}
else
{
lean_object* v___x_1359_; 
lean_dec_ref(v_interestWaiter_1337_);
v___x_1359_ = lean_box(0);
v___y_1345_ = v_pendingConsumer_1353_;
v_interestWaiter_1346_ = v___x_1359_;
v___y_1347_ = v___y_1354_;
goto v___jp_1344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object* v_a_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_1367_);
lean_dec(v_a_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v_pendingProducer_1373_; 
v___x_1372_ = lean_st_ref_get(v_a_1370_);
v_pendingProducer_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_pendingProducer_1373_);
if (lean_obj_tag(v_pendingProducer_1373_) == 1)
{
lean_object* v_val_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1402_; 
v_val_1374_ = lean_ctor_get(v_pendingProducer_1373_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_pendingProducer_1373_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1376_ = v_pendingProducer_1373_;
v_isShared_1377_ = v_isSharedCheck_1402_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_val_1374_);
lean_dec(v_pendingProducer_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1402_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_pendingConsumer_1378_; lean_object* v_interestWaiter_1379_; uint8_t v_closed_1380_; lean_object* v_knownSize_1381_; lean_object* v_pendingIncompleteChunk_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1400_; 
v_pendingConsumer_1378_ = lean_ctor_get(v___x_1372_, 1);
v_interestWaiter_1379_ = lean_ctor_get(v___x_1372_, 2);
v_closed_1380_ = lean_ctor_get_uint8(v___x_1372_, sizeof(void*)*5);
v_knownSize_1381_ = lean_ctor_get(v___x_1372_, 3);
v_pendingIncompleteChunk_1382_ = lean_ctor_get(v___x_1372_, 4);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1372_, 0);
lean_dec(v_unused_1401_);
v___x_1384_ = v___x_1372_;
v_isShared_1385_ = v_isSharedCheck_1400_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1382_);
lean_inc(v_knownSize_1381_);
lean_inc(v_interestWaiter_1379_);
lean_inc(v_pendingConsumer_1378_);
lean_dec(v___x_1372_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1400_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v_chunk_1386_; lean_object* v_done_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v_chunk_1386_ = lean_ctor_get(v_val_1374_, 0);
lean_inc_ref(v_chunk_1386_);
v_done_1387_ = lean_ctor_get(v_val_1374_, 1);
lean_inc(v_done_1387_);
lean_dec(v_val_1374_);
v___x_1388_ = lean_box(0);
v___x_1389_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1381_, v_chunk_1386_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 3, v___x_1389_);
lean_ctor_set(v___x_1384_, 0, v___x_1388_);
v___x_1391_ = v___x_1384_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_pendingConsumer_1378_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_interestWaiter_1379_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_pendingIncompleteChunk_1382_);
lean_ctor_set_uint8(v_reuseFailAlloc_1399_, sizeof(void*)*5, v_closed_1380_);
v___x_1391_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1392_ = lean_st_ref_set(v_a_1370_, v___x_1391_);
v___x_1393_ = 1;
v___x_1394_ = lean_box(v___x_1393_);
v___x_1395_ = lean_io_promise_resolve(v___x_1394_, v_done_1387_);
lean_dec(v_done_1387_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v_chunk_1386_);
v___x_1397_ = v___x_1376_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_chunk_1386_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
else
{
lean_object* v___x_1403_; 
lean_dec(v_pendingProducer_1373_);
lean_dec(v___x_1372_);
v___x_1403_ = lean_box(0);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object* v_a_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_1404_);
lean_dec(v_a_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v_interestWaiter_1410_; 
v___x_1409_ = lean_st_ref_get(v_a_1407_);
v_interestWaiter_1410_ = lean_ctor_get(v___x_1409_, 2);
lean_inc(v_interestWaiter_1410_);
if (lean_obj_tag(v_interestWaiter_1410_) == 1)
{
lean_object* v_pendingProducer_1411_; lean_object* v_pendingConsumer_1412_; uint8_t v_closed_1413_; lean_object* v_knownSize_1414_; lean_object* v_pendingIncompleteChunk_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1427_; 
v_pendingProducer_1411_ = lean_ctor_get(v___x_1409_, 0);
v_pendingConsumer_1412_ = lean_ctor_get(v___x_1409_, 1);
v_closed_1413_ = lean_ctor_get_uint8(v___x_1409_, sizeof(void*)*5);
v_knownSize_1414_ = lean_ctor_get(v___x_1409_, 3);
v_pendingIncompleteChunk_1415_ = lean_ctor_get(v___x_1409_, 4);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v___x_1409_, 2);
lean_dec(v_unused_1428_);
v___x_1417_ = v___x_1409_;
v_isShared_1418_ = v_isSharedCheck_1427_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1415_);
lean_inc(v_knownSize_1414_);
lean_inc(v_pendingConsumer_1412_);
lean_inc(v_pendingProducer_1411_);
lean_dec(v___x_1409_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1427_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_val_1419_; uint8_t v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v_val_1419_ = lean_ctor_get(v_interestWaiter_1410_, 0);
lean_inc(v_val_1419_);
lean_dec_ref(v_interestWaiter_1410_);
v___x_1420_ = 1;
v___x_1421_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1419_, v___x_1420_);
lean_dec(v_val_1419_);
v___x_1422_ = lean_box(0);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 2, v___x_1422_);
v___x_1424_ = v___x_1417_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_pendingProducer_1411_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_pendingConsumer_1412_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_knownSize_1414_);
lean_ctor_set(v_reuseFailAlloc_1426_, 4, v_pendingIncompleteChunk_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1426_, sizeof(void*)*5, v_closed_1413_);
v___x_1424_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_st_ref_set(v_a_1407_, v___x_1424_);
return v___x_1425_;
}
}
}
else
{
lean_object* v___x_1429_; 
lean_dec(v_interestWaiter_1410_);
lean_dec(v___x_1409_);
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object* v_a_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_1430_);
lean_dec(v_a_1430_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object* v_mutex_1433_, lean_object* v_k_1434_){
_start:
{
lean_object* v_ref_1436_; lean_object* v_mutex_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_ref_1436_ = lean_ctor_get(v_mutex_1433_, 0);
lean_inc(v_ref_1436_);
v_mutex_1437_ = lean_ctor_get(v_mutex_1433_, 1);
lean_inc(v_mutex_1437_);
lean_dec_ref(v_mutex_1433_);
v___x_1438_ = lean_io_basemutex_lock(v_mutex_1437_);
v___x_1439_ = lean_apply_2(v_k_1434_, v_ref_1436_, lean_box(0));
v___x_1440_ = lean_io_basemutex_unlock(v_mutex_1437_);
lean_dec(v_mutex_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object* v_mutex_1441_, lean_object* v_k_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1441_, v_k_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object* v_00_u03b1_1445_, lean_object* v_00_u03b2_1446_, lean_object* v_mutex_1447_, lean_object* v_k_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_1447_, v_k_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_mutex_1453_, lean_object* v_k_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(v_00_u03b1_1451_, v_00_u03b2_1452_, v_mutex_1453_, v_k_1454_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object* v_x_1462_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2));
return v___x_1463_;
}
else
{
lean_object* v_val_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_val_1464_ = lean_ctor_get(v_x_1462_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_x_1462_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v_x_1462_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_val_1464_);
lean_dec(v_x_1462_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_val_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2));
v___x_1478_ = lean_task_pure(v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0));
v___x_1480_ = lean_task_pure(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object* v___f_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_1482_);
v___x_1485_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_1482_);
if (lean_obj_tag(v___x_1485_) == 1)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref(v___f_1481_);
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
v___x_1487_ = lean_task_pure(v___x_1486_);
return v___x_1487_;
}
else
{
lean_object* v___x_1488_; uint8_t v_closed_1489_; 
lean_dec(v___x_1485_);
v___x_1488_ = lean_st_ref_get(v___y_1482_);
v_closed_1489_ = lean_ctor_get_uint8(v___x_1488_, sizeof(void*)*5);
if (v_closed_1489_ == 0)
{
lean_object* v_pendingConsumer_1490_; 
v_pendingConsumer_1490_ = lean_ctor_get(v___x_1488_, 1);
lean_inc(v_pendingConsumer_1490_);
if (lean_obj_tag(v_pendingConsumer_1490_) == 0)
{
lean_object* v_pendingProducer_1491_; lean_object* v_interestWaiter_1492_; lean_object* v_knownSize_1493_; lean_object* v_pendingIncompleteChunk_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1510_; 
v_pendingProducer_1491_ = lean_ctor_get(v___x_1488_, 0);
v_interestWaiter_1492_ = lean_ctor_get(v___x_1488_, 2);
v_knownSize_1493_ = lean_ctor_get(v___x_1488_, 3);
v_pendingIncompleteChunk_1494_ = lean_ctor_get(v___x_1488_, 4);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v___x_1488_, 1);
lean_dec(v_unused_1511_);
v___x_1496_ = v___x_1488_;
v_isShared_1497_ = v_isSharedCheck_1510_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1494_);
lean_inc(v_knownSize_1493_);
lean_inc(v_interestWaiter_1492_);
lean_inc(v_pendingProducer_1491_);
lean_dec(v___x_1488_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1510_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1498_ = lean_io_promise_new();
lean_inc(v___x_1498_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v___x_1500_);
v___x_1502_ = v___x_1496_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_pendingProducer_1491_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_interestWaiter_1492_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_knownSize_1493_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_pendingIncompleteChunk_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*5, v_closed_1489_);
v___x_1502_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1503_ = lean_st_ref_set(v___y_1482_, v___x_1502_);
v___x_1504_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_1482_);
v___x_1505_ = 1;
v___x_1506_ = lean_io_promise_result_opt(v___x_1498_);
lean_dec(v___x_1498_);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_task_map(v___f_1481_, v___x_1506_, v___x_1507_, v___x_1505_);
return v___x_1508_;
}
}
}
else
{
lean_object* v___x_1512_; 
lean_dec_ref(v_pendingConsumer_1490_);
lean_dec(v___x_1488_);
lean_dec_ref(v___f_1481_);
v___x_1512_ = lean_obj_once(&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3, &l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3);
return v___x_1512_;
}
}
else
{
lean_object* v___x_1513_; 
lean_dec(v___x_1488_);
lean_dec_ref(v___f_1481_);
v___x_1513_ = lean_obj_once(&l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4, &l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4);
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object* v___f_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(v___f_1514_, v___y_1515_);
lean_dec(v___y_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object* v_stream_1521_){
_start:
{
lean_object* v___f_1523_; lean_object* v___x_1524_; 
v___f_1523_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1));
v___x_1524_ = l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_1521_, v___f_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object* v_stream_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object* v_x_1528_){
_start:
{
if (lean_obj_tag(v_x_1528_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1538_; 
v_a_1530_ = lean_ctor_get(v_x_1528_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_x_1528_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1532_ = v_x_1528_;
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v_x_1528_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
return v___x_1536_;
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v_x_1528_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v_x_1528_);
v___x_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_a_1539_);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object* v_x_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv(lean_object* v_stream_1545_){
_start:
{
lean_object* v___x_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; 
v___x_1547_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_1545_);
v___f_1548_ = ((lean_object*)(l_Std_Http_Body_Stream_recv___closed__0));
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = 0;
v___x_1553_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1551_, v___x_1552_, v___x_1550_, v___f_1548_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object* v_stream_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_Http_Body_Stream_recv(v_stream_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(uint8_t v___x_1557_, lean_object* v_knownSize_1558_, lean_object* v_____r_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
lean_ctor_set(v___x_1563_, 2, v___x_1562_);
lean_ctor_set(v___x_1563_, 3, v_knownSize_1558_);
lean_ctor_set(v___x_1563_, 4, v___x_1562_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*5, v___x_1557_);
v___x_1564_ = lean_st_ref_set(v___y_1560_, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(lean_object* v___x_1567_, lean_object* v_knownSize_1568_, lean_object* v_____r_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v___x_1931__boxed_1572_; lean_object* v_res_1573_; 
v___x_1931__boxed_1572_ = lean_unbox(v___x_1567_);
v_res_1573_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(v___x_1931__boxed_1572_, v_knownSize_1568_, v_____r_1569_, v___y_1570_);
lean_dec(v___y_1570_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(lean_object* v___f_1574_, lean_object* v___y_1575_, lean_object* v_x_1576_){
_start:
{
if (lean_obj_tag(v_x_1576_) == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref(v___f_1574_);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_x_1576_);
return v___x_1578_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v_x_1576_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v_x_1576_);
lean_inc(v___y_1575_);
v___x_1580_ = lean_apply_3(v___f_1574_, v_a_1579_, v___y_1575_, lean_box(0));
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed(lean_object* v___f_1581_, lean_object* v___y_1582_, lean_object* v_x_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(v___f_1581_, v___y_1582_, v_x_1583_);
lean_dec(v___y_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(lean_object* v_pendingProducer_1586_, uint8_t v_closed_1587_, lean_object* v___f_1588_, lean_object* v_____r_1589_, lean_object* v___y_1590_){
_start:
{
if (lean_obj_tag(v_pendingProducer_1586_) == 1)
{
lean_object* v_val_1592_; lean_object* v_done_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_val_1592_ = lean_ctor_get(v_pendingProducer_1586_, 0);
v_done_1593_ = lean_ctor_get(v_val_1592_, 1);
v___x_1594_ = lean_box(v_closed_1587_);
v___x_1595_ = lean_io_promise_resolve(v___x_1594_, v_done_1593_);
lean_inc(v___y_1590_);
v___f_1596_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1596_, 0, v___f_1588_);
lean_closure_set(v___f_1596_, 1, v___y_1590_);
v___x_1597_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1598_, v_closed_1587_, v___x_1597_, v___f_1596_);
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_box(0);
lean_inc(v___y_1590_);
v___x_1601_ = lean_apply_3(v___f_1588_, v___x_1600_, v___y_1590_, lean_box(0));
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(lean_object* v_pendingProducer_1602_, lean_object* v_closed_1603_, lean_object* v___f_1604_, lean_object* v_____r_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v_closed_boxed_1608_; lean_object* v_res_1609_; 
v_closed_boxed_1608_ = lean_unbox(v_closed_1603_);
v_res_1609_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(v_pendingProducer_1602_, v_closed_boxed_1608_, v___f_1604_, v_____r_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec(v_pendingProducer_1602_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(lean_object* v_interestWaiter_1610_, uint8_t v_closed_1611_, lean_object* v___f_1612_, lean_object* v_____r_1613_, lean_object* v___y_1614_){
_start:
{
if (lean_obj_tag(v_interestWaiter_1610_) == 1)
{
lean_object* v_val_1616_; uint8_t v___x_1617_; lean_object* v___f_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_val_1616_ = lean_ctor_get(v_interestWaiter_1610_, 0);
v___x_1617_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1616_, v_closed_1611_);
lean_inc(v___y_1614_);
v___f_1618_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1618_, 0, v___f_1612_);
lean_closure_set(v___f_1618_, 1, v___y_1614_);
v___x_1619_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1620_, v_closed_1611_, v___x_1619_, v___f_1618_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_box(0);
lean_inc(v___y_1614_);
v___x_1623_ = lean_apply_3(v___f_1612_, v___x_1622_, v___y_1614_, lean_box(0));
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(lean_object* v_interestWaiter_1624_, lean_object* v_closed_1625_, lean_object* v___f_1626_, lean_object* v_____r_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v_closed_boxed_1630_; lean_object* v_res_1631_; 
v_closed_boxed_1630_ = lean_unbox(v_closed_1625_);
v_res_1631_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_1624_, v_closed_boxed_1630_, v___f_1626_, v_____r_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec(v_interestWaiter_1624_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(lean_object* v___f_1632_, lean_object* v_a_1633_, lean_object* v_x_1634_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref(v___f_1632_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_x_1634_);
return v___x_1636_;
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v_x_1634_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v_x_1634_);
lean_inc(v_a_1633_);
v___x_1638_ = lean_apply_3(v___f_1632_, v_a_1637_, v_a_1633_, lean_box(0));
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed(lean_object* v___f_1639_, lean_object* v_a_1640_, lean_object* v_x_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(v___f_1639_, v_a_1640_, v_x_1641_);
lean_dec(v_a_1640_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(lean_object* v_a_1644_, lean_object* v_x_1645_){
_start:
{
if (lean_obj_tag(v_x_1645_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1655_; 
v_a_1647_ = lean_ctor_get(v_x_1645_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_x_1645_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1649_ = v_x_1645_;
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v_x_1645_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
}
else
{
lean_object* v_a_1656_; uint8_t v_closed_1657_; 
v_a_1656_ = lean_ctor_get(v_x_1645_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v_x_1645_);
v_closed_1657_ = lean_ctor_get_uint8(v_a_1656_, sizeof(void*)*5);
if (v_closed_1657_ == 0)
{
lean_object* v_pendingProducer_1658_; lean_object* v_pendingConsumer_1659_; lean_object* v_interestWaiter_1660_; lean_object* v_knownSize_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___f_1668_; 
v_pendingProducer_1658_ = lean_ctor_get(v_a_1656_, 0);
lean_inc(v_pendingProducer_1658_);
v_pendingConsumer_1659_ = lean_ctor_get(v_a_1656_, 1);
lean_inc(v_pendingConsumer_1659_);
v_interestWaiter_1660_ = lean_ctor_get(v_a_1656_, 2);
lean_inc_n(v_interestWaiter_1660_, 2);
v_knownSize_1661_ = lean_ctor_get(v_a_1656_, 3);
lean_inc(v_knownSize_1661_);
lean_dec(v_a_1656_);
v___x_1662_ = 1;
v___x_1663_ = lean_box(v___x_1662_);
v___f_1664_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1664_, 0, v___x_1663_);
lean_closure_set(v___f_1664_, 1, v_knownSize_1661_);
v___x_1665_ = lean_box(v_closed_1657_);
v___f_1666_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1666_, 0, v_pendingProducer_1658_);
lean_closure_set(v___f_1666_, 1, v___x_1665_);
lean_closure_set(v___f_1666_, 2, v___f_1664_);
v___x_1667_ = lean_box(v_closed_1657_);
lean_inc_ref(v___f_1666_);
v___f_1668_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1668_, 0, v_interestWaiter_1660_);
lean_closure_set(v___f_1668_, 1, v___x_1667_);
lean_closure_set(v___f_1668_, 2, v___f_1666_);
if (lean_obj_tag(v_pendingConsumer_1659_) == 1)
{
lean_object* v_val_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; lean_object* v___f_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec_ref(v___f_1666_);
lean_dec(v_interestWaiter_1660_);
v_val_1669_ = lean_ctor_get(v_pendingConsumer_1659_, 0);
lean_inc(v_val_1669_);
lean_dec_ref(v_pendingConsumer_1659_);
v___x_1670_ = lean_box(0);
v___x_1671_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_1669_, v___x_1670_);
lean_dec(v_val_1669_);
lean_inc(v_a_1644_);
v___f_1672_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1672_, 0, v___f_1668_);
lean_closure_set(v___f_1672_, 1, v_a_1644_);
v___x_1673_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1674_, v_closed_1657_, v___x_1673_, v___f_1672_);
return v___x_1675_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v___f_1668_);
lean_dec(v_pendingConsumer_1659_);
v___x_1676_ = lean_box(0);
v___x_1677_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_1660_, v_closed_1657_, v___f_1666_, v___x_1676_, v_a_1644_);
lean_dec(v_interestWaiter_1660_);
return v___x_1677_;
}
}
else
{
lean_object* v___x_1678_; 
lean_dec(v_a_1656_);
v___x_1678_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed(lean_object* v_a_1679_, lean_object* v_x_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(v_a_1679_, v_x_1680_);
lean_dec(v_a_1679_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v___f_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1685_ = lean_st_ref_get(v_a_1683_);
lean_inc(v_a_1683_);
v___f_1686_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1686_, 0, v_a_1683_);
v___x_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
v___x_1689_ = lean_unsigned_to_nat(0u);
v___x_1690_ = 0;
v___x_1691_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1689_, v___x_1690_, v___x_1688_, v___f_1686_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed(lean_object* v_a_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v_a_1692_);
lean_dec(v_a_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close(lean_object* v_stream_1696_){
_start:
{
lean_object* v___f_1698_; lean_object* v___x_1699_; 
v___f_1698_ = ((lean_object*)(l_Std_Http_Body_Stream_close___closed__0));
v___x_1699_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_1696_, v___f_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object* v_stream_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_Http_Body_Stream_close(v_stream_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object* v_____do__lift_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v_closed_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_closed_1706_ = lean_ctor_get_uint8(v_____do__lift_1703_, sizeof(void*)*5);
v___x_1707_ = lean_box(v_closed_1706_);
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object* v_____do__lift_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v_____do__lift_1710_);
return v_res_1713_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__1(void){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Std_Internal_IO_Async_EAsync_instMonad(lean_box(0));
return v___x_1715_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__10(void){
_start:
{
lean_object* v___f_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___f_1731_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__0));
v___x_1732_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__9));
v___x_1733_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_1734_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_1734_, 0, lean_box(0));
lean_closure_set(v___x_1734_, 1, lean_box(0));
lean_closure_set(v___x_1734_, 2, lean_box(0));
lean_closure_set(v___x_1734_, 3, v___x_1733_);
lean_closure_set(v___x_1734_, 4, lean_box(0));
lean_closure_set(v___x_1734_, 5, lean_box(0));
lean_closure_set(v___x_1734_, 6, v___x_1732_);
lean_closure_set(v___x_1734_, 7, v___f_1731_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed(lean_object* v_stream_1735_){
_start:
{
lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; lean_object* v___x_26__overap_1741_; lean_object* v___x_1742_; 
v___x_1737_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_1738_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__4));
v___f_1739_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___x_1740_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__10, &l_Std_Http_Body_Stream_isClosed___closed__10_once, _init_l_Std_Http_Body_Stream_isClosed___closed__10);
v___x_26__overap_1741_ = l_Std_Mutex_atomically___redArg(v___x_1737_, v___f_1738_, v___f_1739_, v_stream_1735_, v___x_1740_);
v___x_1742_ = lean_apply_1(v___x_26__overap_1741_, lean_box(0));
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___boxed(lean_object* v_stream_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Std_Http_Body_Stream_isClosed(v_stream_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0(lean_object* v_____do__lift_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_knownSize_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_knownSize_1749_ = lean_ctor_get(v_____do__lift_1746_, 3);
lean_inc(v_knownSize_1749_);
v___x_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_knownSize_1749_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(lean_object* v_____do__lift_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v_____do__lift_1752_);
return v_res_1755_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_getKnownSize___closed__1(void){
_start:
{
lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___f_1757_ = ((lean_object*)(l_Std_Http_Body_Stream_getKnownSize___closed__0));
v___x_1758_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__9));
v___x_1759_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_1760_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_1760_, 0, lean_box(0));
lean_closure_set(v___x_1760_, 1, lean_box(0));
lean_closure_set(v___x_1760_, 2, lean_box(0));
lean_closure_set(v___x_1760_, 3, v___x_1759_);
lean_closure_set(v___x_1760_, 4, lean_box(0));
lean_closure_set(v___x_1760_, 5, lean_box(0));
lean_closure_set(v___x_1760_, 6, v___x_1758_);
lean_closure_set(v___x_1760_, 7, v___f_1757_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize(lean_object* v_stream_1761_){
_start:
{
lean_object* v___x_1763_; lean_object* v___f_1764_; lean_object* v___f_1765_; lean_object* v___x_1766_; lean_object* v___x_26__overap_1767_; lean_object* v___x_1768_; 
v___x_1763_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_1764_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__4));
v___f_1765_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___x_1766_ = lean_obj_once(&l_Std_Http_Body_Stream_getKnownSize___closed__1, &l_Std_Http_Body_Stream_getKnownSize___closed__1_once, _init_l_Std_Http_Body_Stream_getKnownSize___closed__1);
v___x_26__overap_1767_ = l_Std_Mutex_atomically___redArg(v___x_1763_, v___f_1764_, v___f_1765_, v_stream_1761_, v___x_1766_);
v___x_1768_ = lean_apply_1(v___x_26__overap_1767_, lean_box(0));
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___boxed(lean_object* v_stream_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0(lean_object* v_size_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; lean_object* v_pendingProducer_1776_; lean_object* v_pendingConsumer_1777_; lean_object* v_interestWaiter_1778_; uint8_t v_closed_1779_; lean_object* v_pendingIncompleteChunk_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1789_; 
v___x_1775_ = lean_st_ref_take(v___y_1773_);
v_pendingProducer_1776_ = lean_ctor_get(v___x_1775_, 0);
v_pendingConsumer_1777_ = lean_ctor_get(v___x_1775_, 1);
v_interestWaiter_1778_ = lean_ctor_get(v___x_1775_, 2);
v_closed_1779_ = lean_ctor_get_uint8(v___x_1775_, sizeof(void*)*5);
v_pendingIncompleteChunk_1780_ = lean_ctor_get(v___x_1775_, 4);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v___x_1775_, 3);
lean_dec(v_unused_1790_);
v___x_1782_ = v___x_1775_;
v_isShared_1783_ = v_isSharedCheck_1789_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_pendingIncompleteChunk_1780_);
lean_inc(v_interestWaiter_1778_);
lean_inc(v_pendingConsumer_1777_);
lean_inc(v_pendingProducer_1776_);
lean_dec(v___x_1775_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1789_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 3, v_size_1772_);
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_pendingProducer_1776_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_pendingConsumer_1777_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_interestWaiter_1778_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_size_1772_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_pendingIncompleteChunk_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*5, v_closed_1779_);
v___x_1785_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_st_ref_set(v___y_1773_, v___x_1785_);
v___x_1787_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_1787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(lean_object* v_size_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_1791_, v___y_1792_);
lean_dec(v___y_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize(lean_object* v_stream_1795_, lean_object* v_size_1796_){
_start:
{
lean_object* v___f_1798_; lean_object* v___x_1799_; lean_object* v___f_1800_; lean_object* v___f_1801_; lean_object* v___x_22__overap_1802_; lean_object* v___x_1803_; 
v___f_1798_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1798_, 0, v_size_1796_);
v___x_1799_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_1800_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__4));
v___f_1801_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___x_22__overap_1802_ = l_Std_Mutex_atomically___redArg(v___x_1799_, v___f_1800_, v___f_1801_, v_stream_1795_, v___f_1798_);
v___x_1803_ = lean_apply_1(v___x_22__overap_1802_, lean_box(0));
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___boxed(lean_object* v_stream_1804_, lean_object* v_size_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_1804_, v_size_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object* v_pendingProducer_1808_, lean_object* v_pendingConsumer_1809_, uint8_t v_closed_1810_, lean_object* v_knownSize_1811_, lean_object* v_pendingIncompleteChunk_1812_, lean_object* v_a_1813_, lean_object* v_x_1814_){
_start:
{
if (lean_obj_tag(v_x_1814_) == 0)
{
lean_object* v___x_1816_; 
lean_dec(v_pendingIncompleteChunk_1812_);
lean_dec(v_knownSize_1811_);
lean_dec(v_pendingConsumer_1809_);
lean_dec(v_pendingProducer_1808_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_x_1814_);
return v___x_1816_;
}
else
{
lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1827_; 
v_isSharedCheck_1827_ = !lean_is_exclusive(v_x_1814_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_x_1814_, 0);
lean_dec(v_unused_1828_);
v___x_1818_ = v_x_1814_;
v_isShared_1819_ = v_isSharedCheck_1827_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v_x_1814_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1827_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1821_, 0, v_pendingProducer_1808_);
lean_ctor_set(v___x_1821_, 1, v_pendingConsumer_1809_);
lean_ctor_set(v___x_1821_, 2, v___x_1820_);
lean_ctor_set(v___x_1821_, 3, v_knownSize_1811_);
lean_ctor_set(v___x_1821_, 4, v_pendingIncompleteChunk_1812_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*5, v_closed_1810_);
v___x_1822_ = lean_st_ref_set(v_a_1813_, v___x_1821_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1822_);
v___x_1824_ = v___x_1818_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object* v_pendingProducer_1829_, lean_object* v_pendingConsumer_1830_, lean_object* v_closed_1831_, lean_object* v_knownSize_1832_, lean_object* v_pendingIncompleteChunk_1833_, lean_object* v_a_1834_, lean_object* v_x_1835_, lean_object* v___y_1836_){
_start:
{
uint8_t v_closed_boxed_1837_; lean_object* v_res_1838_; 
v_closed_boxed_1837_ = lean_unbox(v_closed_1831_);
v_res_1838_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_1829_, v_pendingConsumer_1830_, v_closed_boxed_1837_, v_knownSize_1832_, v_pendingIncompleteChunk_1833_, v_a_1834_, v_x_1835_);
lean_dec(v_a_1834_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object* v_a_1839_, lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1850_; 
v_a_1842_ = lean_ctor_get(v_x_1840_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_x_1840_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1844_ = v_x_1840_;
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v_x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v_interestWaiter_1852_; 
v_a_1851_ = lean_ctor_get(v_x_1840_, 0);
lean_inc(v_a_1851_);
lean_dec_ref(v_x_1840_);
v_interestWaiter_1852_ = lean_ctor_get(v_a_1851_, 2);
lean_inc(v_interestWaiter_1852_);
if (lean_obj_tag(v_interestWaiter_1852_) == 1)
{
lean_object* v_pendingProducer_1853_; lean_object* v_pendingConsumer_1854_; uint8_t v_closed_1855_; lean_object* v_knownSize_1856_; lean_object* v_pendingIncompleteChunk_1857_; lean_object* v_val_1858_; uint8_t v___x_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___f_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; lean_object* v___x_1866_; 
v_pendingProducer_1853_ = lean_ctor_get(v_a_1851_, 0);
lean_inc(v_pendingProducer_1853_);
v_pendingConsumer_1854_ = lean_ctor_get(v_a_1851_, 1);
lean_inc(v_pendingConsumer_1854_);
v_closed_1855_ = lean_ctor_get_uint8(v_a_1851_, sizeof(void*)*5);
v_knownSize_1856_ = lean_ctor_get(v_a_1851_, 3);
lean_inc(v_knownSize_1856_);
v_pendingIncompleteChunk_1857_ = lean_ctor_get(v_a_1851_, 4);
lean_inc(v_pendingIncompleteChunk_1857_);
lean_dec(v_a_1851_);
v_val_1858_ = lean_ctor_get(v_interestWaiter_1852_, 0);
lean_inc(v_val_1858_);
lean_dec_ref(v_interestWaiter_1852_);
v___x_1859_ = 1;
v___x_1860_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1858_, v___x_1859_);
lean_dec(v_val_1858_);
v___x_1861_ = lean_box(v_closed_1855_);
lean_inc(v_a_1839_);
v___f_1862_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1862_, 0, v_pendingProducer_1853_);
lean_closure_set(v___f_1862_, 1, v_pendingConsumer_1854_);
lean_closure_set(v___f_1862_, 2, v___x_1861_);
lean_closure_set(v___f_1862_, 3, v_knownSize_1856_);
lean_closure_set(v___f_1862_, 4, v_pendingIncompleteChunk_1857_);
lean_closure_set(v___f_1862_, 5, v_a_1839_);
v___x_1863_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = 0;
v___x_1866_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1864_, v___x_1865_, v___x_1863_, v___f_1862_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; 
lean_dec(v_interestWaiter_1852_);
lean_dec(v_a_1851_);
v___x_1867_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_1867_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object* v_a_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_1868_, v_x_1869_);
lean_dec(v_a_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object* v_a_1872_){
_start:
{
lean_object* v___x_1874_; lean_object* v___f_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; lean_object* v___x_1880_; 
v___x_1874_ = lean_st_ref_get(v_a_1872_);
lean_inc(v_a_1872_);
v___f_1875_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1875_, 0, v_a_1872_);
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = 0;
v___x_1880_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1878_, v___x_1879_, v___x_1877_, v___f_1875_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object* v_a_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_1881_);
lean_dec(v_a_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object* v_promise_1884_, lean_object* v_x_1885_){
_start:
{
if (lean_obj_tag(v_x_1885_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_a_1887_ = lean_ctor_get(v_x_1885_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_x_1885_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1889_ = v_x_1885_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v_x_1885_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_io_promise_resolve(v_x_1885_, v_promise_1884_);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_1899_, lean_object* v_x_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(v_promise_1899_, v_x_1900_);
lean_dec(v_promise_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object* v_lose_1903_, lean_object* v___y_1904_, lean_object* v___f_1905_, lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v___f_1905_);
lean_dec_ref(v_lose_1903_);
v_a_1908_ = lean_ctor_get(v_x_1906_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_x_1906_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1910_ = v_x_1906_;
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v_x_1906_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
}
}
else
{
lean_object* v_a_1917_; uint8_t v___x_1918_; 
v_a_1917_ = lean_ctor_get(v_x_1906_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v_x_1906_);
v___x_1918_ = lean_unbox(v_a_1917_);
lean_dec(v_a_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
lean_dec_ref(v___f_1905_);
lean_inc(v___y_1904_);
v___x_1919_ = lean_apply_2(v_lose_1903_, v___y_1904_, lean_box(0));
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; 
lean_dec_ref(v_lose_1903_);
v___x_1920_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_1904_);
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = 0;
v___x_1923_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1921_, v___x_1922_, v___x_1920_, v___f_1905_);
return v___x_1923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object* v_lose_1924_, lean_object* v___y_1925_, lean_object* v___f_1926_, lean_object* v_x_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(v_lose_1924_, v___y_1925_, v___f_1926_, v_x_1927_);
lean_dec(v___y_1925_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object* v_w_1930_, lean_object* v_lose_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_finished_1934_; lean_object* v_promise_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___f_1938_; uint8_t v___y_1940_; uint8_t v___x_1950_; 
v_finished_1934_ = lean_ctor_get(v_w_1930_, 0);
lean_inc(v_finished_1934_);
v_promise_1935_ = lean_ctor_get(v_w_1930_, 1);
lean_inc(v_promise_1935_);
lean_dec_ref(v_w_1930_);
v___x_1936_ = lean_st_ref_take(v_finished_1934_);
v___f_1937_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1937_, 0, v_promise_1935_);
lean_inc(v___y_1932_);
v___f_1938_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1938_, 0, v_lose_1931_);
lean_closure_set(v___f_1938_, 1, v___y_1932_);
lean_closure_set(v___f_1938_, 2, v___f_1937_);
v___x_1950_ = lean_unbox(v___x_1936_);
lean_dec(v___x_1936_);
if (v___x_1950_ == 0)
{
uint8_t v___x_1951_; 
v___x_1951_ = 1;
v___y_1940_ = v___x_1951_;
goto v___jp_1939_;
}
else
{
uint8_t v___x_1952_; 
v___x_1952_ = 0;
v___y_1940_ = v___x_1952_;
goto v___jp_1939_;
}
v___jp_1939_:
{
uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1941_ = 1;
v___x_1942_ = lean_box(v___x_1941_);
v___x_1943_ = lean_st_ref_set(v_finished_1934_, v___x_1942_);
lean_dec(v_finished_1934_);
v___x_1944_ = lean_box(v___y_1940_);
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = 0;
v___x_1949_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1947_, v___x_1948_, v___x_1946_, v___f_1938_);
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object* v_w_1953_, lean_object* v_lose_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_1953_, v_lose_1954_, v___y_1955_);
lean_dec(v___y_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___lam__0(lean_object* v_x_1958_){
_start:
{
uint8_t v___y_1961_; 
if (lean_obj_tag(v_x_1958_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_a_1965_ = lean_ctor_get(v_x_1958_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_x_1958_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v_x_1958_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v_x_1958_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v_pendingProducer_1975_; 
v_a_1974_ = lean_ctor_get(v_x_1958_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v_x_1958_);
v_pendingProducer_1975_ = lean_ctor_get(v_a_1974_, 0);
if (lean_obj_tag(v_pendingProducer_1975_) == 0)
{
uint8_t v_closed_1976_; 
v_closed_1976_ = lean_ctor_get_uint8(v_a_1974_, sizeof(void*)*5);
lean_dec(v_a_1974_);
v___y_1961_ = v_closed_1976_;
goto v___jp_1960_;
}
else
{
uint8_t v___x_1977_; 
lean_dec(v_a_1974_);
v___x_1977_ = 1;
v___y_1961_ = v___x_1977_;
goto v___jp_1960_;
}
}
v___jp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_box(v___y_1961_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___lam__0___boxed(lean_object* v_x_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___lam__0(v_x_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2(lean_object* v_a_1982_){
_start:
{
lean_object* v___x_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1984_ = lean_st_ref_get(v_a_1982_);
v___f_1985_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___closed__0));
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = 0;
v___x_1990_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1988_, v___x_1989_, v___x_1987_, v___f_1985_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2___boxed(lean_object* v_a_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2(v_a_1991_);
lean_dec(v_a_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object* v_x_1994_){
_start:
{
if (lean_obj_tag(v_x_1994_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_a_1996_ = lean_ctor_get(v_x_1994_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_x_1994_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1998_ = v_x_1994_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v_x_1994_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2014_; 
v_a_2005_ = lean_ctor_get(v_x_1994_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_x_1994_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2007_ = v_x_1994_;
v_isShared_2008_ = v_isSharedCheck_2014_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v_x_1994_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2014_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2009_, 0, v_a_2005_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2009_);
v___x_2011_ = v___x_2007_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
return v___x_2012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object* v_x_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_x_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object* v___y_2018_, lean_object* v_x_2019_){
_start:
{
if (lean_obj_tag(v_x_2019_) == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_x_2019_);
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; 
lean_dec_ref(v_x_2019_);
v___x_2022_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_2018_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object* v___y_2023_, lean_object* v_x_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_2023_, v_x_2024_);
lean_dec(v___y_2023_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object* v_waiter_2027_, lean_object* v_pendingProducer_2028_, lean_object* v_interestWaiter_2029_, uint8_t v_closed_2030_, lean_object* v_knownSize_2031_, lean_object* v_pendingIncompleteChunk_2032_, uint8_t v_a_2033_, lean_object* v_____r_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___f_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v_waiter_2027_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2039_, 0, v_pendingProducer_2028_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
lean_ctor_set(v___x_2039_, 2, v_interestWaiter_2029_);
lean_ctor_set(v___x_2039_, 3, v_knownSize_2031_);
lean_ctor_set(v___x_2039_, 4, v_pendingIncompleteChunk_2032_);
lean_ctor_set_uint8(v___x_2039_, sizeof(void*)*5, v_closed_2030_);
v___x_2040_ = lean_st_ref_set(v___y_2035_, v___x_2039_);
lean_inc(v___y_2035_);
v___f_2041_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2041_, 0, v___y_2035_);
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2044_, v_a_2033_, v___x_2043_, v___f_2041_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object* v_waiter_2046_, lean_object* v_pendingProducer_2047_, lean_object* v_interestWaiter_2048_, lean_object* v_closed_2049_, lean_object* v_knownSize_2050_, lean_object* v_pendingIncompleteChunk_2051_, lean_object* v_a_2052_, lean_object* v_____r_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
uint8_t v_closed_boxed_2056_; uint8_t v_a_6169__boxed_2057_; lean_object* v_res_2058_; 
v_closed_boxed_2056_ = lean_unbox(v_closed_2049_);
v_a_6169__boxed_2057_ = lean_unbox(v_a_2052_);
v_res_2058_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v_waiter_2046_, v_pendingProducer_2047_, v_interestWaiter_2048_, v_closed_boxed_2056_, v_knownSize_2050_, v_pendingIncompleteChunk_2051_, v_a_6169__boxed_2057_, v_____r_2053_, v___y_2054_);
lean_dec(v___y_2054_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object* v_waiter_2063_, uint8_t v_a_2064_, lean_object* v___y_2065_, lean_object* v_x_2066_){
_start:
{
if (lean_obj_tag(v_x_2066_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v_waiter_2063_);
v_a_2068_ = lean_ctor_get(v_x_2066_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_x_2066_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2070_ = v_x_2066_;
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v_x_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
return v___x_2074_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v_pendingProducer_2078_; lean_object* v_pendingConsumer_2079_; lean_object* v_interestWaiter_2080_; uint8_t v_closed_2081_; lean_object* v_knownSize_2082_; lean_object* v_pendingIncompleteChunk_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___f_2086_; 
v_a_2077_ = lean_ctor_get(v_x_2066_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v_x_2066_);
v_pendingProducer_2078_ = lean_ctor_get(v_a_2077_, 0);
lean_inc_n(v_pendingProducer_2078_, 2);
v_pendingConsumer_2079_ = lean_ctor_get(v_a_2077_, 1);
lean_inc(v_pendingConsumer_2079_);
v_interestWaiter_2080_ = lean_ctor_get(v_a_2077_, 2);
lean_inc_n(v_interestWaiter_2080_, 2);
v_closed_2081_ = lean_ctor_get_uint8(v_a_2077_, sizeof(void*)*5);
v_knownSize_2082_ = lean_ctor_get(v_a_2077_, 3);
lean_inc_n(v_knownSize_2082_, 2);
v_pendingIncompleteChunk_2083_ = lean_ctor_get(v_a_2077_, 4);
lean_inc_n(v_pendingIncompleteChunk_2083_, 2);
lean_dec(v_a_2077_);
v___x_2084_ = lean_box(v_closed_2081_);
v___x_2085_ = lean_box(v_a_2064_);
lean_inc_ref(v_waiter_2063_);
v___f_2086_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__2___boxed), 10, 7);
lean_closure_set(v___f_2086_, 0, v_waiter_2063_);
lean_closure_set(v___f_2086_, 1, v_pendingProducer_2078_);
lean_closure_set(v___f_2086_, 2, v_interestWaiter_2080_);
lean_closure_set(v___f_2086_, 3, v___x_2084_);
lean_closure_set(v___f_2086_, 4, v_knownSize_2082_);
lean_closure_set(v___f_2086_, 5, v_pendingIncompleteChunk_2083_);
lean_closure_set(v___f_2086_, 6, v___x_2085_);
if (lean_obj_tag(v_pendingConsumer_2079_) == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec_ref(v___f_2086_);
v___x_2087_ = lean_box(0);
v___x_2088_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v_waiter_2063_, v_pendingProducer_2078_, v_interestWaiter_2080_, v_closed_2081_, v_knownSize_2082_, v_pendingIncompleteChunk_2083_, v_a_2064_, v___x_2087_, v___y_2065_);
return v___x_2088_;
}
else
{
lean_object* v___f_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_dec_ref(v_pendingConsumer_2079_);
lean_dec(v_pendingIncompleteChunk_2083_);
lean_dec(v_knownSize_2082_);
lean_dec(v_interestWaiter_2080_);
lean_dec(v_pendingProducer_2078_);
lean_dec_ref(v_waiter_2063_);
lean_inc(v___y_2065_);
v___f_2089_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2089_, 0, v___f_2086_);
lean_closure_set(v___f_2089_, 1, v___y_2065_);
v___x_2090_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__1));
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2091_, v_a_2064_, v___x_2090_, v___f_2089_);
return v___x_2092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object* v_waiter_2093_, lean_object* v_a_2094_, lean_object* v___y_2095_, lean_object* v_x_2096_, lean_object* v___y_2097_){
_start:
{
uint8_t v_a_6210__boxed_2098_; lean_object* v_res_2099_; 
v_a_6210__boxed_2098_ = lean_unbox(v_a_2094_);
v_res_2099_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v_waiter_2093_, v_a_6210__boxed_2098_, v___y_2095_, v_x_2096_);
lean_dec(v___y_2095_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object* v___x_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2100_);
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object* v___x_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v___x_2105_, v___y_2106_);
lean_dec(v___y_2106_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object* v___y_2111_, lean_object* v_waiter_2112_, lean_object* v_x_2113_){
_start:
{
if (lean_obj_tag(v_x_2113_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v_waiter_2112_);
v_a_2115_ = lean_ctor_get(v_x_2113_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2117_ = v_x_2113_;
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v_x_2113_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2140_; 
v_a_2124_ = lean_ctor_get(v_x_2113_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2126_ = v_x_2113_;
v_isShared_2127_ = v_isSharedCheck_2140_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v_x_2113_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2140_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
uint8_t v___x_2128_; 
v___x_2128_ = lean_unbox(v_a_2124_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___f_2130_; lean_object* v___x_2132_; 
v___x_2129_ = lean_st_ref_get(v___y_2111_);
lean_inc(v___y_2111_);
lean_inc(v_a_2124_);
v___f_2130_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(v___f_2130_, 0, v_waiter_2112_);
lean_closure_set(v___f_2130_, 1, v_a_2124_);
lean_closure_set(v___f_2130_, 2, v___y_2111_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2129_);
v___x_2132_ = v___x_2126_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2129_);
v___x_2132_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
v___x_2134_ = lean_unsigned_to_nat(0u);
v___x_2135_ = lean_unbox(v_a_2124_);
lean_dec(v_a_2124_);
v___x_2136_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2134_, v___x_2135_, v___x_2133_, v___f_2130_);
return v___x_2136_;
}
}
else
{
lean_object* v___f_2138_; lean_object* v___x_2139_; 
lean_del_object(v___x_2126_);
lean_dec(v_a_2124_);
v___f_2138_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__5___closed__0));
v___x_2139_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_waiter_2112_, v___f_2138_, v___y_2111_);
return v___x_2139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object* v___y_2141_, lean_object* v_waiter_2142_, lean_object* v_x_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_2141_, v_waiter_2142_, v_x_2143_);
lean_dec(v___y_2141_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object* v___y_2146_, lean_object* v___f_2147_, lean_object* v_x_2148_){
_start:
{
if (lean_obj_tag(v_x_2148_) == 0)
{
lean_object* v___x_2150_; 
lean_dec_ref(v___f_2147_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_x_2148_);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v_x_2148_);
v___x_2151_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2(v___y_2146_);
v___x_2152_ = lean_unsigned_to_nat(0u);
v___x_2153_ = 0;
v___x_2154_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2152_, v___x_2153_, v___x_2151_, v___f_2147_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object* v___y_2155_, lean_object* v___f_2156_, lean_object* v_x_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v___y_2155_, v___f_2156_, v_x_2157_);
lean_dec(v___y_2155_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object* v_waiter_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v___x_2163_; lean_object* v___f_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; 
v___x_2163_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2161_);
lean_inc_n(v___y_2161_, 2);
v___f_2164_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2164_, 0, v___y_2161_);
lean_closure_set(v___f_2164_, 1, v_waiter_2160_);
v___f_2165_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2165_, 0, v___y_2161_);
lean_closure_set(v___f_2165_, 1, v___f_2164_);
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = 0;
v___x_2168_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2166_, v___x_2167_, v___x_2163_, v___f_2165_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object* v_waiter_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_waiter_2169_, v___y_2170_);
lean_dec(v___y_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__8(lean_object* v_stream_2173_, lean_object* v_waiter_2174_){
_start:
{
lean_object* v___f_2176_; lean_object* v___x_2177_; 
v___f_2176_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2176_, 0, v_waiter_2174_);
v___x_2177_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2173_, v___f_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__8___boxed(lean_object* v_stream_2178_, lean_object* v_waiter_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Std_Http_Body_Stream_recvSelector___lam__8(v_stream_2178_, v_waiter_2179_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__9(lean_object* v___y_2186_, lean_object* v___f_2187_, lean_object* v_x_2188_){
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
lean_object* v_a_2199_; uint8_t v___x_2200_; 
v_a_2199_ = lean_ctor_get(v_x_2188_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v_x_2188_);
v___x_2200_ = lean_unbox(v_a_2199_);
lean_dec(v_a_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; 
lean_dec_ref(v___f_2187_);
v___x_2201_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__9___closed__1));
return v___x_2201_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2186_);
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = 0;
v___x_2205_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2203_, v___x_2204_, v___x_2202_, v___f_2187_);
return v___x_2205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__9___boxed(lean_object* v___y_2206_, lean_object* v___f_2207_, lean_object* v_x_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Std_Http_Body_Stream_recvSelector___lam__9(v___y_2206_, v___f_2207_, v_x_2208_);
lean_dec(v___y_2206_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__10(lean_object* v___y_2211_, lean_object* v___f_2212_, lean_object* v_x_2213_){
_start:
{
if (lean_obj_tag(v_x_2213_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v___f_2212_);
v_a_2215_ = lean_ctor_get(v_x_2213_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_x_2213_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2217_ = v_x_2213_;
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v_x_2213_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; 
lean_dec_ref(v_x_2213_);
v___x_2224_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_recvSelector_spec__2(v___y_2211_);
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = 0;
v___x_2227_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2225_, v___x_2226_, v___x_2224_, v___f_2212_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__10___boxed(lean_object* v___y_2228_, lean_object* v___f_2229_, lean_object* v_x_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Std_Http_Body_Stream_recvSelector___lam__10(v___y_2228_, v___f_2229_, v_x_2230_);
lean_dec(v___y_2228_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__11(lean_object* v___f_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; lean_object* v___f_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; lean_object* v___x_2241_; 
v___x_2236_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2234_);
lean_inc_n(v___y_2234_, 2);
v___f_2237_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__9___boxed), 4, 2);
lean_closure_set(v___f_2237_, 0, v___y_2234_);
lean_closure_set(v___f_2237_, 1, v___f_2233_);
v___f_2238_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__10___boxed), 4, 2);
lean_closure_set(v___f_2238_, 0, v___y_2234_);
lean_closure_set(v___f_2238_, 1, v___f_2237_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = 0;
v___x_2241_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2239_, v___x_2240_, v___x_2236_, v___f_2238_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__11___boxed(lean_object* v___f_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Std_Http_Body_Stream_recvSelector___lam__11(v___f_2242_, v___y_2243_);
lean_dec(v___y_2243_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object* v_stream_2250_){
_start:
{
lean_object* v___f_2251_; lean_object* v___f_2252_; lean_object* v___f_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___f_2251_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__1));
lean_inc_ref_n(v_stream_2250_, 2);
v___f_2252_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__8___boxed), 3, 1);
lean_closure_set(v___f_2252_, 0, v_stream_2250_);
v___f_2253_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__2));
v___x_2254_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2254_, 0, lean_box(0));
lean_closure_set(v___x_2254_, 1, lean_box(0));
lean_closure_set(v___x_2254_, 2, v_stream_2250_);
lean_closure_set(v___x_2254_, 3, v___f_2253_);
v___x_2255_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2255_, 0, lean_box(0));
lean_closure_set(v___x_2255_, 1, lean_box(0));
lean_closure_set(v___x_2255_, 2, v_stream_2250_);
lean_closure_set(v___x_2255_, 3, v___f_2251_);
v___x_2256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___f_2252_);
lean_ctor_set(v___x_2256_, 2, v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(lean_object* v_step_2257_, lean_object* v_acc_2258_, lean_object* v___f_2259_, lean_object* v_x_2260_){
_start:
{
if (lean_obj_tag(v_x_2260_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2270_; 
lean_dec_ref(v___f_2259_);
lean_dec(v_acc_2258_);
lean_dec_ref(v_step_2257_);
v_a_2262_ = lean_ctor_get(v_x_2260_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_x_2260_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2264_ = v_x_2260_;
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v_x_2260_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2284_; 
v_a_2271_ = lean_ctor_get(v_x_2260_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_x_2260_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2273_ = v_x_2260_;
v_isShared_2274_ = v_isSharedCheck_2284_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v_x_2260_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2284_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
if (lean_obj_tag(v_a_2271_) == 1)
{
lean_object* v_val_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; 
lean_del_object(v___x_2273_);
v_val_2275_ = lean_ctor_get(v_a_2271_, 0);
lean_inc(v_val_2275_);
lean_dec_ref(v_a_2271_);
v___x_2276_ = lean_apply_3(v_step_2257_, v_val_2275_, v_acc_2258_, lean_box(0));
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = 0;
v___x_2279_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2277_, v___x_2278_, v___x_2276_, v___f_2259_);
return v___x_2279_;
}
else
{
lean_object* v___x_2281_; 
lean_dec(v_a_2271_);
lean_dec_ref(v___f_2259_);
lean_dec_ref(v_step_2257_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v_acc_2258_);
v___x_2281_ = v___x_2273_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_acc_2258_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed(lean_object* v_step_2285_, lean_object* v_acc_2286_, lean_object* v___f_2287_, lean_object* v_x_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(v_step_2285_, v_acc_2286_, v___f_2287_, v_x_2288_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(lean_object* v_step_2291_, lean_object* v_stream_2292_, lean_object* v_x_2293_){
_start:
{
if (lean_obj_tag(v_x_2293_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v_stream_2292_);
lean_dec_ref(v_step_2291_);
v_a_2295_ = lean_ctor_get(v_x_2293_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_x_2293_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2297_ = v_x_2293_;
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v_x_2293_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2321_; 
v_a_2304_ = lean_ctor_get(v_x_2293_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_x_2293_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2306_ = v_x_2293_;
v_isShared_2307_ = v_isSharedCheck_2321_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v_x_2293_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2321_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
if (lean_obj_tag(v_a_2304_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v_stream_2292_);
lean_dec_ref(v_step_2291_);
v_a_2308_ = lean_ctor_get(v_a_2304_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_a_2304_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2310_ = v_a_2304_;
v_isShared_2311_ = v_isSharedCheck_2318_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v_a_2304_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2318_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v_a_2308_);
v___x_2313_ = v___x_2306_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2315_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2313_);
v___x_2315_ = v___x_2310_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
lean_del_object(v___x_2306_);
v_a_2319_ = lean_ctor_get(v_a_2304_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v_a_2304_);
v___x_2320_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2291_, v_stream_2292_, v_a_2319_);
return v___x_2320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed(lean_object* v_step_2322_, lean_object* v_stream_2323_, lean_object* v_x_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(v_step_2322_, v_stream_2323_, v_x_2324_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(lean_object* v_step_2327_, lean_object* v_stream_2328_, lean_object* v_acc_2329_){
_start:
{
lean_object* v___x_2331_; lean_object* v___f_2332_; lean_object* v___f_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; 
lean_inc_ref(v_stream_2328_);
v___x_2331_ = l_Std_Http_Body_Stream_recv(v_stream_2328_);
lean_inc_ref(v_step_2327_);
v___f_2332_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2332_, 0, v_step_2327_);
lean_closure_set(v___f_2332_, 1, v_stream_2328_);
v___f_2333_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2333_, 0, v_step_2327_);
lean_closure_set(v___f_2333_, 1, v_acc_2329_);
lean_closure_set(v___f_2333_, 2, v___f_2332_);
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = 0;
v___x_2336_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2334_, v___x_2335_, v___x_2331_, v___f_2333_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___boxed(lean_object* v_step_2337_, lean_object* v_stream_2338_, lean_object* v_acc_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2337_, v_stream_2338_, v_acc_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(lean_object* v_00_u03b2_2342_, lean_object* v_step_2343_, lean_object* v_stream_2344_, lean_object* v_acc_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2343_, v_stream_2344_, v_acc_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___boxed(lean_object* v_00_u03b2_2348_, lean_object* v_step_2349_, lean_object* v_stream_2350_, lean_object* v_acc_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(v_00_u03b2_2348_, v_step_2349_, v_stream_2350_, v_acc_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_2354_, lean_object* v_acc_2355_, lean_object* v_step_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2356_, v_stream_2354_, v_acc_2355_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_2359_, lean_object* v_acc_2360_, lean_object* v_step_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_2359_, v_acc_2360_, v_step_2361_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_2364_, lean_object* v_stream_2365_, lean_object* v_acc_2366_, lean_object* v_step_2367_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_2367_, v_stream_2365_, v_acc_2366_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_2370_, lean_object* v_stream_2371_, lean_object* v_acc_2372_, lean_object* v_step_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_2370_, v_stream_2371_, v_acc_2372_, v_step_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(lean_object* v_x_2376_){
_start:
{
if (lean_obj_tag(v_x_2376_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2386_; 
v_a_2378_ = lean_ctor_get(v_x_2376_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_x_2376_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2380_ = v_x_2376_;
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v_x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
return v___x_2384_;
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2397_; 
v_a_2387_ = lean_ctor_get(v_x_2376_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_x_2376_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2389_ = v_x_2376_;
v_isShared_2390_ = v_isSharedCheck_2397_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v_x_2376_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2397_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v_token_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
v_token_2391_ = lean_ctor_get(v_a_2387_, 1);
lean_inc_ref(v_token_2391_);
lean_dec(v_a_2387_);
v___x_2392_ = l_Std_CancellationToken_selector(v_token_2391_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2392_);
v___x_2394_ = v___x_2389_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_x_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(v_x_2398_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(lean_object* v___y_2401_){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___y_2401_);
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed(lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(v___y_2405_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(lean_object* v_x_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1));
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed(lean_object* v_x_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(v_x_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(lean_object* v_step_2414_, lean_object* v_acc_2415_, lean_object* v_a_2416_, lean_object* v___f_2417_, lean_object* v_x_2418_){
_start:
{
if (lean_obj_tag(v_x_2418_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___f_2417_);
lean_dec(v_acc_2415_);
lean_dec_ref(v_step_2414_);
v_a_2420_ = lean_ctor_get(v_x_2418_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_x_2418_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2422_ = v_x_2418_;
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v_x_2418_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2442_; 
v_a_2429_ = lean_ctor_get(v_x_2418_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_x_2418_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2431_ = v_x_2418_;
v_isShared_2432_ = v_isSharedCheck_2442_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v_x_2418_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2442_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
if (lean_obj_tag(v_a_2429_) == 1)
{
lean_object* v_val_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; 
lean_del_object(v___x_2431_);
v_val_2433_ = lean_ctor_get(v_a_2429_, 0);
lean_inc(v_val_2433_);
lean_dec_ref(v_a_2429_);
lean_inc_ref(v_a_2416_);
v___x_2434_ = lean_apply_4(v_step_2414_, v_val_2433_, v_acc_2415_, v_a_2416_, lean_box(0));
v___x_2435_ = lean_unsigned_to_nat(0u);
v___x_2436_ = 0;
v___x_2437_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2435_, v___x_2436_, v___x_2434_, v___f_2417_);
return v___x_2437_;
}
else
{
lean_object* v___x_2439_; 
lean_dec(v_a_2429_);
lean_dec_ref(v___f_2417_);
lean_dec_ref(v_step_2414_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v_acc_2415_);
v___x_2439_ = v___x_2431_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_acc_2415_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed(lean_object* v_step_2443_, lean_object* v_acc_2444_, lean_object* v_a_2445_, lean_object* v___f_2446_, lean_object* v_x_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(v_step_2443_, v_acc_2444_, v_a_2445_, v___f_2446_, v_x_2447_);
lean_dec_ref(v_a_2445_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(lean_object* v_stream_2450_, lean_object* v___f_2451_, lean_object* v___f_2452_, lean_object* v___f_2453_, lean_object* v_x_2454_){
_start:
{
if (lean_obj_tag(v_x_2454_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2452_);
lean_dec_ref(v___f_2451_);
lean_dec_ref(v_stream_2450_);
v_a_2456_ = lean_ctor_get(v_x_2454_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_x_2454_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2458_ = v_x_2454_;
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v_x_2454_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; 
v_a_2465_ = lean_ctor_get(v_x_2454_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v_x_2454_);
v___x_2466_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2450_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v___f_2451_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_a_2465_);
lean_ctor_set(v___x_2468_, 1, v___f_2452_);
v___x_2469_ = lean_unsigned_to_nat(2u);
v___x_2470_ = lean_mk_empty_array_with_capacity(v___x_2469_);
v___x_2471_ = lean_array_push(v___x_2470_, v___x_2467_);
v___x_2472_ = lean_array_push(v___x_2471_, v___x_2468_);
v___x_2473_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = 0;
v___x_2476_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2474_, v___x_2475_, v___x_2473_, v___f_2453_);
return v___x_2476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed(lean_object* v_stream_2477_, lean_object* v___f_2478_, lean_object* v___f_2479_, lean_object* v___f_2480_, lean_object* v_x_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(v_stream_2477_, v___f_2478_, v___f_2479_, v___f_2480_, v_x_2481_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed(lean_object* v_step_2487_, lean_object* v_stream_2488_, lean_object* v_a_2489_, lean_object* v_x_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(v_step_2487_, v_stream_2488_, v_a_2489_, v_x_2490_);
lean_dec_ref(v_a_2489_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(lean_object* v_step_2493_, lean_object* v_stream_2494_, lean_object* v_acc_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v___f_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___f_2504_; lean_object* v___f_2505_; lean_object* v___f_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; 
v___f_2498_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0));
lean_inc_ref_n(v_a_2496_, 3);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_a_2496_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
v___x_2501_ = lean_unsigned_to_nat(0u);
v___x_2502_ = 0;
v___x_2503_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2501_, v___x_2502_, v___x_2500_, v___f_2498_);
v___f_2504_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1));
v___f_2505_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2));
lean_inc_ref(v_stream_2494_);
lean_inc_ref(v_step_2493_);
v___f_2506_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2506_, 0, v_step_2493_);
lean_closure_set(v___f_2506_, 1, v_stream_2494_);
lean_closure_set(v___f_2506_, 2, v_a_2496_);
v___f_2507_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_2507_, 0, v_step_2493_);
lean_closure_set(v___f_2507_, 1, v_acc_2495_);
lean_closure_set(v___f_2507_, 2, v_a_2496_);
lean_closure_set(v___f_2507_, 3, v___f_2506_);
v___f_2508_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_2508_, 0, v_stream_2494_);
lean_closure_set(v___f_2508_, 1, v___f_2504_);
lean_closure_set(v___f_2508_, 2, v___f_2505_);
lean_closure_set(v___f_2508_, 3, v___f_2507_);
v___x_2509_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2501_, v___x_2502_, v___x_2503_, v___f_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(lean_object* v_step_2510_, lean_object* v_stream_2511_, lean_object* v_a_2512_, lean_object* v_x_2513_){
_start:
{
if (lean_obj_tag(v_x_2513_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2523_; 
lean_dec_ref(v_stream_2511_);
lean_dec_ref(v_step_2510_);
v_a_2515_ = lean_ctor_get(v_x_2513_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_x_2513_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2517_ = v_x_2513_;
v_isShared_2518_ = v_isSharedCheck_2523_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v_x_2513_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2523_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2541_; 
v_a_2524_ = lean_ctor_get(v_x_2513_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_x_2513_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2526_ = v_x_2513_;
v_isShared_2527_ = v_isSharedCheck_2541_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v_x_2513_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2541_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
if (lean_obj_tag(v_a_2524_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_stream_2511_);
lean_dec_ref(v_step_2510_);
v_a_2528_ = lean_ctor_get(v_a_2524_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_a_2524_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2530_ = v_a_2524_;
v_isShared_2531_ = v_isSharedCheck_2538_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v_a_2524_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2538_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v_a_2528_);
v___x_2533_ = v___x_2526_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2535_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2533_);
v___x_2535_ = v___x_2530_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2540_; 
lean_del_object(v___x_2526_);
v_a_2539_ = lean_ctor_get(v_a_2524_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v_a_2524_);
v___x_2540_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2510_, v_stream_2511_, v_a_2539_, v_a_2512_);
return v___x_2540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___boxed(lean_object* v_step_2542_, lean_object* v_stream_2543_, lean_object* v_acc_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2542_, v_stream_2543_, v_acc_2544_, v_a_2545_);
lean_dec_ref(v_a_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(lean_object* v_00_u03b2_2548_, lean_object* v_step_2549_, lean_object* v_stream_2550_, lean_object* v_acc_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2549_, v_stream_2550_, v_acc_2551_, v_a_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___boxed(lean_object* v_00_u03b2_2555_, lean_object* v_step_2556_, lean_object* v_stream_2557_, lean_object* v_acc_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(v_00_u03b2_2555_, v_step_2556_, v_stream_2557_, v_acc_2558_, v_a_2559_);
lean_dec_ref(v_a_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_2562_, lean_object* v_acc_2563_, lean_object* v_step_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2564_, v_stream_2562_, v_acc_2563_, v_a_2565_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_2568_, lean_object* v_acc_2569_, lean_object* v_step_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_2568_, v_acc_2569_, v_step_2570_, v_a_2571_);
lean_dec_ref(v_a_2571_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_2574_, lean_object* v_stream_2575_, lean_object* v_acc_2576_, lean_object* v_step_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_2577_, v_stream_2575_, v_acc_2576_, v_a_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_2581_, lean_object* v_stream_2582_, lean_object* v_acc_2583_, lean_object* v_step_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_2581_, v_stream_2582_, v_acc_2583_, v_step_2584_, v_a_2585_);
lean_dec_ref(v_a_2585_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v_x_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1));
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v_x_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v_x_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___y_2596_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed(lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(v___y_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(lean_object* v_x_2603_){
_start:
{
if (lean_obj_tag(v_x_2603_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2613_; 
v_a_2605_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2607_ = v_x_2603_;
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v_x_2603_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
return v___x_2611_;
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2624_; 
v_a_2614_ = lean_ctor_get(v_x_2603_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2616_ = v_x_2603_;
v_isShared_2617_ = v_isSharedCheck_2624_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v_x_2603_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2624_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_token_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v_token_2618_ = lean_ctor_get(v_a_2614_, 1);
lean_inc_ref(v_token_2618_);
lean_dec(v_a_2614_);
v___x_2619_ = l_Std_CancellationToken_selector(v_token_2618_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed(lean_object* v_x_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(v_x_2625_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v_stream_2628_, lean_object* v___f_2629_, lean_object* v___f_2630_, lean_object* v_x_2631_){
_start:
{
if (lean_obj_tag(v_x_2631_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref(v___f_2630_);
lean_dec_ref(v___f_2629_);
lean_dec_ref(v_stream_2628_);
v_a_2633_ = lean_ctor_get(v_x_2631_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_x_2631_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2635_ = v_x_2631_;
v_isShared_2636_ = v_isSharedCheck_2641_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v_x_2631_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2641_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
return v___x_2639_;
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_a_2642_ = lean_ctor_get(v_x_2631_, 0);
lean_inc(v_a_2642_);
lean_dec_ref(v_x_2631_);
v___x_2643_ = l_Std_Http_Body_Stream_recvSelector(v_stream_2628_);
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
lean_ctor_set(v___x_2644_, 1, v___f_2629_);
v___x_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2645_, 0, v_a_2642_);
lean_ctor_set(v___x_2645_, 1, v___f_2630_);
v___x_2646_ = lean_unsigned_to_nat(2u);
v___x_2647_ = lean_mk_empty_array_with_capacity(v___x_2646_);
v___x_2648_ = lean_array_push(v___x_2647_, v___x_2644_);
v___x_2649_ = lean_array_push(v___x_2648_, v___x_2645_);
v___x_2650_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v___x_2649_);
return v___x_2650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v_stream_2651_, lean_object* v___f_2652_, lean_object* v___f_2653_, lean_object* v_x_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_2651_, v___f_2652_, v___f_2653_, v_x_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(lean_object* v___f_2657_, lean_object* v___f_2658_, lean_object* v___f_2659_, lean_object* v_stream_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; 
lean_inc_ref(v___y_2661_);
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___y_2661_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = 0;
v___x_2667_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2665_, v___x_2666_, v___x_2664_, v___f_2657_);
v___f_2668_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2668_, 0, v_stream_2660_);
lean_closure_set(v___f_2668_, 1, v___f_2658_);
lean_closure_set(v___f_2668_, 2, v___f_2659_);
v___x_2669_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2665_, v___x_2666_, v___x_2667_, v___f_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4___boxed(lean_object* v___f_2670_, lean_object* v___f_2671_, lean_object* v___f_2672_, lean_object* v_stream_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(v___f_2670_, v___f_2671_, v___f_2672_, v_stream_2673_, v___y_2674_);
lean_dec_ref(v___y_2674_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v_toPure_2687_, lean_object* v_result_2688_, lean_object* v_maximumSize_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_stream_2693_, lean_object* v_toBind_2694_, lean_object* v_____do__lift_2695_){
_start:
{
if (lean_obj_tag(v_____do__lift_2695_) == 0)
{
lean_object* v___x_2696_; 
lean_dec(v_toBind_2694_);
lean_dec_ref(v_stream_2693_);
lean_dec(v_inst_2692_);
lean_dec_ref(v_inst_2691_);
lean_dec_ref(v_inst_2690_);
lean_dec(v_maximumSize_2689_);
v___x_2696_ = lean_apply_2(v_toPure_2687_, lean_box(0), v_result_2688_);
return v___x_2696_;
}
else
{
lean_object* v_val_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v_toPure_2687_);
v_val_2697_ = lean_ctor_get(v_____do__lift_2695_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_____do__lift_2695_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2699_ = v_____do__lift_2695_;
v_isShared_2700_ = v_isSharedCheck_2728_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_val_2697_);
lean_dec(v_____do__lift_2695_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2728_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_data_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; lean_object* v_result_2706_; 
v_data_2701_ = lean_ctor_get(v_val_2697_, 0);
lean_inc_ref(v_data_2701_);
lean_dec(v_val_2697_);
v___x_2702_ = lean_unsigned_to_nat(0u);
v___x_2703_ = lean_byte_array_size(v_result_2688_);
v___x_2704_ = lean_byte_array_size(v_data_2701_);
v___x_2705_ = 0;
v_result_2706_ = lean_byte_array_copy_slice(v_data_2701_, v___x_2702_, v_result_2688_, v___x_2703_, v___x_2704_, v___x_2705_);
lean_dec_ref(v_data_2701_);
if (lean_obj_tag(v_maximumSize_2689_) == 1)
{
lean_object* v_val_2707_; lean_object* v___x_2708_; uint64_t v___x_2709_; uint64_t v___x_2710_; uint8_t v___x_2711_; 
v_val_2707_ = lean_ctor_get(v_maximumSize_2689_, 0);
v___x_2708_ = lean_byte_array_size(v_result_2706_);
v___x_2709_ = lean_uint64_of_nat(v___x_2708_);
v___x_2710_ = lean_unbox_uint64(v_val_2707_);
v___x_2711_ = lean_uint64_dec_lt(v___x_2710_, v___x_2709_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; 
lean_del_object(v___x_2699_);
lean_dec(v_toBind_2694_);
v___x_2712_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2690_, v_inst_2691_, v_inst_2692_, v_stream_2693_, v_maximumSize_2689_, v_result_2706_);
return v___x_2712_;
}
else
{
lean_object* v_throw_2713_; lean_object* v___f_2714_; lean_object* v___x_2715_; uint64_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
lean_inc(v_val_2707_);
v_throw_2713_ = lean_ctor_get(v_inst_2691_, 0);
lean_inc(v_throw_2713_);
v___f_2714_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0), 7, 6);
lean_closure_set(v___f_2714_, 0, v_inst_2690_);
lean_closure_set(v___f_2714_, 1, v_inst_2691_);
lean_closure_set(v___f_2714_, 2, v_inst_2692_);
lean_closure_set(v___f_2714_, 3, v_stream_2693_);
lean_closure_set(v___f_2714_, 4, v_maximumSize_2689_);
lean_closure_set(v___f_2714_, 5, v_result_2706_);
v___x_2715_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0));
v___x_2716_ = lean_unbox_uint64(v_val_2707_);
lean_dec(v_val_2707_);
v___x_2717_ = lean_uint64_to_nat(v___x_2716_);
v___x_2718_ = l_Nat_reprFast(v___x_2717_);
v___x_2719_ = lean_string_append(v___x_2715_, v___x_2718_);
lean_dec_ref(v___x_2718_);
v___x_2720_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1));
v___x_2721_ = lean_string_append(v___x_2719_, v___x_2720_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set_tag(v___x_2699_, 18);
lean_ctor_set(v___x_2699_, 0, v___x_2721_);
v___x_2723_ = v___x_2699_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_apply_2(v_throw_2713_, lean_box(0), v___x_2723_);
v___x_2725_ = lean_apply_4(v_toBind_2694_, lean_box(0), lean_box(0), v___x_2724_, v___f_2714_);
return v___x_2725_;
}
}
}
else
{
lean_object* v___x_2727_; 
lean_del_object(v___x_2699_);
lean_dec(v_toBind_2694_);
v___x_2727_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2690_, v_inst_2691_, v_inst_2692_, v_stream_2693_, v_maximumSize_2689_, v_result_2706_);
return v___x_2727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_stream_2732_, lean_object* v_maximumSize_2733_, lean_object* v_result_2734_){
_start:
{
lean_object* v_toApplicative_2735_; lean_object* v_toBind_2736_; lean_object* v_toPure_2737_; lean_object* v___x_2738_; lean_object* v___f_2739_; lean_object* v___x_2740_; 
v_toApplicative_2735_ = lean_ctor_get(v_inst_2729_, 0);
v_toBind_2736_ = lean_ctor_get(v_inst_2729_, 1);
lean_inc_n(v_toBind_2736_, 2);
v_toPure_2737_ = lean_ctor_get(v_toApplicative_2735_, 1);
lean_inc(v_toPure_2737_);
lean_inc(v_inst_2731_);
lean_inc_ref(v_stream_2732_);
v___x_2738_ = lean_apply_1(v_inst_2731_, v_stream_2732_);
v___f_2739_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 9, 8);
lean_closure_set(v___f_2739_, 0, v_toPure_2737_);
lean_closure_set(v___f_2739_, 1, v_result_2734_);
lean_closure_set(v___f_2739_, 2, v_maximumSize_2733_);
lean_closure_set(v___f_2739_, 3, v_inst_2729_);
lean_closure_set(v___f_2739_, 4, v_inst_2730_);
lean_closure_set(v___f_2739_, 5, v_inst_2731_);
lean_closure_set(v___f_2739_, 6, v_stream_2732_);
lean_closure_set(v___f_2739_, 7, v_toBind_2736_);
v___x_2740_ = lean_apply_4(v_toBind_2736_, lean_box(0), lean_box(0), v___x_2738_, v___f_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_stream_2744_, lean_object* v_maximumSize_2745_, lean_object* v_result_2746_, lean_object* v_____r_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2741_, v_inst_2742_, v_inst_2743_, v_stream_2744_, v_maximumSize_2745_, v_result_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_inst_2752_, lean_object* v_stream_2753_, lean_object* v_maximumSize_2754_, lean_object* v_result_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2750_, v_inst_2751_, v_inst_2752_, v_stream_2753_, v_maximumSize_2754_, v_result_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_2757_, lean_object* v_inst_2758_, lean_object* v_toPure_2759_, lean_object* v_result_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_apply_1(v_inst_2757_, v_result_2760_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_toPure_2759_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2771_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2771_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_throw_2766_; lean_object* v___x_2768_; 
v_throw_2766_ = lean_ctor_get(v_inst_2758_, 0);
lean_inc(v_throw_2766_);
lean_dec_ref(v_inst_2758_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set_tag(v___x_2764_, 18);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2762_);
v___x_2768_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_apply_2(v_throw_2766_, lean_box(0), v___x_2768_);
return v___x_2769_;
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2773_; 
lean_dec_ref(v_inst_2758_);
v_a_2772_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2772_);
lean_dec_ref(v___x_2761_);
v___x_2773_ = lean_apply_2(v_toPure_2759_, lean_box(0), v_a_2772_);
return v___x_2773_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_2774_, lean_object* v_inst_2775_, lean_object* v_inst_2776_, lean_object* v_inst_2777_, lean_object* v_stream_2778_, lean_object* v_maximumSize_2779_){
_start:
{
lean_object* v_toApplicative_2780_; lean_object* v_toBind_2781_; lean_object* v_toPure_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___f_2785_; lean_object* v___x_2786_; 
v_toApplicative_2780_ = lean_ctor_get(v_inst_2775_, 0);
v_toBind_2781_ = lean_ctor_get(v_inst_2775_, 1);
lean_inc(v_toBind_2781_);
v_toPure_2782_ = lean_ctor_get(v_toApplicative_2780_, 1);
lean_inc(v_toPure_2782_);
v___x_2783_ = l_ByteArray_empty;
lean_inc_ref(v_inst_2776_);
v___x_2784_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_2775_, v_inst_2776_, v_inst_2777_, v_stream_2778_, v_maximumSize_2779_, v___x_2783_);
v___f_2785_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2785_, 0, v_inst_2774_);
lean_closure_set(v___f_2785_, 1, v_inst_2776_);
lean_closure_set(v___f_2785_, 2, v_toPure_2782_);
v___x_2786_ = lean_apply_4(v_toBind_2781_, lean_box(0), lean_box(0), v___x_2784_, v___f_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_2787_, lean_object* v_m_2788_, lean_object* v_inst_2789_, lean_object* v_inst_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_stream_2793_, lean_object* v_maximumSize_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_2789_, v_inst_2790_, v_inst_2791_, v_inst_2792_, v_stream_2793_, v_maximumSize_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(uint8_t v_incomplete_2801_, lean_object* v_chunk_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v_pendingProducer_2807_; lean_object* v_pendingConsumer_2808_; lean_object* v_interestWaiter_2809_; uint8_t v_closed_2810_; lean_object* v_knownSize_2811_; lean_object* v_pendingIncompleteChunk_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2853_; 
v___x_2805_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_2803_);
v___x_2806_ = lean_st_ref_get(v___y_2803_);
v_pendingProducer_2807_ = lean_ctor_get(v___x_2806_, 0);
v_pendingConsumer_2808_ = lean_ctor_get(v___x_2806_, 1);
v_interestWaiter_2809_ = lean_ctor_get(v___x_2806_, 2);
v_closed_2810_ = lean_ctor_get_uint8(v___x_2806_, sizeof(void*)*5);
v_knownSize_2811_ = lean_ctor_get(v___x_2806_, 3);
v_pendingIncompleteChunk_2812_ = lean_ctor_get(v___x_2806_, 4);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2814_ = v___x_2806_;
v_isShared_2815_ = v_isSharedCheck_2853_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_pendingIncompleteChunk_2812_);
lean_inc(v_knownSize_2811_);
lean_inc(v_interestWaiter_2809_);
lean_inc(v_pendingConsumer_2808_);
lean_inc(v_pendingProducer_2807_);
lean_dec(v___x_2806_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2853_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___y_2817_; 
if (v_closed_2810_ == 0)
{
if (lean_obj_tag(v_pendingIncompleteChunk_2812_) == 0)
{
v___y_2817_ = v_chunk_2802_;
goto v___jp_2816_;
}
else
{
lean_object* v_val_2831_; lean_object* v_data_2832_; lean_object* v_extensions_2833_; lean_object* v_data_2834_; lean_object* v_extensions_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2851_; 
v_val_2831_ = lean_ctor_get(v_pendingIncompleteChunk_2812_, 0);
lean_inc(v_val_2831_);
lean_dec_ref(v_pendingIncompleteChunk_2812_);
v_data_2832_ = lean_ctor_get(v_val_2831_, 0);
lean_inc_ref(v_data_2832_);
v_extensions_2833_ = lean_ctor_get(v_val_2831_, 1);
lean_inc_ref(v_extensions_2833_);
lean_dec(v_val_2831_);
v_data_2834_ = lean_ctor_get(v_chunk_2802_, 0);
v_extensions_2835_ = lean_ctor_get(v_chunk_2802_, 1);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_chunk_2802_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2837_ = v_chunk_2802_;
v_isShared_2838_ = v_isSharedCheck_2851_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_extensions_2835_);
lean_inc(v_data_2834_);
lean_dec(v_chunk_2802_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2851_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = lean_byte_array_size(v_data_2832_);
v___x_2841_ = lean_byte_array_size(v_data_2834_);
v___x_2842_ = lean_byte_array_copy_slice(v_data_2834_, v___x_2839_, v_data_2832_, v___x_2840_, v___x_2841_, v_closed_2810_);
lean_dec_ref(v_data_2834_);
v___x_2843_ = lean_array_get_size(v_extensions_2833_);
v___x_2844_ = lean_nat_dec_eq(v___x_2843_, v___x_2839_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2846_; 
lean_dec_ref(v_extensions_2835_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_extensions_2833_);
lean_ctor_set(v___x_2837_, 0, v___x_2842_);
v___x_2846_ = v___x_2837_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_extensions_2833_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
v___y_2817_ = v___x_2846_;
goto v___jp_2816_;
}
}
else
{
lean_object* v___x_2849_; 
lean_dec_ref(v_extensions_2833_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2842_);
v___x_2849_ = v___x_2837_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_extensions_2835_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
v___y_2817_ = v___x_2849_;
goto v___jp_2816_;
}
}
}
}
}
else
{
lean_object* v___x_2852_; 
lean_del_object(v___x_2814_);
lean_dec(v_pendingIncompleteChunk_2812_);
lean_dec(v_knownSize_2811_);
lean_dec(v_interestWaiter_2809_);
lean_dec(v_pendingConsumer_2808_);
lean_dec(v_pendingProducer_2807_);
lean_dec_ref(v_chunk_2802_);
v___x_2852_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_2852_;
}
v___jp_2816_:
{
if (v_incomplete_2801_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2818_ = lean_box(0);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 4, v___x_2818_);
v___x_2820_ = v___x_2814_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_pendingProducer_2807_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_pendingConsumer_2808_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_interestWaiter_2809_);
lean_ctor_set(v_reuseFailAlloc_2824_, 3, v_knownSize_2811_);
lean_ctor_set(v_reuseFailAlloc_2824_, 4, v___x_2818_);
lean_ctor_set_uint8(v_reuseFailAlloc_2824_, sizeof(void*)*5, v_closed_2810_);
v___x_2820_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2821_ = lean_st_ref_set(v___y_2803_, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___y_2817_);
v___x_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___y_2817_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 4, v___x_2825_);
v___x_2827_ = v___x_2814_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_pendingProducer_2807_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_pendingConsumer_2808_);
lean_ctor_set(v_reuseFailAlloc_2830_, 2, v_interestWaiter_2809_);
lean_ctor_set(v_reuseFailAlloc_2830_, 3, v_knownSize_2811_);
lean_ctor_set(v_reuseFailAlloc_2830_, 4, v___x_2825_);
lean_ctor_set_uint8(v_reuseFailAlloc_2830_, sizeof(void*)*5, v_closed_2810_);
v___x_2827_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_st_ref_set(v___y_2803_, v___x_2827_);
v___x_2829_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0));
return v___x_2829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_incomplete_2854_, lean_object* v_chunk_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
uint8_t v_incomplete_boxed_2858_; lean_object* v_res_2859_; 
v_incomplete_boxed_2858_ = lean_unbox(v_incomplete_2854_);
v_res_2859_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_incomplete_boxed_2858_, v_chunk_2855_, v___y_2856_);
lean_dec(v___y_2856_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_2860_, lean_object* v_chunk_2861_, uint8_t v_incomplete_2862_){
_start:
{
lean_object* v___x_2864_; lean_object* v___f_2865_; lean_object* v___x_2866_; 
v___x_2864_ = lean_box(v_incomplete_2862_);
v___f_2865_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2865_, 0, v___x_2864_);
lean_closure_set(v___f_2865_, 1, v_chunk_2861_);
v___x_2866_ = l_Std_Mutex_atomically___at___00__private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_2860_, v___f_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_2867_, lean_object* v_chunk_2868_, lean_object* v_incomplete_2869_, lean_object* v_a_2870_){
_start:
{
uint8_t v_incomplete_boxed_2871_; lean_object* v_res_2872_; 
v_incomplete_boxed_2871_ = lean_unbox(v_incomplete_2869_);
v_res_2872_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_2867_, v_chunk_2868_, v_incomplete_boxed_2871_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_2879_){
_start:
{
if (lean_obj_tag(v_x_2879_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2889_; 
v_a_2881_ = lean_ctor_get(v_x_2879_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_x_2879_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2883_ = v_x_2879_;
v_isShared_2884_ = v_isSharedCheck_2889_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v_x_2879_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2889_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
}
}
else
{
lean_object* v___x_2890_; 
lean_dec_ref(v_x_2879_);
v___x_2890_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_2890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___2894_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___2897_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_2904_, lean_object* v_x_2905_){
_start:
{
if (lean_obj_tag(v_x_2905_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v___f_2904_);
v_a_2909_ = lean_ctor_get(v_x_2905_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_x_2905_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2911_ = v_x_2905_;
v_isShared_2912_ = v_isSharedCheck_2917_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v_x_2905_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2917_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
}
else
{
lean_object* v_a_2918_; 
v_a_2918_ = lean_ctor_get(v_x_2905_, 0);
lean_inc(v_a_2918_);
lean_dec_ref(v_x_2905_);
if (lean_obj_tag(v_a_2918_) == 1)
{
lean_object* v_val_2919_; uint8_t v___x_2920_; 
v_val_2919_ = lean_ctor_get(v_a_2918_, 0);
lean_inc(v_val_2919_);
lean_dec_ref(v_a_2918_);
v___x_2920_ = lean_unbox(v_val_2919_);
lean_dec(v_val_2919_);
if (v___x_2920_ == 1)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_box(0);
v___x_2922_ = lean_apply_2(v___f_2904_, v___x_2921_, lean_box(0));
return v___x_2922_;
}
else
{
lean_dec_ref(v___f_2904_);
goto v___jp_2907_;
}
}
else
{
lean_dec(v_a_2918_);
lean_dec_ref(v___f_2904_);
goto v___jp_2907_;
}
}
v___jp_2907_:
{
lean_object* v___x_2908_; 
v___x_2908_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_2908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_2923_, lean_object* v_x_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_2923_, v_x_2924_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_a_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_2929_, lean_object* v_x_2930_){
_start:
{
if (lean_obj_tag(v_x_2930_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2940_; 
v_a_2932_ = lean_ctor_get(v_x_2930_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_x_2930_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2934_ = v_x_2930_;
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v_x_2930_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
}
else
{
lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2951_; 
v_isSharedCheck_2951_ = !lean_is_exclusive(v_x_2930_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; 
v_unused_2952_ = lean_ctor_get(v_x_2930_, 0);
lean_dec(v_unused_2952_);
v___x_2942_ = v_x_2930_;
v_isShared_2943_ = v_isSharedCheck_2951_;
goto v_resetjp_2941_;
}
else
{
lean_dec(v_x_2930_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2951_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2944_ = lean_box(v___x_2929_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2945_);
v___x_2947_ = v___x_2942_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_2953_, lean_object* v_x_2954_, lean_object* v___y_2955_){
_start:
{
uint8_t v___x_5381__boxed_2956_; lean_object* v_res_2957_; 
v___x_5381__boxed_2956_ = lean_unbox(v___x_2953_);
v_res_2957_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5381__boxed_2956_, v_x_2954_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_2958_, lean_object* v_x_2959_){
_start:
{
if (lean_obj_tag(v_x_2959_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2969_; 
v_a_2961_ = lean_ctor_get(v_x_2959_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_x_2959_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2963_ = v_x_2959_;
v_isShared_2964_ = v_isSharedCheck_2969_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v_x_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2969_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
return v___x_2967_;
}
}
}
else
{
lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2980_; 
v_isSharedCheck_2980_ = !lean_is_exclusive(v_x_2959_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; 
v_unused_2981_ = lean_ctor_get(v_x_2959_, 0);
lean_dec(v_unused_2981_);
v___x_2971_ = v_x_2959_;
v_isShared_2972_ = v_isSharedCheck_2980_;
goto v_resetjp_2970_;
}
else
{
lean_dec(v_x_2959_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2980_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2973_ = lean_box(v_a_2958_);
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v___x_2974_);
v___x_2976_ = v___x_2971_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_2982_, lean_object* v_x_2983_, lean_object* v___y_2984_){
_start:
{
uint8_t v_a_5433__boxed_2985_; lean_object* v_res_2986_; 
v_a_5433__boxed_2985_ = lean_unbox(v_a_2982_);
v_res_2986_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5433__boxed_2985_, v_x_2983_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_2987_, lean_object* v_interestWaiter_2988_, uint8_t v_closed_2989_, lean_object* v_knownSize_2990_, lean_object* v_pendingIncompleteChunk_2991_, lean_object* v___y_2992_, lean_object* v_chunk_2993_, lean_object* v___f_2994_, lean_object* v_x_2995_){
_start:
{
if (lean_obj_tag(v_x_2995_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v___f_2994_);
lean_dec(v_pendingIncompleteChunk_2991_);
lean_dec(v_knownSize_2990_);
lean_dec(v_interestWaiter_2988_);
lean_dec(v_pendingProducer_2987_);
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
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3032_; 
v_a_3006_ = lean_ctor_get(v_x_2995_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_x_2995_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3008_ = v_x_2995_;
v_isShared_3009_ = v_isSharedCheck_3032_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v_x_2995_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3032_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
uint8_t v___x_3010_; 
v___x_3010_ = lean_unbox(v_a_3006_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___f_3014_; lean_object* v___x_3016_; 
lean_dec_ref(v___f_2994_);
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3012_, 0, v_pendingProducer_2987_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
lean_ctor_set(v___x_3012_, 2, v_interestWaiter_2988_);
lean_ctor_set(v___x_3012_, 3, v_knownSize_2990_);
lean_ctor_set(v___x_3012_, 4, v_pendingIncompleteChunk_2991_);
lean_ctor_set_uint8(v___x_3012_, sizeof(void*)*5, v_closed_2989_);
v___x_3013_ = lean_st_ref_set(v___y_2992_, v___x_3012_);
lean_inc(v_a_3006_);
v___f_3014_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3014_, 0, v_a_3006_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v___x_3013_);
v___x_3016_ = v___x_3008_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3013_);
v___x_3016_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; lean_object* v___x_3020_; 
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
v___x_3018_ = lean_unsigned_to_nat(0u);
v___x_3019_ = lean_unbox(v_a_3006_);
lean_dec(v_a_3006_);
v___x_3020_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3018_, v___x_3019_, v___x_3017_, v___f_3014_);
return v___x_3020_;
}
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
lean_dec(v_a_3006_);
v___x_3022_ = lean_box(0);
v___x_3023_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_2990_, v_chunk_2993_);
v___x_3024_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3024_, 0, v_pendingProducer_2987_);
lean_ctor_set(v___x_3024_, 1, v___x_3022_);
lean_ctor_set(v___x_3024_, 2, v_interestWaiter_2988_);
lean_ctor_set(v___x_3024_, 3, v___x_3023_);
lean_ctor_set(v___x_3024_, 4, v_pendingIncompleteChunk_2991_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*5, v_closed_2989_);
v___x_3025_ = lean_st_ref_set(v___y_2992_, v___x_3024_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v___x_3025_);
v___x_3027_ = v___x_3008_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3029_, v_closed_2989_, v___x_3028_, v___f_2994_);
return v___x_3030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_3033_, lean_object* v_interestWaiter_3034_, lean_object* v_closed_3035_, lean_object* v_knownSize_3036_, lean_object* v_pendingIncompleteChunk_3037_, lean_object* v___y_3038_, lean_object* v_chunk_3039_, lean_object* v___f_3040_, lean_object* v_x_3041_, lean_object* v___y_3042_){
_start:
{
uint8_t v_closed_boxed_3043_; lean_object* v_res_3044_; 
v_closed_boxed_3043_ = lean_unbox(v_closed_3035_);
v_res_3044_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_3033_, v_interestWaiter_3034_, v_closed_boxed_3043_, v_knownSize_3036_, v_pendingIncompleteChunk_3037_, v___y_3038_, v_chunk_3039_, v___f_3040_, v_x_3041_);
lean_dec_ref(v_chunk_3039_);
lean_dec(v___y_3038_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v_chunk_3063_, lean_object* v___y_3064_, lean_object* v_a_3065_, lean_object* v___f_3066_, lean_object* v_x_3067_){
_start:
{
if (lean_obj_tag(v_x_3067_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3077_; 
lean_dec_ref(v___f_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_chunk_3063_);
v_a_3069_ = lean_ctor_get(v_x_3067_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_x_3067_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3071_ = v_x_3067_;
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v_x_3067_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3131_; 
v_a_3078_ = lean_ctor_get(v_x_3067_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_x_3067_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3080_ = v_x_3067_;
v_isShared_3081_ = v_isSharedCheck_3131_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v_x_3067_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3131_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
uint8_t v_closed_3082_; 
v_closed_3082_ = lean_ctor_get_uint8(v_a_3078_, sizeof(void*)*5);
if (v_closed_3082_ == 0)
{
lean_object* v_pendingConsumer_3083_; 
v_pendingConsumer_3083_ = lean_ctor_get(v_a_3078_, 1);
lean_inc(v_pendingConsumer_3083_);
if (lean_obj_tag(v_pendingConsumer_3083_) == 1)
{
lean_object* v_pendingProducer_3084_; lean_object* v_interestWaiter_3085_; lean_object* v_knownSize_3086_; lean_object* v_pendingIncompleteChunk_3087_; lean_object* v_val_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v___f_3066_);
lean_dec(v_a_3065_);
v_pendingProducer_3084_ = lean_ctor_get(v_a_3078_, 0);
lean_inc(v_pendingProducer_3084_);
v_interestWaiter_3085_ = lean_ctor_get(v_a_3078_, 2);
lean_inc(v_interestWaiter_3085_);
v_knownSize_3086_ = lean_ctor_get(v_a_3078_, 3);
lean_inc(v_knownSize_3086_);
v_pendingIncompleteChunk_3087_ = lean_ctor_get(v_a_3078_, 4);
lean_inc(v_pendingIncompleteChunk_3087_);
lean_dec(v_a_3078_);
v_val_3088_ = lean_ctor_get(v_pendingConsumer_3083_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_pendingConsumer_3083_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3090_ = v_pendingConsumer_3083_;
v_isShared_3091_ = v_isSharedCheck_3106_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_val_3088_);
lean_dec(v_pendingConsumer_3083_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3106_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
lean_inc_ref(v_chunk_3063_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v_chunk_3063_);
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_chunk_3063_);
v___x_3093_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
uint8_t v___x_3094_; lean_object* v___f_3095_; lean_object* v___x_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3094_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_3088_, v___x_3093_);
lean_dec(v_val_3088_);
v___f_3095_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_3096_ = lean_box(v_closed_3082_);
lean_inc(v___y_3064_);
v___f_3097_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 10, 8);
lean_closure_set(v___f_3097_, 0, v_pendingProducer_3084_);
lean_closure_set(v___f_3097_, 1, v_interestWaiter_3085_);
lean_closure_set(v___f_3097_, 2, v___x_3096_);
lean_closure_set(v___f_3097_, 3, v_knownSize_3086_);
lean_closure_set(v___f_3097_, 4, v_pendingIncompleteChunk_3087_);
lean_closure_set(v___f_3097_, 5, v___y_3064_);
lean_closure_set(v___f_3097_, 6, v_chunk_3063_);
lean_closure_set(v___f_3097_, 7, v___f_3095_);
v___x_3098_ = lean_box(v___x_3094_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3098_);
v___x_3100_ = v___x_3080_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3102_, v_closed_3082_, v___x_3101_, v___f_3097_);
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_pendingProducer_3107_; 
v_pendingProducer_3107_ = lean_ctor_get(v_a_3078_, 0);
if (lean_obj_tag(v_pendingProducer_3107_) == 0)
{
lean_object* v_interestWaiter_3108_; lean_object* v_knownSize_3109_; lean_object* v_pendingIncompleteChunk_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3126_; 
v_interestWaiter_3108_ = lean_ctor_get(v_a_3078_, 2);
v_knownSize_3109_ = lean_ctor_get(v_a_3078_, 3);
v_pendingIncompleteChunk_3110_ = lean_ctor_get(v_a_3078_, 4);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_a_3078_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; lean_object* v_unused_3128_; 
v_unused_3127_ = lean_ctor_get(v_a_3078_, 1);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_a_3078_, 0);
lean_dec(v_unused_3128_);
v___x_3112_ = v_a_3078_;
v_isShared_3113_ = v_isSharedCheck_3126_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_pendingIncompleteChunk_3110_);
lean_inc(v_knownSize_3109_);
lean_inc(v_interestWaiter_3108_);
lean_dec(v_a_3078_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3126_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_chunk_3063_);
lean_ctor_set(v___x_3114_, 1, v_a_3065_);
v___x_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3115_);
v___x_3117_ = v___x_3112_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_pendingConsumer_3083_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_interestWaiter_3108_);
lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_knownSize_3109_);
lean_ctor_set(v_reuseFailAlloc_3125_, 4, v_pendingIncompleteChunk_3110_);
lean_ctor_set_uint8(v_reuseFailAlloc_3125_, sizeof(void*)*5, v_closed_3082_);
v___x_3117_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = lean_st_ref_set(v___y_3064_, v___x_3117_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3118_);
v___x_3120_ = v___x_3080_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
v___x_3122_ = lean_unsigned_to_nat(0u);
v___x_3123_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3122_, v_closed_3082_, v___x_3121_, v___f_3066_);
return v___x_3123_;
}
}
}
}
else
{
lean_object* v___x_3129_; 
lean_dec(v_pendingConsumer_3083_);
lean_del_object(v___x_3080_);
lean_dec(v_a_3078_);
lean_dec_ref(v___f_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_chunk_3063_);
v___x_3129_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_3129_;
}
}
}
else
{
lean_object* v___x_3130_; 
lean_del_object(v___x_3080_);
lean_dec(v_a_3078_);
lean_dec_ref(v___f_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_chunk_3063_);
v___x_3130_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_3130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v_chunk_3132_, lean_object* v___y_3133_, lean_object* v_a_3134_, lean_object* v___f_3135_, lean_object* v_x_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v_chunk_3132_, v___y_3133_, v_a_3134_, v___f_3135_, v_x_3136_);
lean_dec(v___y_3133_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_3139_, lean_object* v___f_3140_, lean_object* v_x_3141_){
_start:
{
if (lean_obj_tag(v_x_3141_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v___f_3140_);
v_a_3143_ = lean_ctor_get(v_x_3141_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_x_3141_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3145_ = v_x_3141_;
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v_x_3141_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; 
v___x_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
return v___x_3149_;
}
}
}
else
{
lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3163_; 
v_isSharedCheck_3163_ = !lean_is_exclusive(v_x_3141_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v_x_3141_, 0);
lean_dec(v_unused_3164_);
v___x_3153_ = v_x_3141_;
v_isShared_3154_ = v_isSharedCheck_3163_;
goto v_resetjp_3152_;
}
else
{
lean_dec(v_x_3141_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3163_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3155_ = lean_st_ref_get(v___y_3139_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v___x_3155_);
v___x_3157_ = v___x_3153_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = 0;
v___x_3161_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3159_, v___x_3160_, v___x_3158_, v___f_3140_);
return v___x_3161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_3165_, lean_object* v___f_3166_, lean_object* v_x_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_3165_, v___f_3166_, v_x_3167_);
lean_dec(v___y_3165_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_3170_, lean_object* v_a_3171_, lean_object* v___f_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; lean_object* v___f_3176_; lean_object* v___f_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; lean_object* v___x_3180_; 
v___x_3175_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3173_);
lean_inc_n(v___y_3173_, 2);
v___f_3176_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_3176_, 0, v_chunk_3170_);
lean_closure_set(v___f_3176_, 1, v___y_3173_);
lean_closure_set(v___f_3176_, 2, v_a_3171_);
lean_closure_set(v___f_3176_, 3, v___f_3172_);
v___f_3177_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_3177_, 0, v___y_3173_);
lean_closure_set(v___f_3177_, 1, v___f_3176_);
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = 0;
v___x_3180_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3178_, v___x_3179_, v___x_3175_, v___f_3177_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_3181_, lean_object* v_a_3182_, lean_object* v___f_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_3181_, v_a_3182_, v___f_3183_, v___y_3184_);
lean_dec(v___y_3184_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_3192_, lean_object* v___f_3193_, lean_object* v___f_3194_, lean_object* v_stream_3195_, lean_object* v_chunk_3196_, lean_object* v___f_3197_, lean_object* v_x_3198_){
_start:
{
if (lean_obj_tag(v_x_3198_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v___f_3197_);
lean_dec_ref(v_chunk_3196_);
lean_dec_ref(v_stream_3195_);
lean_dec_ref(v___f_3194_);
lean_dec_ref(v___f_3193_);
v_a_3200_ = lean_ctor_get(v_x_3198_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_x_3198_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3202_ = v_x_3198_;
v_isShared_3203_ = v_isSharedCheck_3208_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v_x_3198_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3208_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
return v___x_3206_;
}
}
}
else
{
lean_object* v_a_3209_; 
v_a_3209_ = lean_ctor_get(v_x_3198_, 0);
lean_inc(v_a_3209_);
lean_dec_ref(v_x_3198_);
if (lean_obj_tag(v_a_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3218_; 
lean_dec_ref(v___f_3197_);
lean_dec_ref(v_chunk_3196_);
lean_dec_ref(v_stream_3195_);
lean_dec_ref(v___f_3194_);
lean_dec_ref(v___f_3193_);
v_a_3210_ = lean_ctor_get(v_a_3209_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_a_3209_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3212_ = v_a_3209_;
v_isShared_3213_ = v_isSharedCheck_3218_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v_a_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3218_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
return v___x_3216_;
}
}
}
else
{
lean_object* v_a_3219_; 
v_a_3219_ = lean_ctor_get(v_a_3209_, 0);
lean_inc(v_a_3219_);
lean_dec_ref(v_a_3209_);
if (lean_obj_tag(v_a_3219_) == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec_ref(v___f_3197_);
lean_dec_ref(v_chunk_3196_);
lean_dec_ref(v_stream_3195_);
v___x_3220_ = lean_io_promise_result_opt(v_a_3192_);
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = 0;
v___x_3223_ = lean_task_map(v___f_3193_, v___x_3220_, v___x_3221_, v___x_3222_);
v___x_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
v___x_3225_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3221_, v___x_3222_, v___x_3224_, v___f_3194_);
return v___x_3225_;
}
else
{
lean_object* v_val_3226_; uint8_t v___x_3227_; 
lean_dec_ref(v___f_3194_);
lean_dec_ref(v___f_3193_);
v_val_3226_ = lean_ctor_get(v_a_3219_, 0);
lean_inc(v_val_3226_);
lean_dec_ref(v_a_3219_);
v___x_3227_ = lean_unbox(v_val_3226_);
lean_dec(v_val_3226_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; 
lean_dec_ref(v___f_3197_);
v___x_3228_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3195_, v_chunk_3196_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_dec_ref(v_chunk_3196_);
lean_dec_ref(v_stream_3195_);
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_apply_2(v___f_3197_, v___x_3229_, lean_box(0));
return v___x_3230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_3231_, lean_object* v___f_3232_, lean_object* v___f_3233_, lean_object* v_stream_3234_, lean_object* v_chunk_3235_, lean_object* v___f_3236_, lean_object* v_x_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_3231_, v___f_3232_, v___f_3233_, v_stream_3234_, v_chunk_3235_, v___f_3236_, v_x_3237_);
lean_dec(v_a_3231_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_3240_, lean_object* v___f_3241_, lean_object* v_stream_3242_, lean_object* v___f_3243_, lean_object* v___f_3244_, lean_object* v___f_3245_, lean_object* v_x_3246_){
_start:
{
if (lean_obj_tag(v_x_3246_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3256_; 
lean_dec_ref(v___f_3245_);
lean_dec_ref(v___f_3244_);
lean_dec_ref(v___f_3243_);
lean_dec_ref(v_stream_3242_);
lean_dec_ref(v___f_3241_);
lean_dec_ref(v_chunk_3240_);
v_a_3248_ = lean_ctor_get(v_x_3246_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_x_3246_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3250_ = v_x_3246_;
v_isShared_3251_ = v_isSharedCheck_3256_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v_x_3246_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3256_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
return v___x_3254_;
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___f_3258_; lean_object* v___x_3259_; lean_object* v___f_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; lean_object* v___x_3263_; 
v_a_3257_ = lean_ctor_get(v_x_3246_, 0);
lean_inc_n(v_a_3257_, 2);
lean_dec_ref(v_x_3246_);
lean_inc_ref(v_chunk_3240_);
v___f_3258_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_3258_, 0, v_chunk_3240_);
lean_closure_set(v___f_3258_, 1, v_a_3257_);
lean_closure_set(v___f_3258_, 2, v___f_3241_);
lean_inc_ref(v_stream_3242_);
v___x_3259_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3242_, v___f_3258_);
v___f_3260_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3260_, 0, v_a_3257_);
lean_closure_set(v___f_3260_, 1, v___f_3243_);
lean_closure_set(v___f_3260_, 2, v___f_3244_);
lean_closure_set(v___f_3260_, 3, v_stream_3242_);
lean_closure_set(v___f_3260_, 4, v_chunk_3240_);
lean_closure_set(v___f_3260_, 5, v___f_3245_);
v___x_3261_ = lean_unsigned_to_nat(0u);
v___x_3262_ = 0;
v___x_3263_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3261_, v___x_3262_, v___x_3259_, v___f_3260_);
return v___x_3263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_3264_, lean_object* v___f_3265_, lean_object* v_stream_3266_, lean_object* v___f_3267_, lean_object* v___f_3268_, lean_object* v___f_3269_, lean_object* v_x_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_3264_, v___f_3265_, v_stream_3266_, v___f_3267_, v___f_3268_, v___f_3269_, v_x_3270_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_3273_, lean_object* v_chunk_3274_){
_start:
{
lean_object* v___x_3276_; lean_object* v___f_3277_; lean_object* v___f_3278_; lean_object* v___f_3279_; lean_object* v___f_3280_; lean_object* v___f_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; lean_object* v___x_3286_; 
v___x_3276_ = lean_io_promise_new();
v___f_3277_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_3278_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_3279_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_3280_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_3281_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_3281_, 0, v_chunk_3274_);
lean_closure_set(v___f_3281_, 1, v___f_3277_);
lean_closure_set(v___f_3281_, 2, v_stream_3273_);
lean_closure_set(v___f_3281_, 3, v___f_3280_);
lean_closure_set(v___f_3281_, 4, v___f_3279_);
lean_closure_set(v___f_3281_, 5, v___f_3278_);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3276_);
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
v___x_3284_ = lean_unsigned_to_nat(0u);
v___x_3285_ = 0;
v___x_3286_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3284_, v___x_3285_, v___x_3283_, v___f_3281_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_3287_, lean_object* v_chunk_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3287_, v_chunk_3288_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_3291_, lean_object* v_x_3292_){
_start:
{
if (lean_obj_tag(v_x_3292_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3302_; 
lean_dec_ref(v_stream_3291_);
v_a_3294_ = lean_ctor_get(v_x_3292_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_x_3292_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3296_ = v_x_3292_;
v_isShared_3297_ = v_isSharedCheck_3302_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v_x_3292_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3302_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
return v___x_3300_;
}
}
}
else
{
lean_object* v_a_3303_; 
v_a_3303_ = lean_ctor_get(v_x_3292_, 0);
lean_inc(v_a_3303_);
lean_dec_ref(v_x_3292_);
if (lean_obj_tag(v_a_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref(v_stream_3291_);
v_a_3304_ = lean_ctor_get(v_a_3303_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v_a_3303_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3306_ = v_a_3303_;
v_isShared_3307_ = v_isSharedCheck_3312_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v_a_3303_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3312_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
return v___x_3310_;
}
}
}
else
{
lean_object* v_a_3313_; 
v_a_3313_ = lean_ctor_get(v_a_3303_, 0);
lean_inc(v_a_3313_);
lean_dec_ref(v_a_3303_);
if (lean_obj_tag(v_a_3313_) == 0)
{
lean_object* v___x_3314_; 
lean_dec_ref(v_stream_3291_);
v___x_3314_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_3314_;
}
else
{
lean_object* v_val_3315_; lean_object* v_data_3316_; lean_object* v_extensions_3317_; uint8_t v___x_3318_; 
v_val_3315_ = lean_ctor_get(v_a_3313_, 0);
lean_inc(v_val_3315_);
lean_dec_ref(v_a_3313_);
v_data_3316_ = lean_ctor_get(v_val_3315_, 0);
v_extensions_3317_ = lean_ctor_get(v_val_3315_, 1);
v___x_3318_ = l_ByteArray_isEmpty(v_data_3316_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3291_, v_val_3315_);
return v___x_3319_;
}
else
{
lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3320_ = lean_array_get_size(v_extensions_3317_);
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3322_ = lean_nat_dec_eq(v___x_3320_, v___x_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_3291_, v_val_3315_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; 
lean_dec(v_val_3315_);
lean_dec_ref(v_stream_3291_);
v___x_3324_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_3324_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object* v_stream_3325_, lean_object* v_x_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_3325_, v_x_3326_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object* v_stream_3329_, lean_object* v_chunk_3330_, uint8_t v_incomplete_3331_){
_start:
{
lean_object* v___x_3333_; lean_object* v___f_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; 
lean_inc_ref(v_stream_3329_);
v___x_3333_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_3329_, v_chunk_3330_, v_incomplete_3331_);
v___f_3334_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3334_, 0, v_stream_3329_);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = 0;
v___x_3339_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3337_, v___x_3338_, v___x_3336_, v___f_3334_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object* v_stream_3340_, lean_object* v_chunk_3341_, lean_object* v_incomplete_3342_, lean_object* v_a_3343_){
_start:
{
uint8_t v_incomplete_boxed_3344_; lean_object* v_res_3345_; 
v_incomplete_boxed_3344_ = lean_unbox(v_incomplete_3342_);
v_res_3345_ = l_Std_Http_Body_Stream_send(v_stream_3340_, v_chunk_3341_, v_incomplete_boxed_3344_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object* v_x_3346_){
_start:
{
uint8_t v___y_3349_; 
if (lean_obj_tag(v_x_3346_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3361_; 
v_a_3353_ = lean_ctor_get(v_x_3346_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v_x_3346_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3355_ = v_x_3346_;
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v_x_3346_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
return v___x_3359_;
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v_pendingConsumer_3363_; 
v_a_3362_ = lean_ctor_get(v_x_3346_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v_x_3346_);
v_pendingConsumer_3363_ = lean_ctor_get(v_a_3362_, 1);
lean_inc(v_pendingConsumer_3363_);
lean_dec(v_a_3362_);
if (lean_obj_tag(v_pendingConsumer_3363_) == 0)
{
uint8_t v___x_3364_; 
v___x_3364_ = 0;
v___y_3349_ = v___x_3364_;
goto v___jp_3348_;
}
else
{
uint8_t v___x_3365_; 
lean_dec_ref(v_pendingConsumer_3363_);
v___x_3365_ = 1;
v___y_3349_ = v___x_3365_;
goto v___jp_3348_;
}
}
v___jp_3348_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = lean_box(v___y_3349_);
v___x_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
return v___x_3352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object* v_x_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_3366_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object* v_a_3370_){
_start:
{
lean_object* v___x_3372_; lean_object* v___f_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; 
v___x_3372_ = lean_st_ref_get(v_a_3370_);
v___f_3373_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
v___x_3376_ = lean_unsigned_to_nat(0u);
v___x_3377_ = 0;
v___x_3378_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3376_, v___x_3377_, v___x_3375_, v___f_3373_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object* v_a_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_3379_);
lean_dec(v_a_3379_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object* v___y_3382_, lean_object* v_x_3383_){
_start:
{
if (lean_obj_tag(v_x_3383_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3393_; 
v_a_3385_ = lean_ctor_get(v_x_3383_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_x_3383_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3387_ = v_x_3383_;
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v_x_3383_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
return v___x_3391_;
}
}
}
else
{
lean_object* v___x_3394_; 
lean_dec_ref(v_x_3383_);
v___x_3394_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_3382_);
return v___x_3394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object* v___y_3395_, lean_object* v_x_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_3395_, v_x_3396_);
lean_dec(v___y_3395_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object* v___y_3399_){
_start:
{
lean_object* v___x_3401_; lean_object* v___f_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; 
v___x_3401_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3399_);
lean_inc(v___y_3399_);
v___f_3402_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3402_, 0, v___y_3399_);
v___x_3403_ = lean_unsigned_to_nat(0u);
v___x_3404_ = 0;
v___x_3405_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3403_, v___x_3404_, v___x_3401_, v___f_3402_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_3406_);
lean_dec(v___y_3406_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object* v_stream_3410_){
_start:
{
lean_object* v___f_3412_; lean_object* v___x_3413_; 
v___f_3412_ = ((lean_object*)(l_Std_Http_Body_Stream_hasInterest___closed__0));
v___x_3413_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3410_, v___f_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object* v_stream_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Std_Http_Body_Stream_hasInterest(v_stream_3414_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object* v_lose_3417_, lean_object* v___y_3418_, uint8_t v___x_3419_, lean_object* v_promise_3420_, lean_object* v_x_3421_){
_start:
{
if (lean_obj_tag(v_x_3421_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_lose_3417_);
v_a_3423_ = lean_ctor_get(v_x_3421_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_x_3421_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3425_ = v_x_3421_;
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v_x_3421_);
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
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3445_; 
v_a_3432_ = lean_ctor_get(v_x_3421_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_x_3421_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3434_ = v_x_3421_;
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v_x_3421_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_unbox(v_a_3432_);
lean_dec(v_a_3432_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; 
lean_del_object(v___x_3434_);
lean_inc(v___y_3418_);
v___x_3437_ = lean_apply_2(v_lose_3417_, v___y_3418_, lean_box(0));
return v___x_3437_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
lean_dec_ref(v_lose_3417_);
v___x_3438_ = lean_box(v___x_3419_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___x_3438_);
v___x_3440_ = v___x_3434_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = lean_io_promise_resolve(v___x_3440_, v_promise_3420_);
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object* v_lose_3446_, lean_object* v___y_3447_, lean_object* v___x_3448_, lean_object* v_promise_3449_, lean_object* v_x_3450_, lean_object* v___y_3451_){
_start:
{
uint8_t v___x_4255__boxed_3452_; lean_object* v_res_3453_; 
v___x_4255__boxed_3452_ = lean_unbox(v___x_3448_);
v_res_3453_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_3446_, v___y_3447_, v___x_4255__boxed_3452_, v_promise_3449_, v_x_3450_);
lean_dec(v_promise_3449_);
lean_dec(v___y_3447_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_3454_, lean_object* v_lose_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v_finished_3458_; lean_object* v_promise_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; lean_object* v___x_3462_; lean_object* v___f_3463_; uint8_t v___y_3465_; uint8_t v___x_3474_; 
v_finished_3458_ = lean_ctor_get(v_w_3454_, 0);
lean_inc(v_finished_3458_);
v_promise_3459_ = lean_ctor_get(v_w_3454_, 1);
lean_inc(v_promise_3459_);
lean_dec_ref(v_w_3454_);
v___x_3460_ = lean_st_ref_take(v_finished_3458_);
v___x_3461_ = 0;
v___x_3462_ = lean_box(v___x_3461_);
lean_inc(v___y_3456_);
v___f_3463_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3463_, 0, v_lose_3455_);
lean_closure_set(v___f_3463_, 1, v___y_3456_);
lean_closure_set(v___f_3463_, 2, v___x_3462_);
lean_closure_set(v___f_3463_, 3, v_promise_3459_);
v___x_3474_ = lean_unbox(v___x_3460_);
lean_dec(v___x_3460_);
if (v___x_3474_ == 0)
{
uint8_t v___x_3475_; 
v___x_3475_ = 1;
v___y_3465_ = v___x_3475_;
goto v___jp_3464_;
}
else
{
v___y_3465_ = v___x_3461_;
goto v___jp_3464_;
}
v___jp_3464_:
{
uint8_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3466_ = 1;
v___x_3467_ = lean_box(v___x_3466_);
v___x_3468_ = lean_st_ref_set(v_finished_3458_, v___x_3467_);
lean_dec(v_finished_3458_);
v___x_3469_ = lean_box(v___y_3465_);
v___x_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
v___x_3472_ = lean_unsigned_to_nat(0u);
v___x_3473_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3472_, v___x_3461_, v___x_3471_, v___f_3463_);
return v___x_3473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object* v_w_3476_, lean_object* v_lose_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_3476_, v_lose_3477_, v___y_3478_);
lean_dec(v___y_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object* v_w_3481_, lean_object* v_lose_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_finished_3485_; lean_object* v_promise_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___f_3490_; uint8_t v___y_3492_; uint8_t v___x_3501_; 
v_finished_3485_ = lean_ctor_get(v_w_3481_, 0);
lean_inc(v_finished_3485_);
v_promise_3486_ = lean_ctor_get(v_w_3481_, 1);
lean_inc(v_promise_3486_);
lean_dec_ref(v_w_3481_);
v___x_3487_ = lean_st_ref_take(v_finished_3485_);
v___x_3488_ = 1;
v___x_3489_ = lean_box(v___x_3488_);
lean_inc(v___y_3483_);
v___f_3490_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3490_, 0, v_lose_3482_);
lean_closure_set(v___f_3490_, 1, v___y_3483_);
lean_closure_set(v___f_3490_, 2, v___x_3489_);
lean_closure_set(v___f_3490_, 3, v_promise_3486_);
v___x_3501_ = lean_unbox(v___x_3487_);
lean_dec(v___x_3487_);
if (v___x_3501_ == 0)
{
v___y_3492_ = v___x_3488_;
goto v___jp_3491_;
}
else
{
uint8_t v___x_3502_; 
v___x_3502_ = 0;
v___y_3492_ = v___x_3502_;
goto v___jp_3491_;
}
v___jp_3491_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; lean_object* v___x_3500_; 
v___x_3493_ = lean_box(v___x_3488_);
v___x_3494_ = lean_st_ref_set(v_finished_3485_, v___x_3493_);
lean_dec(v_finished_3485_);
v___x_3495_ = lean_box(v___y_3492_);
v___x_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
v___x_3498_ = lean_unsigned_to_nat(0u);
v___x_3499_ = 0;
v___x_3500_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3498_, v___x_3499_, v___x_3497_, v___f_3490_);
return v___x_3500_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_3503_, lean_object* v_lose_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_3503_, v_lose_3504_, v___y_3505_);
lean_dec(v___y_3505_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_3524_){
_start:
{
if (lean_obj_tag(v_x_3524_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3534_; 
v_a_3526_ = lean_ctor_get(v_x_3524_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_x_3524_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3528_ = v_x_3524_;
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v_x_3524_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v_pendingConsumer_3536_; 
v_a_3535_ = lean_ctor_get(v_x_3524_, 0);
lean_inc(v_a_3535_);
lean_dec_ref(v_x_3524_);
v_pendingConsumer_3536_ = lean_ctor_get(v_a_3535_, 1);
if (lean_obj_tag(v_pendingConsumer_3536_) == 0)
{
uint8_t v_closed_3537_; 
v_closed_3537_ = lean_ctor_get_uint8(v_a_3535_, sizeof(void*)*5);
lean_dec(v_a_3535_);
if (v_closed_3537_ == 0)
{
lean_object* v___x_3538_; 
v___x_3538_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_3538_;
}
else
{
lean_object* v___x_3539_; 
v___x_3539_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_3539_;
}
}
else
{
lean_object* v___x_3540_; 
lean_dec(v_a_3535_);
v___x_3540_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_3540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_3541_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_3551_, lean_object* v___y_3552_, lean_object* v_x_3553_){
_start:
{
if (lean_obj_tag(v_x_3553_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3563_; 
lean_dec_ref(v_waiter_3551_);
v_a_3555_ = lean_ctor_get(v_x_3553_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_x_3553_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3557_ = v_x_3553_;
v_isShared_3558_ = v_isSharedCheck_3563_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v_x_3553_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3563_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
return v___x_3561_;
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3594_; 
v_a_3564_ = lean_ctor_get(v_x_3553_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_x_3553_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3566_ = v_x_3553_;
v_isShared_3567_ = v_isSharedCheck_3594_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v_x_3553_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3594_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v_pendingConsumer_3568_; 
v_pendingConsumer_3568_ = lean_ctor_get(v_a_3564_, 1);
lean_inc(v_pendingConsumer_3568_);
if (lean_obj_tag(v_pendingConsumer_3568_) == 0)
{
uint8_t v_closed_3569_; 
v_closed_3569_ = lean_ctor_get_uint8(v_a_3564_, sizeof(void*)*5);
if (v_closed_3569_ == 0)
{
lean_object* v_interestWaiter_3570_; 
v_interestWaiter_3570_ = lean_ctor_get(v_a_3564_, 2);
if (lean_obj_tag(v_interestWaiter_3570_) == 0)
{
lean_object* v_pendingProducer_3571_; lean_object* v_knownSize_3572_; lean_object* v_pendingIncompleteChunk_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3586_; 
v_pendingProducer_3571_ = lean_ctor_get(v_a_3564_, 0);
v_knownSize_3572_ = lean_ctor_get(v_a_3564_, 3);
v_pendingIncompleteChunk_3573_ = lean_ctor_get(v_a_3564_, 4);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_a_3564_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; lean_object* v_unused_3588_; 
v_unused_3587_ = lean_ctor_get(v_a_3564_, 2);
lean_dec(v_unused_3587_);
v_unused_3588_ = lean_ctor_get(v_a_3564_, 1);
lean_dec(v_unused_3588_);
v___x_3575_ = v_a_3564_;
v_isShared_3576_ = v_isSharedCheck_3586_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_pendingIncompleteChunk_3573_);
lean_inc(v_knownSize_3572_);
lean_inc(v_pendingProducer_3571_);
lean_dec(v_a_3564_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3586_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3577_, 0, v_waiter_3551_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 2, v___x_3577_);
v___x_3579_ = v___x_3575_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_pendingProducer_3571_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_pendingConsumer_3568_);
lean_ctor_set(v_reuseFailAlloc_3585_, 2, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3585_, 3, v_knownSize_3572_);
lean_ctor_set(v_reuseFailAlloc_3585_, 4, v_pendingIncompleteChunk_3573_);
lean_ctor_set_uint8(v_reuseFailAlloc_3585_, sizeof(void*)*5, v_closed_3569_);
v___x_3579_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3580_ = lean_st_ref_set(v___y_3552_, v___x_3579_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3580_);
v___x_3582_ = v___x_3566_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; 
v___x_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
return v___x_3583_;
}
}
}
}
else
{
lean_object* v___x_3589_; 
lean_del_object(v___x_3566_);
lean_dec(v_a_3564_);
lean_dec_ref(v_waiter_3551_);
v___x_3589_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_3589_;
}
}
else
{
lean_object* v___f_3590_; lean_object* v___x_3591_; 
lean_del_object(v___x_3566_);
lean_dec(v_a_3564_);
v___f_3590_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__5___closed__0));
v___x_3591_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_3551_, v___f_3590_, v___y_3552_);
return v___x_3591_;
}
}
else
{
lean_object* v___f_3592_; lean_object* v___x_3593_; 
lean_dec_ref(v_pendingConsumer_3568_);
lean_del_object(v___x_3566_);
lean_dec(v_a_3564_);
v___f_3592_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__5___closed__0));
v___x_3593_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_3551_, v___f_3592_, v___y_3552_);
return v___x_3593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_3595_, lean_object* v___y_3596_, lean_object* v_x_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_3595_, v___y_3596_, v_x_3597_);
lean_dec(v___y_3596_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_3600_, lean_object* v___f_3601_, lean_object* v_x_3602_){
_start:
{
if (lean_obj_tag(v_x_3602_) == 0)
{
lean_object* v___x_3604_; 
lean_dec_ref(v___f_3601_);
v___x_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3604_, 0, v_x_3602_);
return v___x_3604_;
}
else
{
lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3616_; 
v_isSharedCheck_3616_ = !lean_is_exclusive(v_x_3602_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v_x_3602_, 0);
lean_dec(v_unused_3617_);
v___x_3606_ = v_x_3602_;
v_isShared_3607_ = v_isSharedCheck_3616_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v_x_3602_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3616_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = lean_st_ref_get(v___y_3600_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v___x_3608_);
v___x_3610_ = v___x_3606_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; lean_object* v___x_3614_; 
v___x_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
v___x_3612_ = lean_unsigned_to_nat(0u);
v___x_3613_ = 0;
v___x_3614_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3612_, v___x_3613_, v___x_3611_, v___f_3601_);
return v___x_3614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_3618_, lean_object* v___f_3619_, lean_object* v_x_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_3618_, v___f_3619_, v_x_3620_);
lean_dec(v___y_3618_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; lean_object* v___f_3627_; lean_object* v___f_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; lean_object* v___x_3631_; 
v___x_3626_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3624_);
lean_inc_n(v___y_3624_, 2);
v___f_3627_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_3627_, 0, v_waiter_3623_);
lean_closure_set(v___f_3627_, 1, v___y_3624_);
v___f_3628_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3628_, 0, v___y_3624_);
lean_closure_set(v___f_3628_, 1, v___f_3627_);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = 0;
v___x_3631_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3629_, v___x_3630_, v___x_3626_, v___f_3628_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_3632_, v___y_3633_);
lean_dec(v___y_3633_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_3636_, lean_object* v_waiter_3637_){
_start:
{
lean_object* v___f_3639_; lean_object* v___x_3640_; 
v___f_3639_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3639_, 0, v_waiter_3637_);
v___x_3640_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3636_, v___f_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_3641_, lean_object* v_waiter_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_3641_, v_waiter_3642_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_3645_, lean_object* v___f_3646_, lean_object* v_x_3647_){
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
lean_object* v___x_3661_; lean_object* v___x_3663_; 
v___x_3661_ = lean_st_ref_get(v___y_3645_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 0, v___x_3661_);
v___x_3663_ = v___x_3659_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; lean_object* v___x_3667_; 
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
v___x_3665_ = lean_unsigned_to_nat(0u);
v___x_3666_ = 0;
v___x_3667_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3665_, v___x_3666_, v___x_3664_, v___f_3646_);
return v___x_3667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_3671_, lean_object* v___f_3672_, lean_object* v_x_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_3671_, v___f_3672_, v_x_3673_);
lean_dec(v___y_3671_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___x_3679_; lean_object* v___f_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; lean_object* v___x_3683_; 
v___x_3679_ = l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3677_);
lean_inc(v___y_3677_);
v___f_3680_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_3680_, 0, v___y_3677_);
lean_closure_set(v___f_3680_, 1, v___f_3676_);
v___x_3681_ = lean_unsigned_to_nat(0u);
v___x_3682_ = 0;
v___x_3683_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3681_, v___x_3682_, v___x_3679_, v___f_3680_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_3684_, v___y_3685_);
lean_dec(v___y_3685_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_3691_){
_start:
{
lean_object* v___f_3692_; lean_object* v___f_3693_; lean_object* v___f_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___f_3692_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__1));
lean_inc_ref_n(v_stream_3691_, 2);
v___f_3693_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3693_, 0, v_stream_3691_);
v___f_3694_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_3695_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_3695_, 0, lean_box(0));
lean_closure_set(v___x_3695_, 1, lean_box(0));
lean_closure_set(v___x_3695_, 2, v_stream_3691_);
lean_closure_set(v___x_3695_, 3, v___f_3694_);
v___x_3696_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_3696_, 0, lean_box(0));
lean_closure_set(v___x_3696_, 1, lean_box(0));
lean_closure_set(v___x_3696_, 2, v_stream_3691_);
lean_closure_set(v___x_3696_, 3, v___f_3692_);
v___x_3697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___f_3693_);
lean_ctor_set(v___x_3697_, 2, v___x_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v___y_3698_){
_start:
{
if (lean_obj_tag(v___y_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
v_a_3699_ = lean_ctor_get(v___y_3698_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___y_3698_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___y_3698_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___y_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3715_; 
v_a_3707_ = lean_ctor_get(v___y_3698_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___y_3698_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3709_ = v___y_3698_;
v_isShared_3710_ = v_isSharedCheck_3715_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___y_3698_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3715_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v_fst_3711_; lean_object* v___x_3713_; 
v_fst_3711_ = lean_ctor_get(v_a_3707_, 0);
lean_inc(v_fst_3711_);
lean_dec(v_a_3707_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v_fst_3711_);
v___x_3713_ = v___x_3709_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_fst_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_a_3716_, lean_object* v_x_3717_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Std_Http_Body_Stream_close(v_a_3716_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_a_3720_, lean_object* v_x_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Std_Http_Body_stream___lam__1(v_a_3720_, v_x_3721_);
lean_dec(v_x_3721_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v___x_3724_, lean_object* v___f_3725_, lean_object* v___x_3726_, lean_object* v___f_3727_){
_start:
{
uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___y_3732_; 
v___x_3729_ = 0;
lean_inc(v___x_3726_);
v___x_3730_ = l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(v___x_3724_, v___f_3725_, v___x_3726_, v___x_3729_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3734_; 
lean_dec_ref(v___f_3727_);
lean_dec(v___x_3726_);
v_a_3734_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3734_);
lean_dec_ref(v___x_3730_);
if (lean_obj_tag(v_a_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_a_3735_ = lean_ctor_get(v_a_3734_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_a_3734_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v_a_3734_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v_a_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
v___y_3732_ = v___x_3740_;
goto v___jp_3731_;
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3751_; 
v_a_3743_ = lean_ctor_get(v_a_3734_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_a_3734_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3745_ = v_a_3734_;
v_isShared_3746_ = v_isSharedCheck_3751_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v_a_3734_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3751_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v_fst_3747_; lean_object* v___x_3749_; 
v_fst_3747_ = lean_ctor_get(v_a_3743_, 0);
lean_inc(v_fst_3747_);
lean_dec(v_a_3743_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v_fst_3747_);
v___x_3749_ = v___x_3745_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_fst_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
v___y_3732_ = v___x_3749_;
goto v___jp_3731_;
}
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3760_; 
v_a_3752_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3754_ = v___x_3730_;
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3730_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
v___x_3756_ = lean_task_map(v___f_3727_, v_a_3752_, v___x_3726_, v___x_3729_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_3756_);
v___x_3758_ = v___x_3754_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
v___jp_3731_:
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___y_3732_);
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v___x_3761_, lean_object* v___f_3762_, lean_object* v___x_3763_, lean_object* v___f_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Std_Http_Body_stream___lam__2(v___x_3761_, v___f_3762_, v___x_3763_, v___f_3764_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_x_3767_, lean_object* v_x_3768_){
_start:
{
if (lean_obj_tag(v_x_3768_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3778_; 
lean_dec_ref(v_x_3767_);
v_a_3770_ = lean_ctor_get(v_x_3768_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_x_3768_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3772_ = v_x_3768_;
v_isShared_3773_ = v_isSharedCheck_3778_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v_x_3768_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3778_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
return v___x_3776_;
}
}
}
else
{
lean_object* v___x_3779_; 
lean_dec_ref(v_x_3768_);
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v_x_3767_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_x_3780_, lean_object* v_x_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Std_Http_Body_stream___lam__3(v_x_3780_, v_x_3781_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_3784_, lean_object* v___f_3785_, lean_object* v_x_3786_){
_start:
{
if (lean_obj_tag(v_x_3786_) == 0)
{
lean_object* v___x_3788_; 
lean_dec_ref(v___f_3785_);
lean_dec_ref(v_gen_3784_);
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v_x_3786_);
return v___x_3788_;
}
else
{
lean_object* v_a_3789_; lean_object* v___f_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___f_3793_; lean_object* v___x_3794_; lean_object* v___f_3795_; lean_object* v___x_3796_; uint8_t v___x_3797_; lean_object* v___x_3798_; 
v_a_3789_ = lean_ctor_get(v_x_3786_, 0);
lean_inc_n(v_a_3789_, 2);
v___f_3790_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3790_, 0, v_a_3789_);
v___x_3791_ = lean_apply_1(v_gen_3784_, v_a_3789_);
v___x_3792_ = lean_unsigned_to_nat(0u);
v___f_3793_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 5, 4);
lean_closure_set(v___f_3793_, 0, v___x_3791_);
lean_closure_set(v___f_3793_, 1, v___f_3790_);
lean_closure_set(v___f_3793_, 2, v___x_3792_);
lean_closure_set(v___f_3793_, 3, v___f_3785_);
v___x_3794_ = lean_io_as_task(v___f_3793_, v___x_3792_);
lean_dec_ref(v___x_3794_);
v___f_3795_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3795_, 0, v_x_3786_);
v___x_3796_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
v___x_3797_ = 0;
v___x_3798_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3792_, v___x_3797_, v___x_3796_, v___f_3795_);
return v___x_3798_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_3799_, lean_object* v___f_3800_, lean_object* v_x_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Std_Http_Body_stream___lam__4(v_gen_3799_, v___f_3800_, v_x_3801_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object* v_gen_3805_){
_start:
{
lean_object* v___x_3807_; lean_object* v___f_3808_; lean_object* v___f_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; 
v___x_3807_ = l_Std_Http_Body_mkStream();
v___f_3808_ = ((lean_object*)(l_Std_Http_Body_stream___closed__0));
v___f_3809_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3809_, 0, v_gen_3805_);
lean_closure_set(v___f_3809_, 1, v___f_3808_);
v___x_3810_ = lean_unsigned_to_nat(0u);
v___x_3811_ = 0;
v___x_3812_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3810_, v___x_3811_, v___x_3807_, v___f_3809_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_3813_, lean_object* v_a_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Std_Http_Body_stream(v_gen_3813_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v___x_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v___x_3819_; lean_object* v_pendingProducer_3820_; lean_object* v_pendingConsumer_3821_; lean_object* v_interestWaiter_3822_; uint8_t v_closed_3823_; lean_object* v_pendingIncompleteChunk_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3833_; 
v___x_3819_ = lean_st_ref_take(v___y_3817_);
v_pendingProducer_3820_ = lean_ctor_get(v___x_3819_, 0);
v_pendingConsumer_3821_ = lean_ctor_get(v___x_3819_, 1);
v_interestWaiter_3822_ = lean_ctor_get(v___x_3819_, 2);
v_closed_3823_ = lean_ctor_get_uint8(v___x_3819_, sizeof(void*)*5);
v_pendingIncompleteChunk_3824_ = lean_ctor_get(v___x_3819_, 4);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; 
v_unused_3834_ = lean_ctor_get(v___x_3819_, 3);
lean_dec(v_unused_3834_);
v___x_3826_ = v___x_3819_;
v_isShared_3827_ = v_isSharedCheck_3833_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_pendingIncompleteChunk_3824_);
lean_inc(v_interestWaiter_3822_);
lean_inc(v_pendingConsumer_3821_);
lean_inc(v_pendingProducer_3820_);
lean_dec(v___x_3819_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3833_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 3, v___x_3816_);
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_pendingProducer_3820_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_pendingConsumer_3821_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_interestWaiter_3822_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v_pendingIncompleteChunk_3824_);
lean_ctor_set_uint8(v_reuseFailAlloc_3832_, sizeof(void*)*5, v_closed_3823_);
v___x_3829_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = lean_st_ref_set(v___y_3817_, v___x_3829_);
v___x_3831_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_3831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v___x_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Std_Http_Body_fromBytes___lam__0(v___x_3835_, v___y_3836_);
lean_dec(v___y_3836_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1(lean_object* v___x_3839_, lean_object* v_content_3840_, lean_object* v_s_3841_, lean_object* v_x_3842_){
_start:
{
if (lean_obj_tag(v_x_3842_) == 0)
{
lean_object* v___x_3844_; 
lean_dec_ref(v_s_3841_);
lean_dec_ref(v_content_3840_);
v___x_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3844_, 0, v_x_3842_);
return v___x_3844_;
}
else
{
lean_object* v___x_3845_; uint8_t v___x_3846_; 
lean_dec_ref(v_x_3842_);
v___x_3845_ = lean_unsigned_to_nat(0u);
v___x_3846_ = lean_nat_dec_lt(v___x_3845_, v___x_3839_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
lean_dec_ref(v_s_3841_);
lean_dec_ref(v_content_3840_);
v___x_3847_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1));
return v___x_3847_;
}
else
{
lean_object* v___x_3848_; uint8_t v___x_3849_; lean_object* v___x_3850_; 
v___x_3848_ = l_Std_Http_Chunk_ofByteArray(v_content_3840_);
v___x_3849_ = 0;
v___x_3850_ = l_Std_Http_Body_Stream_send(v_s_3841_, v___x_3848_, v___x_3849_);
return v___x_3850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__1___boxed(lean_object* v___x_3851_, lean_object* v_content_3852_, lean_object* v_s_3853_, lean_object* v_x_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Std_Http_Body_fromBytes___lam__1(v___x_3851_, v_content_3852_, v_s_3853_, v_x_3854_);
lean_dec(v___x_3851_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object* v_content_3857_, lean_object* v_s_3858_){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___f_3863_; lean_object* v___x_3864_; lean_object* v___f_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; lean_object* v___x_3868_; 
v___x_3860_ = lean_byte_array_size(v_content_3857_);
v___x_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
v___f_3863_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3863_, 0, v___x_3862_);
lean_inc_ref(v_s_3858_);
v___x_3864_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_3858_, v___f_3863_);
v___f_3865_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3865_, 0, v___x_3860_);
lean_closure_set(v___f_3865_, 1, v_content_3857_);
lean_closure_set(v___f_3865_, 2, v_s_3858_);
v___x_3866_ = lean_unsigned_to_nat(0u);
v___x_3867_ = 0;
v___x_3868_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3866_, v___x_3867_, v___x_3864_, v___f_3865_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object* v_content_3869_, lean_object* v_s_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Std_Http_Body_fromBytes___lam__2(v_content_3869_, v_s_3870_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_3873_){
_start:
{
lean_object* v___f_3875_; lean_object* v___x_3876_; 
v___f_3875_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3875_, 0, v_content_3873_);
v___x_3876_ = l_Std_Http_Body_stream(v___f_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_3877_, lean_object* v_a_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Std_Http_Body_fromBytes(v_content_3877_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_a_3880_, lean_object* v___f_3881_, lean_object* v_x_3882_){
_start:
{
if (lean_obj_tag(v_x_3882_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3892_; 
lean_dec_ref(v___f_3881_);
lean_dec_ref(v_a_3880_);
v_a_3884_ = lean_ctor_get(v_x_3882_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_x_3882_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3886_ = v_x_3882_;
v_isShared_3887_ = v_isSharedCheck_3892_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v_x_3882_);
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
lean_object* v___x_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; lean_object* v___x_3896_; 
lean_dec_ref(v_x_3882_);
v___x_3893_ = l_Std_Http_Body_Stream_close(v_a_3880_);
v___x_3894_ = lean_unsigned_to_nat(0u);
v___x_3895_ = 0;
v___x_3896_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3894_, v___x_3895_, v___x_3893_, v___f_3881_);
return v___x_3896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_a_3897_, lean_object* v___f_3898_, lean_object* v_x_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Std_Http_Body_empty___lam__2(v_a_3897_, v___f_3898_, v_x_3899_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0(lean_object* v_x_3908_){
_start:
{
if (lean_obj_tag(v_x_3908_) == 0)
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v_x_3908_);
return v___x_3910_;
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3912_; lean_object* v___f_3913_; lean_object* v___x_3914_; lean_object* v___f_3915_; lean_object* v___f_3916_; uint8_t v___x_3917_; lean_object* v___x_3918_; 
v_a_3911_ = lean_ctor_get(v_x_3908_, 0);
lean_inc_n(v_a_3911_, 2);
v___x_3912_ = lean_unsigned_to_nat(0u);
v___f_3913_ = ((lean_object*)(l_Std_Http_Body_empty___lam__0___closed__2));
v___x_3914_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_3911_, v___f_3913_);
v___f_3915_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3915_, 0, v_x_3908_);
v___f_3916_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3916_, 0, v_a_3911_);
lean_closure_set(v___f_3916_, 1, v___f_3915_);
v___x_3917_ = 0;
v___x_3918_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3912_, v___x_3917_, v___x_3914_, v___f_3916_);
return v___x_3918_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__0___boxed(lean_object* v_x_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Std_Http_Body_empty___lam__0(v_x_3919_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___x_3924_; lean_object* v___f_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; lean_object* v___x_3928_; 
v___x_3924_ = l_Std_Http_Body_mkStream();
v___f_3925_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_3926_ = lean_unsigned_to_nat(0u);
v___x_3927_ = 0;
v___x_3928_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3926_, v___x_3927_, v___x_3924_, v___f_3925_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Std_Http_Body_empty();
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_3951_, lean_object* v_f_3952_){
_start:
{
lean_object* v_line_3953_; lean_object* v_body_3954_; lean_object* v_extensions_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3963_; 
v_line_3953_ = lean_ctor_get(v_f_3952_, 0);
v_body_3954_ = lean_ctor_get(v_f_3952_, 1);
v_extensions_3955_ = lean_ctor_get(v_f_3952_, 2);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_f_3952_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3957_ = v_f_3952_;
v_isShared_3958_ = v_isSharedCheck_3963_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_extensions_3955_);
lean_inc(v_body_3954_);
lean_inc(v_line_3953_);
lean_dec(v_f_3952_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3963_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3959_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_3951_, v_body_3954_);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 1, v___x_3959_);
v___x_3961_ = v___x_3957_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_line_3953_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3962_, 2, v_extensions_3955_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_3967_, lean_object* v_x_3968_){
_start:
{
if (lean_obj_tag(v_x_3968_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3978_; 
lean_dec_ref(v___x_3967_);
v_a_3970_ = lean_ctor_get(v_x_3968_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v_x_3968_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3972_ = v_x_3968_;
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v_x_3968_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
return v___x_3976_;
}
}
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3998_; 
v_a_3979_ = lean_ctor_get(v_x_3968_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_x_3968_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3981_ = v_x_3968_;
v_isShared_3982_ = v_isSharedCheck_3998_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v_x_3968_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3998_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v_line_3983_; lean_object* v_body_3984_; lean_object* v_extensions_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3997_; 
v_line_3983_ = lean_ctor_get(v_a_3979_, 0);
v_body_3984_ = lean_ctor_get(v_a_3979_, 1);
v_extensions_3985_ = lean_ctor_get(v_a_3979_, 2);
v_isSharedCheck_3997_ = !lean_is_exclusive(v_a_3979_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3987_ = v_a_3979_;
v_isShared_3988_ = v_isSharedCheck_3997_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_extensions_3985_);
lean_inc(v_body_3984_);
lean_inc(v_line_3983_);
lean_dec(v_a_3979_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3997_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3989_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_3967_, v_body_3984_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 1, v___x_3989_);
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_line_3983_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v___x_3989_);
lean_ctor_set(v_reuseFailAlloc_3996_, 2, v_extensions_3985_);
v___x_3991_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3993_; 
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___x_3991_);
v___x_3993_ = v___x_3981_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_3999_, lean_object* v_x_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_3999_, v_x_4000_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_4003_, lean_object* v_action_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; lean_object* v___x_4010_; 
lean_inc_ref(v___y_4005_);
v___x_4007_ = lean_apply_2(v_action_4004_, v___y_4005_, lean_box(0));
v___x_4008_ = lean_unsigned_to_nat(0u);
v___x_4009_ = 0;
v___x_4010_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4008_, v___x_4009_, v___x_4007_, v___f_4003_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_4011_, lean_object* v_action_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_4011_, v_action_4012_, v___y_4013_);
lean_dec_ref(v___y_4013_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_4021_, lean_object* v_action_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; uint8_t v___x_4027_; lean_object* v___x_4028_; 
v___x_4025_ = lean_apply_1(v_action_4022_, lean_box(0));
v___x_4026_ = lean_unsigned_to_nat(0u);
v___x_4027_ = 0;
v___x_4028_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4026_, v___x_4027_, v___x_4025_, v___f_4021_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_4029_, lean_object* v_action_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_4029_, v_action_4030_, v___y_4031_);
lean_dec_ref(v___y_4031_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_4037_, lean_object* v_x_4038_){
_start:
{
if (lean_obj_tag(v_x_4038_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4048_; 
v_a_4040_ = lean_ctor_get(v_x_4038_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_x_4038_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4042_ = v_x_4038_;
v_isShared_4043_ = v_isSharedCheck_4048_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v_x_4038_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4048_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
lean_object* v___x_4046_; 
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4058_; 
v_a_4049_ = lean_ctor_get(v_x_4038_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_x_4038_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4051_ = v_x_4038_;
v_isShared_4052_ = v_isSharedCheck_4058_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v_x_4038_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4058_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4053_; lean_object* v___x_4055_; 
v___x_4053_ = l_Std_Http_Request_Builder_body___redArg(v_builder_4037_, v_a_4049_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v___x_4053_);
v___x_4055_ = v___x_4051_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; 
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
return v___x_4056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_4059_, lean_object* v_x_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_4059_, v_x_4060_);
lean_dec_ref(v_builder_4059_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_4063_, lean_object* v_gen_4064_){
_start:
{
lean_object* v___x_4066_; lean_object* v___f_4067_; lean_object* v___x_4068_; uint8_t v___x_4069_; lean_object* v___x_4070_; 
v___x_4066_ = l_Std_Http_Body_stream(v_gen_4064_);
v___f_4067_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4067_, 0, v_builder_4063_);
v___x_4068_ = lean_unsigned_to_nat(0u);
v___x_4069_ = 0;
v___x_4070_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4068_, v___x_4069_, v___x_4066_, v___f_4067_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_4071_, lean_object* v_gen_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Std_Http_Request_Builder_stream(v_builder_4071_, v_gen_4072_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_4075_, lean_object* v_x_4076_){
_start:
{
if (lean_obj_tag(v_x_4076_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4086_; 
v_a_4078_ = lean_ctor_get(v_x_4076_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_x_4076_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4080_ = v_x_4076_;
v_isShared_4081_ = v_isSharedCheck_4086_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v_x_4076_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4086_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
return v___x_4084_;
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4096_; 
v_a_4087_ = lean_ctor_get(v_x_4076_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_x_4076_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4089_ = v_x_4076_;
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v_x_4076_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4091_ = l_Std_Http_Response_Builder_body___redArg(v_builder_4075_, v_a_4087_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4091_);
v___x_4093_ = v___x_4089_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4091_);
v___x_4093_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4094_; 
v___x_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
return v___x_4094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_4097_, v_x_4098_);
lean_dec_ref(v_builder_4097_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_4101_, lean_object* v_gen_4102_){
_start:
{
lean_object* v___x_4104_; lean_object* v___f_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; lean_object* v___x_4108_; 
v___x_4104_ = l_Std_Http_Body_stream(v_gen_4102_);
v___f_4105_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4105_, 0, v_builder_4101_);
v___x_4106_ = lean_unsigned_to_nat(0u);
v___x_4107_ = 0;
v___x_4108_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4106_, v___x_4107_, v___x_4104_, v___f_4105_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_4109_, lean_object* v_gen_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Std_Http_Response_Builder_stream(v_builder_4109_, v_gen_4110_);
return v_res_4112_;
}
}
lean_object* runtime_initialize_Std_Sync(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Async(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Chunk(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Body_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Body_Any(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Body_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Body_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Body_Stream(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync(uint8_t builtin);
lean_object* initialize_Std_Internal_Async(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Request(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Response(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Chunk(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Body_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Body_Any(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Body_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Body_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Body_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Body_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Body_Stream(builtin);
}
#ifdef __cplusplus
}
#endif

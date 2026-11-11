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
lean_object* lean_io_promise_new();
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
lean_object* l_IO_Promise_new___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody(lean_object*, lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Chunk_ofByteArray(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_Promise_new___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Body_Stream_close___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "the read was cancelled before the body ended"};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "body exceeded maximum size of "};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " bytes"};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(lean_object*, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Http_Body_Stream_offer___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Stream_offer___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_offer___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_offer___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_offer___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_offer___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_offer___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Stream_offer___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value)}};
static const lean_object* l_Std_Http_Body_Stream_offer___lam__5___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_offer___lam__5___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_offer___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_offer___lam__5___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_offer___lam__5___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_offer___lam__5___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_Stream_offer___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_offer___lam__5___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Stream_offer___lam__5___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_offer___lam__5___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__6(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Stream_offer___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Stream_offer___lam__9___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_offer___lam__9___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_offer___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_offer___lam__9___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_offer___lam__9___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_offer___lam__9___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_Stream_offer___lam__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_offer___lam__9___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Stream_offer___lam__9___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_offer___lam__9___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_offer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_offer___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_offer___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_offer___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Stream_offer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_offer___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_offer___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_offer___closed__1_value;
static const lean_closure_object l_Std_Http_Body_Stream_offer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_offer___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_offer___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_offer___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces_spec__0_spec__0(lean_object* v_as_87_, size_t v_i_88_, size_t v_stop_89_, lean_object* v_b_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = lean_usize_dec_eq(v_i_88_, v_stop_89_);
if (v___x_91_ == 0)
{
size_t v___x_92_; size_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_sub(v_i_88_, v___x_92_);
v___x_94_ = lean_array_uget_borrowed(v_as_87_, v___x_93_);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_byte_array_size(v_b_90_);
v___x_97_ = lean_byte_array_size(v___x_94_);
v___x_98_ = lean_byte_array_copy_slice(v___x_94_, v___x_95_, v_b_90_, v___x_96_, v___x_97_, v___x_91_);
v_i_88_ = v___x_93_;
v_b_90_ = v___x_98_;
goto _start;
}
else
{
return v_b_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces_spec__0_spec__0___boxed(lean_object* v_as_100_, lean_object* v_i_101_, lean_object* v_stop_102_, lean_object* v_b_103_){
_start:
{
size_t v_i_boxed_104_; size_t v_stop_boxed_105_; lean_object* v_res_106_; 
v_i_boxed_104_ = lean_unbox_usize(v_i_101_);
lean_dec(v_i_101_);
v_stop_boxed_105_ = lean_unbox_usize(v_stop_102_);
lean_dec(v_stop_102_);
v_res_106_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces_spec__0_spec__0(v_as_100_, v_i_boxed_104_, v_stop_boxed_105_, v_b_103_);
lean_dec_ref(v_as_100_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces_spec__0(lean_object* v_init_107_, lean_object* v_l_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_109_ = lean_array_mk(v_l_108_);
v___x_110_ = lean_array_get_size(v___x_109_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_nat_dec_lt(v___x_111_, v___x_110_);
if (v___x_112_ == 0)
{
lean_dec_ref(v___x_109_);
return v_init_107_;
}
else
{
size_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_usize_of_nat(v___x_110_);
v___x_114_ = ((size_t)0ULL);
v___x_115_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces_spec__0_spec__0(v___x_109_, v___x_113_, v___x_114_, v_init_107_);
lean_dec_ref(v___x_109_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces(lean_object* v_pieces_116_, lean_object* v_size_117_){
_start:
{
if (lean_obj_tag(v_pieces_116_) == 1)
{
lean_object* v_tail_121_; 
v_tail_121_ = lean_ctor_get(v_pieces_116_, 1);
if (lean_obj_tag(v_tail_121_) == 0)
{
lean_object* v_head_122_; 
v_head_122_ = lean_ctor_get(v_pieces_116_, 0);
lean_inc(v_head_122_);
lean_dec_ref_known(v_pieces_116_, 2);
return v_head_122_;
}
else
{
goto v___jp_118_;
}
}
else
{
goto v___jp_118_;
}
v___jp_118_:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_mk_empty_byte_array(v_size_117_);
v___x_120_ = l_List_foldrTR___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces_spec__0(v___x_119_, v_pieces_116_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces___boxed(lean_object* v_pieces_123_, lean_object* v_size_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces(v_pieces_123_, v_size_124_);
lean_dec(v_size_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_push(lean_object* v_pending_126_, lean_object* v_chunk_127_){
_start:
{
if (lean_obj_tag(v_pending_126_) == 0)
{
lean_object* v_data_128_; lean_object* v_extensions_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_139_; 
v_data_128_ = lean_ctor_get(v_chunk_127_, 0);
v_extensions_129_ = lean_ctor_get(v_chunk_127_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_chunk_127_);
if (v_isSharedCheck_139_ == 0)
{
v___x_131_ = v_chunk_127_;
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_extensions_129_);
lean_inc(v_data_128_);
lean_dec(v_chunk_127_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_133_ = lean_box(0);
lean_inc_ref(v_data_128_);
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 1);
lean_ctor_set(v___x_131_, 1, v___x_133_);
v___x_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_data_128_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_138_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_byte_array_size(v_data_128_);
lean_dec_ref(v_data_128_);
v___x_137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
lean_ctor_set(v___x_137_, 2, v_extensions_129_);
return v___x_137_;
}
}
}
else
{
lean_object* v_val_140_; lean_object* v_data_141_; lean_object* v_extensions_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_167_; 
v_val_140_ = lean_ctor_get(v_pending_126_, 0);
lean_inc(v_val_140_);
lean_dec_ref_known(v_pending_126_, 1);
v_data_141_ = lean_ctor_get(v_chunk_127_, 0);
v_extensions_142_ = lean_ctor_get(v_chunk_127_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_chunk_127_);
if (v_isSharedCheck_167_ == 0)
{
v___x_144_ = v_chunk_127_;
v_isShared_145_ = v_isSharedCheck_167_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_extensions_142_);
lean_inc(v_data_141_);
lean_dec(v_chunk_127_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_167_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_pieces_146_; lean_object* v_size_147_; lean_object* v_extensions_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_166_; 
v_pieces_146_ = lean_ctor_get(v_val_140_, 0);
v_size_147_ = lean_ctor_get(v_val_140_, 1);
v_extensions_148_ = lean_ctor_get(v_val_140_, 2);
v_isSharedCheck_166_ = !lean_is_exclusive(v_val_140_);
if (v_isSharedCheck_166_ == 0)
{
v___x_150_ = v_val_140_;
v_isShared_151_ = v_isSharedCheck_166_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_extensions_148_);
lean_inc(v_size_147_);
lean_inc(v_pieces_146_);
lean_dec(v_val_140_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_166_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
lean_inc_ref(v_data_141_);
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 1);
lean_ctor_set(v___x_144_, 1, v_pieces_146_);
v___x_153_ = v___x_144_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_data_141_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_pieces_146_);
v___x_153_ = v_reuseFailAlloc_165_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_154_ = lean_byte_array_size(v_data_141_);
lean_dec_ref(v_data_141_);
v___x_155_ = lean_nat_add(v_size_147_, v___x_154_);
lean_dec(v_size_147_);
v___x_156_ = lean_array_get_size(v_extensions_148_);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_nat_dec_eq(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_160_; 
lean_dec_ref(v_extensions_142_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_155_);
lean_ctor_set(v___x_150_, 0, v___x_153_);
v___x_160_ = v___x_150_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_extensions_148_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
else
{
lean_object* v___x_163_; 
lean_dec_ref(v_extensions_148_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 2, v_extensions_142_);
lean_ctor_set(v___x_150_, 1, v___x_155_);
lean_ctor_set(v___x_150_, 0, v___x_153_);
v___x_163_ = v___x_150_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_extensions_142_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(lean_object* v_pending_168_){
_start:
{
lean_object* v_pieces_169_; lean_object* v_size_170_; lean_object* v_extensions_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_pieces_169_ = lean_ctor_get(v_pending_168_, 0);
lean_inc(v_pieces_169_);
v_size_170_ = lean_ctor_get(v_pending_168_, 1);
lean_inc(v_size_170_);
v_extensions_171_ = lean_ctor_get(v_pending_168_, 2);
lean_inc_ref(v_extensions_171_);
lean_dec_ref(v_pending_168_);
v___x_172_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces(v_pieces_169_, v_size_170_);
lean_dec(v_size_170_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_extensions_171_);
return v___x_173_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(uint8_t v_x_174_, lean_object* v_w_175_, lean_object* v_lose_176_){
_start:
{
lean_object* v_finished_178_; lean_object* v_promise_179_; lean_object* v___x_180_; uint8_t v___y_182_; uint8_t v___x_191_; 
v_finished_178_ = lean_ctor_get(v_w_175_, 0);
v_promise_179_ = lean_ctor_get(v_w_175_, 1);
v___x_180_ = lean_st_ref_take(v_finished_178_);
v___x_191_ = lean_unbox(v___x_180_);
lean_dec(v___x_180_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; 
v___x_192_ = 1;
v___y_182_ = v___x_192_;
goto v___jp_181_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = 0;
v___y_182_ = v___x_193_;
goto v___jp_181_;
}
v___jp_181_:
{
uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = 1;
v___x_184_ = lean_box(v___x_183_);
v___x_185_ = lean_st_ref_put(v_finished_178_, v___x_184_);
if (v___y_182_ == 0)
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_apply_1(v_lose_176_, lean_box(0));
v___x_187_ = lean_unbox(v___x_186_);
return v___x_187_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec_ref(v_lose_176_);
v___x_188_ = lean_box(v_x_174_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
v___x_190_ = lean_io_promise_resolve(v___x_189_, v_promise_179_);
return v___y_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0___boxed(lean_object* v_x_194_, lean_object* v_w_195_, lean_object* v_lose_196_, lean_object* v___y_197_){
_start:
{
uint8_t v_x_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_x_boxed_198_ = lean_unbox(v_x_194_);
v_res_199_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_boxed_198_, v_w_195_, v_lose_196_);
lean_dec_ref(v_w_195_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(lean_object* v_waiter_201_, uint8_t v_x_202_){
_start:
{
lean_object* v_lose_204_; uint8_t v___x_205_; 
v_lose_204_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0));
v___x_205_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_202_, v_waiter_201_, v_lose_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed(lean_object* v_waiter_206_, lean_object* v_x_207_, lean_object* v_a_208_){
_start:
{
uint8_t v_x_boxed_209_; uint8_t v_res_210_; lean_object* v_r_211_; 
v_x_boxed_209_ = lean_unbox(v_x_207_);
v_res_210_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_waiter_206_, v_x_boxed_209_);
lean_dec_ref(v_waiter_206_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0(lean_object* v_x_223_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
v_a_225_ = lean_ctor_get(v_x_223_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_233_ == 0)
{
v___x_227_ = v_x_223_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v_x_223_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_242_; 
v_a_234_ = lean_ctor_get(v_x_223_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_242_ == 0)
{
v___x_236_ = v_x_223_;
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v_x_223_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_241_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0___boxed(lean_object* v_x_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Http_Body_mkStream___lam__0(v_x_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream(){
_start:
{
lean_object* v___f_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___f_251_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__0));
v___x_252_ = 0;
v___x_253_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__1));
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l_Std_Mutex_new___redArg(v___x_253_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___x_258_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_254_, v___x_252_, v___x_257_, v___f_251_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___boxed(lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_Http_Body_mkStream();
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object* v_knownSize_261_, lean_object* v_chunk_262_){
_start:
{
if (lean_obj_tag(v_knownSize_261_) == 1)
{
lean_object* v_val_263_; 
v_val_263_ = lean_ctor_get(v_knownSize_261_, 0);
lean_inc(v_val_263_);
if (lean_obj_tag(v_val_263_) == 1)
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_281_; 
v_isSharedCheck_281_ = !lean_is_exclusive(v_knownSize_261_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v_knownSize_261_, 0);
lean_dec(v_unused_282_);
v___x_265_ = v_knownSize_261_;
v_isShared_266_ = v_isSharedCheck_281_;
goto v_resetjp_264_;
}
else
{
lean_dec(v_knownSize_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_281_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_n_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_280_; 
v_n_267_ = lean_ctor_get(v_val_263_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v_val_263_);
if (v_isSharedCheck_280_ == 0)
{
v___x_269_ = v_val_263_;
v_isShared_270_ = v_isSharedCheck_280_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_n_267_);
lean_dec(v_val_263_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_280_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v_data_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v_data_271_ = lean_ctor_get(v_chunk_262_, 0);
v___x_272_ = lean_byte_array_size(v_data_271_);
v___x_273_ = lean_nat_sub(v_n_267_, v___x_272_);
lean_dec(v_n_267_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_273_);
v___x_275_ = v___x_269_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_277_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_275_);
v___x_277_ = v___x_265_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
else
{
lean_dec(v_val_263_);
return v_knownSize_261_;
}
}
else
{
return v_knownSize_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object* v_knownSize_283_, lean_object* v_chunk_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_283_, v_chunk_284_);
lean_dec_ref(v_chunk_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object* v_pendingProducer_286_, lean_object* v_pendingConsumer_287_, uint8_t v_closed_288_, lean_object* v_knownSize_289_, lean_object* v_pendingIncomplete_290_, lean_object* v_closeError_291_, uint8_t v_closeAfterProducer_292_, lean_object* v_inst_293_, lean_object* v_interestWaiter_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_296_, 0, v_pendingProducer_286_);
lean_ctor_set(v___x_296_, 1, v_pendingConsumer_287_);
lean_ctor_set(v___x_296_, 2, v_interestWaiter_294_);
lean_ctor_set(v___x_296_, 3, v_knownSize_289_);
lean_ctor_set(v___x_296_, 4, v_pendingIncomplete_290_);
lean_ctor_set(v___x_296_, 5, v_closeError_291_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*6, v_closed_288_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*6 + 1, v_closeAfterProducer_292_);
lean_inc(v___y_295_);
v___x_297_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_297_, 0, lean_box(0));
lean_closure_set(v___x_297_, 1, lean_box(0));
lean_closure_set(v___x_297_, 2, v___y_295_);
lean_closure_set(v___x_297_, 3, v___x_296_);
v___x_298_ = lean_apply_2(v_inst_293_, lean_box(0), v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object* v_pendingProducer_299_, lean_object* v_pendingConsumer_300_, lean_object* v_closed_301_, lean_object* v_knownSize_302_, lean_object* v_pendingIncomplete_303_, lean_object* v_closeError_304_, lean_object* v_closeAfterProducer_305_, lean_object* v_inst_306_, lean_object* v_interestWaiter_307_, lean_object* v___y_308_){
_start:
{
uint8_t v_closed_boxed_309_; uint8_t v_closeAfterProducer_boxed_310_; lean_object* v_res_311_; 
v_closed_boxed_309_ = lean_unbox(v_closed_301_);
v_closeAfterProducer_boxed_310_ = lean_unbox(v_closeAfterProducer_305_);
v_res_311_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(v_pendingProducer_299_, v_pendingConsumer_300_, v_closed_boxed_309_, v_knownSize_302_, v_pendingIncomplete_303_, v_closeError_304_, v_closeAfterProducer_boxed_310_, v_inst_306_, v_interestWaiter_307_, v___y_308_);
lean_dec(v___y_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object* v___f_312_, lean_object* v___y_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_315_; 
lean_inc(v___y_313_);
v___x_315_ = lean_apply_2(v___f_312_, v_a_314_, v___y_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object* v___f_316_, lean_object* v___y_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(v___f_316_, v___y_317_, v_a_318_);
lean_dec(v___y_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object* v_toApplicative_320_, lean_object* v_interestWaiter_321_, lean_object* v_toBind_322_, lean_object* v___f_323_, lean_object* v___f_324_, uint8_t v_a_325_){
_start:
{
if (v_a_325_ == 0)
{
lean_object* v_toPure_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v___f_324_);
v_toPure_326_ = lean_ctor_get(v_toApplicative_320_, 1);
lean_inc(v_toPure_326_);
lean_dec_ref(v_toApplicative_320_);
v___x_327_ = lean_apply_2(v_toPure_326_, lean_box(0), v_interestWaiter_321_);
v___x_328_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_327_, v___f_323_);
return v___x_328_;
}
else
{
lean_object* v_toPure_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v___f_323_);
lean_dec(v_interestWaiter_321_);
v_toPure_329_ = lean_ctor_get(v_toApplicative_320_, 1);
lean_inc(v_toPure_329_);
lean_dec_ref(v_toApplicative_320_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_apply_2(v_toPure_329_, lean_box(0), v___x_330_);
v___x_332_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_331_, v___f_324_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object* v_toApplicative_333_, lean_object* v_interestWaiter_334_, lean_object* v_toBind_335_, lean_object* v___f_336_, lean_object* v___f_337_, lean_object* v_a_338_){
_start:
{
uint8_t v_a_boxed_339_; lean_object* v_res_340_; 
v_a_boxed_339_ = lean_unbox(v_a_338_);
v_res_340_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(v_toApplicative_333_, v_interestWaiter_334_, v_toBind_335_, v___f_336_, v___f_337_, v_a_boxed_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object* v_pendingProducer_341_, uint8_t v_closed_342_, lean_object* v_knownSize_343_, lean_object* v_pendingIncomplete_344_, lean_object* v_closeError_345_, uint8_t v_closeAfterProducer_346_, lean_object* v_inst_347_, lean_object* v_interestWaiter_348_, lean_object* v_toApplicative_349_, lean_object* v_toBind_350_, lean_object* v_pendingConsumer_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___f_355_; 
v___x_353_ = lean_box(v_closed_342_);
v___x_354_ = lean_box(v_closeAfterProducer_346_);
lean_inc(v_inst_347_);
v___f_355_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed), 10, 8);
lean_closure_set(v___f_355_, 0, v_pendingProducer_341_);
lean_closure_set(v___f_355_, 1, v_pendingConsumer_351_);
lean_closure_set(v___f_355_, 2, v___x_353_);
lean_closure_set(v___f_355_, 3, v_knownSize_343_);
lean_closure_set(v___f_355_, 4, v_pendingIncomplete_344_);
lean_closure_set(v___f_355_, 5, v_closeError_345_);
lean_closure_set(v___f_355_, 6, v___x_354_);
lean_closure_set(v___f_355_, 7, v_inst_347_);
if (lean_obj_tag(v_interestWaiter_348_) == 0)
{
lean_object* v_toPure_356_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_inst_347_);
v_toPure_356_ = lean_ctor_get(v_toApplicative_349_, 1);
lean_inc(v_toPure_356_);
lean_dec_ref(v_toApplicative_349_);
lean_inc(v___y_352_);
v___f_357_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_357_, 0, v___f_355_);
lean_closure_set(v___f_357_, 1, v___y_352_);
v___x_358_ = lean_apply_2(v_toPure_356_, lean_box(0), v_interestWaiter_348_);
v___x_359_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_358_, v___f_357_);
return v___x_359_;
}
else
{
lean_object* v_val_360_; lean_object* v_finished_361_; lean_object* v___f_362_; lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_val_360_ = lean_ctor_get(v_interestWaiter_348_, 0);
v_finished_361_ = lean_ctor_get(v_val_360_, 0);
lean_inc(v_finished_361_);
lean_inc(v___y_352_);
v___f_362_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_362_, 0, v___f_355_);
lean_closure_set(v___f_362_, 1, v___y_352_);
lean_inc_ref(v___f_362_);
lean_inc(v_toBind_350_);
v___f_363_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_363_, 0, v_toApplicative_349_);
lean_closure_set(v___f_363_, 1, v_interestWaiter_348_);
lean_closure_set(v___f_363_, 2, v_toBind_350_);
lean_closure_set(v___f_363_, 3, v___f_362_);
lean_closure_set(v___f_363_, 4, v___f_362_);
v___x_364_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_364_, 0, lean_box(0));
lean_closure_set(v___x_364_, 1, lean_box(0));
lean_closure_set(v___x_364_, 2, v_finished_361_);
v___x_365_ = lean_apply_2(v_inst_347_, lean_box(0), v___x_364_);
v___x_366_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_365_, v___f_363_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object* v_pendingProducer_367_, lean_object* v_closed_368_, lean_object* v_knownSize_369_, lean_object* v_pendingIncomplete_370_, lean_object* v_closeError_371_, lean_object* v_closeAfterProducer_372_, lean_object* v_inst_373_, lean_object* v_interestWaiter_374_, lean_object* v_toApplicative_375_, lean_object* v_toBind_376_, lean_object* v_pendingConsumer_377_, lean_object* v___y_378_){
_start:
{
uint8_t v_closed_boxed_379_; uint8_t v_closeAfterProducer_boxed_380_; lean_object* v_res_381_; 
v_closed_boxed_379_ = lean_unbox(v_closed_368_);
v_closeAfterProducer_boxed_380_ = lean_unbox(v_closeAfterProducer_372_);
v_res_381_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(v_pendingProducer_367_, v_closed_boxed_379_, v_knownSize_369_, v_pendingIncomplete_370_, v_closeError_371_, v_closeAfterProducer_boxed_380_, v_inst_373_, v_interestWaiter_374_, v_toApplicative_375_, v_toBind_376_, v_pendingConsumer_377_, v___y_378_);
lean_dec(v___y_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(lean_object* v___f_382_, lean_object* v___y_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_385_; 
lean_inc(v___y_383_);
v___x_385_ = lean_apply_2(v___f_382_, v_a_384_, v___y_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(lean_object* v___f_386_, lean_object* v___y_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(v___f_386_, v___y_387_, v_a_388_);
lean_dec(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(lean_object* v___f_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_393_; 
lean_inc(v_a_391_);
v___x_393_ = lean_apply_2(v___f_390_, v_a_392_, v_a_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(lean_object* v___f_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(v___f_394_, v_a_395_, v_a_396_);
lean_dec(v_a_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(lean_object* v_toApplicative_398_, lean_object* v_pendingConsumer_399_, lean_object* v_toBind_400_, lean_object* v___f_401_, lean_object* v___f_402_, uint8_t v_a_403_){
_start:
{
if (v_a_403_ == 0)
{
lean_object* v_toPure_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v___f_402_);
v_toPure_404_ = lean_ctor_get(v_toApplicative_398_, 1);
lean_inc(v_toPure_404_);
lean_dec_ref(v_toApplicative_398_);
v___x_405_ = lean_apply_2(v_toPure_404_, lean_box(0), v_pendingConsumer_399_);
v___x_406_ = lean_apply_4(v_toBind_400_, lean_box(0), lean_box(0), v___x_405_, v___f_401_);
return v___x_406_;
}
else
{
lean_object* v_toPure_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v___f_401_);
lean_dec(v_pendingConsumer_399_);
v_toPure_407_ = lean_ctor_get(v_toApplicative_398_, 1);
lean_inc(v_toPure_407_);
lean_dec_ref(v_toApplicative_398_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_apply_2(v_toPure_407_, lean_box(0), v___x_408_);
v___x_410_ = lean_apply_4(v_toBind_400_, lean_box(0), lean_box(0), v___x_409_, v___f_402_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(lean_object* v_toApplicative_411_, lean_object* v_pendingConsumer_412_, lean_object* v_toBind_413_, lean_object* v___f_414_, lean_object* v___f_415_, lean_object* v_a_416_){
_start:
{
uint8_t v_a_boxed_417_; lean_object* v_res_418_; 
v_a_boxed_417_ = lean_unbox(v_a_416_);
v_res_418_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(v_toApplicative_411_, v_pendingConsumer_412_, v_toBind_413_, v___f_414_, v___f_415_, v_a_boxed_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(lean_object* v_inst_419_, lean_object* v_toApplicative_420_, lean_object* v_toBind_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_pendingProducer_424_; lean_object* v_pendingConsumer_425_; lean_object* v_interestWaiter_426_; uint8_t v_closed_427_; lean_object* v_knownSize_428_; lean_object* v_pendingIncomplete_429_; lean_object* v_closeError_430_; uint8_t v_closeAfterProducer_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___f_434_; lean_object* v___y_436_; 
v_pendingProducer_424_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_pendingProducer_424_);
v_pendingConsumer_425_ = lean_ctor_get(v_a_423_, 1);
lean_inc(v_pendingConsumer_425_);
v_interestWaiter_426_ = lean_ctor_get(v_a_423_, 2);
lean_inc(v_interestWaiter_426_);
v_closed_427_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*6);
v_knownSize_428_ = lean_ctor_get(v_a_423_, 3);
lean_inc(v_knownSize_428_);
v_pendingIncomplete_429_ = lean_ctor_get(v_a_423_, 4);
lean_inc(v_pendingIncomplete_429_);
v_closeError_430_ = lean_ctor_get(v_a_423_, 5);
lean_inc(v_closeError_430_);
v_closeAfterProducer_431_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*6 + 1);
lean_dec_ref(v_a_423_);
v___x_432_ = lean_box(v_closed_427_);
v___x_433_ = lean_box(v_closeAfterProducer_431_);
lean_inc(v_toBind_421_);
lean_inc_ref(v_toApplicative_420_);
lean_inc(v_inst_419_);
v___f_434_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_434_, 0, v_pendingProducer_424_);
lean_closure_set(v___f_434_, 1, v___x_432_);
lean_closure_set(v___f_434_, 2, v_knownSize_428_);
lean_closure_set(v___f_434_, 3, v_pendingIncomplete_429_);
lean_closure_set(v___f_434_, 4, v_closeError_430_);
lean_closure_set(v___f_434_, 5, v___x_433_);
lean_closure_set(v___f_434_, 6, v_inst_419_);
lean_closure_set(v___f_434_, 7, v_interestWaiter_426_);
lean_closure_set(v___f_434_, 8, v_toApplicative_420_);
lean_closure_set(v___f_434_, 9, v_toBind_421_);
if (lean_obj_tag(v_pendingConsumer_425_) == 1)
{
lean_object* v_val_441_; 
v_val_441_ = lean_ctor_get(v_pendingConsumer_425_, 0);
if (lean_obj_tag(v_val_441_) == 1)
{
lean_object* v_finished_442_; lean_object* v_finished_443_; lean_object* v___f_444_; lean_object* v___f_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_finished_442_ = lean_ctor_get(v_val_441_, 0);
v_finished_443_ = lean_ctor_get(v_finished_442_, 0);
lean_inc(v_finished_443_);
lean_inc(v_a_422_);
v___f_444_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_444_, 0, v___f_434_);
lean_closure_set(v___f_444_, 1, v_a_422_);
lean_inc_ref(v___f_444_);
lean_inc(v_toBind_421_);
v___f_445_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_445_, 0, v_toApplicative_420_);
lean_closure_set(v___f_445_, 1, v_pendingConsumer_425_);
lean_closure_set(v___f_445_, 2, v_toBind_421_);
lean_closure_set(v___f_445_, 3, v___f_444_);
lean_closure_set(v___f_445_, 4, v___f_444_);
v___x_446_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_446_, 0, lean_box(0));
lean_closure_set(v___x_446_, 1, lean_box(0));
lean_closure_set(v___x_446_, 2, v_finished_443_);
v___x_447_ = lean_apply_2(v_inst_419_, lean_box(0), v___x_446_);
v___x_448_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v___x_447_, v___f_445_);
return v___x_448_;
}
else
{
lean_dec(v_inst_419_);
v___y_436_ = v_a_422_;
goto v___jp_435_;
}
}
else
{
lean_dec(v_inst_419_);
v___y_436_ = v_a_422_;
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v_toPure_437_; lean_object* v___f_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_toPure_437_ = lean_ctor_get(v_toApplicative_420_, 1);
lean_inc(v_toPure_437_);
lean_dec_ref(v_toApplicative_420_);
lean_inc(v___y_436_);
v___f_438_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_438_, 0, v___f_434_);
lean_closure_set(v___f_438_, 1, v___y_436_);
v___x_439_ = lean_apply_2(v_toPure_437_, lean_box(0), v_pendingConsumer_425_);
v___x_440_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v___x_439_, v___f_438_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(lean_object* v_inst_449_, lean_object* v_toApplicative_450_, lean_object* v_toBind_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(v_inst_449_, v_toApplicative_450_, v_toBind_451_, v_a_452_, v_a_453_);
lean_dec(v_a_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_toApplicative_458_; lean_object* v_toBind_459_; lean_object* v___f_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_toApplicative_458_ = lean_ctor_get(v_inst_455_, 0);
lean_inc_ref(v_toApplicative_458_);
v_toBind_459_ = lean_ctor_get(v_inst_455_, 1);
lean_inc_n(v_toBind_459_, 2);
lean_dec_ref(v_inst_455_);
lean_inc_n(v_a_457_, 2);
lean_inc(v_inst_456_);
v___f_460_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_460_, 0, v_inst_456_);
lean_closure_set(v___f_460_, 1, v_toApplicative_458_);
lean_closure_set(v___f_460_, 2, v_toBind_459_);
lean_closure_set(v___f_460_, 3, v_a_457_);
v___x_461_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_461_, 0, lean_box(0));
lean_closure_set(v___x_461_, 1, lean_box(0));
lean_closure_set(v___x_461_, 2, v_a_457_);
v___x_462_ = lean_apply_2(v_inst_456_, lean_box(0), v___x_461_);
v___x_463_ = lean_apply_4(v_toBind_459_, lean_box(0), lean_box(0), v___x_462_, v___f_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_464_, v_inst_465_, v_a_466_);
lean_dec(v_a_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(lean_object* v_m_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_469_, v_inst_470_, v_a_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(lean_object* v_m_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(v_m_473_, v_inst_474_, v_inst_475_, v_a_476_);
lean_dec(v_a_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object* v_pendingProducer_478_, lean_object* v_pendingConsumer_479_, uint8_t v_closed_480_, lean_object* v_knownSize_481_, lean_object* v_pendingIncomplete_482_, lean_object* v_closeError_483_, uint8_t v_closeAfterProducer_484_, lean_object* v_a_485_, lean_object* v_inst_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_489_, 0, v_pendingProducer_478_);
lean_ctor_set(v___x_489_, 1, v_pendingConsumer_479_);
lean_ctor_set(v___x_489_, 2, v___x_488_);
lean_ctor_set(v___x_489_, 3, v_knownSize_481_);
lean_ctor_set(v___x_489_, 4, v_pendingIncomplete_482_);
lean_ctor_set(v___x_489_, 5, v_closeError_483_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*6, v_closed_480_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*6 + 1, v_closeAfterProducer_484_);
lean_inc(v_a_485_);
v___x_490_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_490_, 0, lean_box(0));
lean_closure_set(v___x_490_, 1, lean_box(0));
lean_closure_set(v___x_490_, 2, v_a_485_);
lean_closure_set(v___x_490_, 3, v___x_489_);
v___x_491_ = lean_apply_2(v_inst_486_, lean_box(0), v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object* v_pendingProducer_492_, lean_object* v_pendingConsumer_493_, lean_object* v_closed_494_, lean_object* v_knownSize_495_, lean_object* v_pendingIncomplete_496_, lean_object* v_closeError_497_, lean_object* v_closeAfterProducer_498_, lean_object* v_a_499_, lean_object* v_inst_500_, lean_object* v_a_501_){
_start:
{
uint8_t v_closed_boxed_502_; uint8_t v_closeAfterProducer_boxed_503_; lean_object* v_res_504_; 
v_closed_boxed_502_ = lean_unbox(v_closed_494_);
v_closeAfterProducer_boxed_503_ = lean_unbox(v_closeAfterProducer_498_);
v_res_504_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(v_pendingProducer_492_, v_pendingConsumer_493_, v_closed_boxed_502_, v_knownSize_495_, v_pendingIncomplete_496_, v_closeError_497_, v_closeAfterProducer_boxed_503_, v_a_499_, v_inst_500_, v_a_501_);
lean_dec(v_a_499_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(lean_object* v_toApplicative_505_, lean_object* v_a_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_toBind_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_interestWaiter_511_; 
v_interestWaiter_511_ = lean_ctor_get(v_a_510_, 2);
lean_inc(v_interestWaiter_511_);
if (lean_obj_tag(v_interestWaiter_511_) == 1)
{
lean_object* v_toFunctor_512_; lean_object* v_pendingProducer_513_; lean_object* v_pendingConsumer_514_; uint8_t v_closed_515_; lean_object* v_knownSize_516_; lean_object* v_pendingIncomplete_517_; lean_object* v_closeError_518_; uint8_t v_closeAfterProducer_519_; lean_object* v_val_520_; lean_object* v_mapConst_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___f_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_toFunctor_512_ = lean_ctor_get(v_toApplicative_505_, 0);
lean_inc_ref(v_toFunctor_512_);
lean_dec_ref(v_toApplicative_505_);
v_pendingProducer_513_ = lean_ctor_get(v_a_510_, 0);
lean_inc(v_pendingProducer_513_);
v_pendingConsumer_514_ = lean_ctor_get(v_a_510_, 1);
lean_inc(v_pendingConsumer_514_);
v_closed_515_ = lean_ctor_get_uint8(v_a_510_, sizeof(void*)*6);
v_knownSize_516_ = lean_ctor_get(v_a_510_, 3);
lean_inc(v_knownSize_516_);
v_pendingIncomplete_517_ = lean_ctor_get(v_a_510_, 4);
lean_inc(v_pendingIncomplete_517_);
v_closeError_518_ = lean_ctor_get(v_a_510_, 5);
lean_inc(v_closeError_518_);
v_closeAfterProducer_519_ = lean_ctor_get_uint8(v_a_510_, sizeof(void*)*6 + 1);
lean_dec_ref(v_a_510_);
v_val_520_ = lean_ctor_get(v_interestWaiter_511_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v_interestWaiter_511_, 1);
v_mapConst_521_ = lean_ctor_get(v_toFunctor_512_, 1);
lean_inc(v_mapConst_521_);
lean_dec_ref(v_toFunctor_512_);
v___x_522_ = lean_box(v_closed_515_);
v___x_523_ = lean_box(v_closeAfterProducer_519_);
lean_inc(v_a_506_);
v___f_524_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_524_, 0, v_pendingProducer_513_);
lean_closure_set(v___f_524_, 1, v_pendingConsumer_514_);
lean_closure_set(v___f_524_, 2, v___x_522_);
lean_closure_set(v___f_524_, 3, v_knownSize_516_);
lean_closure_set(v___f_524_, 4, v_pendingIncomplete_517_);
lean_closure_set(v___f_524_, 5, v_closeError_518_);
lean_closure_set(v___f_524_, 6, v___x_523_);
lean_closure_set(v___f_524_, 7, v_a_506_);
lean_closure_set(v___f_524_, 8, v_inst_507_);
v___x_525_ = 1;
v___x_526_ = lean_box(v___x_525_);
v___x_527_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_527_, 0, v_val_520_);
lean_closure_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_apply_2(v_inst_508_, lean_box(0), v___x_527_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_apply_4(v_mapConst_521_, lean_box(0), lean_box(0), v___x_529_, v___x_528_);
v___x_531_ = lean_apply_4(v_toBind_509_, lean_box(0), lean_box(0), v___x_530_, v___f_524_);
return v___x_531_;
}
else
{
lean_object* v_toPure_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v_interestWaiter_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_toBind_509_);
lean_dec(v_inst_508_);
lean_dec(v_inst_507_);
v_toPure_532_ = lean_ctor_get(v_toApplicative_505_, 1);
lean_inc(v_toPure_532_);
lean_dec_ref(v_toApplicative_505_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_apply_2(v_toPure_532_, lean_box(0), v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(lean_object* v_toApplicative_535_, lean_object* v_a_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_toBind_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(v_toApplicative_535_, v_a_536_, v_inst_537_, v_inst_538_, v_toBind_539_, v_a_540_);
lean_dec(v_a_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_toApplicative_546_; lean_object* v_toBind_547_; lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_toApplicative_546_ = lean_ctor_get(v_inst_542_, 0);
lean_inc_ref(v_toApplicative_546_);
v_toBind_547_ = lean_ctor_get(v_inst_542_, 1);
lean_inc_n(v_toBind_547_, 2);
lean_dec_ref(v_inst_542_);
lean_inc(v_inst_543_);
lean_inc_n(v_a_545_, 2);
v___f_548_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_548_, 0, v_toApplicative_546_);
lean_closure_set(v___f_548_, 1, v_a_545_);
lean_closure_set(v___f_548_, 2, v_inst_543_);
lean_closure_set(v___f_548_, 3, v_inst_544_);
lean_closure_set(v___f_548_, 4, v_toBind_547_);
v___x_549_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_549_, 0, lean_box(0));
lean_closure_set(v___x_549_, 1, lean_box(0));
lean_closure_set(v___x_549_, 2, v_a_545_);
v___x_550_ = lean_apply_2(v_inst_543_, lean_box(0), v___x_549_);
v___x_551_ = lean_apply_4(v_toBind_547_, lean_box(0), lean_box(0), v___x_550_, v___f_548_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_552_, v_inst_553_, v_inst_554_, v_a_555_);
lean_dec(v_a_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(lean_object* v_m_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_558_, v_inst_559_, v_inst_560_, v_a_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(lean_object* v_m_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(v_m_563_, v_inst_564_, v_inst_565_, v_inst_566_, v_a_567_);
lean_dec(v_a_567_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_569_, lean_object* v_a_570_){
_start:
{
uint8_t v___y_572_; lean_object* v_pendingProducer_576_; 
v_pendingProducer_576_ = lean_ctor_get(v_a_570_, 0);
if (lean_obj_tag(v_pendingProducer_576_) == 0)
{
uint8_t v_closed_577_; 
v_closed_577_ = lean_ctor_get_uint8(v_a_570_, sizeof(void*)*6);
v___y_572_ = v_closed_577_;
goto v___jp_571_;
}
else
{
uint8_t v___x_578_; 
v___x_578_ = 1;
v___y_572_ = v___x_578_;
goto v___jp_571_;
}
v___jp_571_:
{
lean_object* v_toPure_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_toPure_573_ = lean_ctor_get(v_toApplicative_569_, 1);
lean_inc(v_toPure_573_);
lean_dec_ref(v_toApplicative_569_);
v___x_574_ = lean_box(v___y_572_);
v___x_575_ = lean_apply_2(v_toPure_573_, lean_box(0), v___x_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(v_toApplicative_579_, v_a_580_);
lean_dec_ref(v_a_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_toApplicative_585_; lean_object* v_toBind_586_; lean_object* v___f_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_toApplicative_585_ = lean_ctor_get(v_inst_582_, 0);
lean_inc_ref(v_toApplicative_585_);
v_toBind_586_ = lean_ctor_get(v_inst_582_, 1);
lean_inc(v_toBind_586_);
lean_dec_ref(v_inst_582_);
v___f_587_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_587_, 0, v_toApplicative_585_);
lean_inc(v_a_584_);
v___x_588_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_588_, 0, lean_box(0));
lean_closure_set(v___x_588_, 1, lean_box(0));
lean_closure_set(v___x_588_, 2, v_a_584_);
v___x_589_ = lean_apply_2(v_inst_583_, lean_box(0), v___x_588_);
v___x_590_ = lean_apply_4(v_toBind_586_, lean_box(0), lean_box(0), v___x_589_, v___f_587_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_591_, v_inst_592_, v_a_593_);
lean_dec(v_a_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(lean_object* v_m_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_596_, v_inst_597_, v_a_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(lean_object* v_m_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(v_m_600_, v_inst_601_, v_inst_602_, v_a_603_);
lean_dec(v_a_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(lean_object* v_toApplicative_605_, lean_object* v_a_606_){
_start:
{
uint8_t v___y_608_; lean_object* v_pendingConsumer_612_; 
v_pendingConsumer_612_ = lean_ctor_get(v_a_606_, 1);
if (lean_obj_tag(v_pendingConsumer_612_) == 0)
{
uint8_t v___x_613_; 
v___x_613_ = 0;
v___y_608_ = v___x_613_;
goto v___jp_607_;
}
else
{
uint8_t v___x_614_; 
v___x_614_ = 1;
v___y_608_ = v___x_614_;
goto v___jp_607_;
}
v___jp_607_:
{
lean_object* v_toPure_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_toPure_609_ = lean_ctor_get(v_toApplicative_605_, 1);
lean_inc(v_toPure_609_);
lean_dec_ref(v_toApplicative_605_);
v___x_610_ = lean_box(v___y_608_);
v___x_611_ = lean_apply_2(v_toPure_609_, lean_box(0), v___x_610_);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(v_toApplicative_615_, v_a_616_);
lean_dec_ref(v_a_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_toApplicative_621_; lean_object* v_toBind_622_; lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_toApplicative_621_ = lean_ctor_get(v_inst_618_, 0);
lean_inc_ref(v_toApplicative_621_);
v_toBind_622_ = lean_ctor_get(v_inst_618_, 1);
lean_inc(v_toBind_622_);
lean_dec_ref(v_inst_618_);
v___f_623_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_623_, 0, v_toApplicative_621_);
lean_inc(v_a_620_);
v___x_624_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_624_, 0, lean_box(0));
lean_closure_set(v___x_624_, 1, lean_box(0));
lean_closure_set(v___x_624_, 2, v_a_620_);
v___x_625_ = lean_apply_2(v_inst_619_, lean_box(0), v___x_624_);
v___x_626_ = lean_apply_4(v_toBind_622_, lean_box(0), lean_box(0), v___x_625_, v___f_623_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_627_, v_inst_628_, v_a_629_);
lean_dec(v_a_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(lean_object* v_m_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_632_, v_inst_633_, v_a_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(lean_object* v_m_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(v_m_636_, v_inst_637_, v_inst_638_, v_a_639_);
lean_dec(v_a_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(lean_object* v_val_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v_val_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(uint8_t v___x_643_, lean_object* v_knownSize_644_, lean_object* v_closeError_645_, uint8_t v_closed_646_, lean_object* v___y_647_, lean_object* v_inst_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_650_ = lean_box(0);
v___x_651_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_651_, 0, v_a_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
lean_ctor_set(v___x_651_, 2, v___x_650_);
lean_ctor_set(v___x_651_, 3, v_knownSize_644_);
lean_ctor_set(v___x_651_, 4, v___x_650_);
lean_ctor_set(v___x_651_, 5, v_closeError_645_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*6, v___x_643_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*6 + 1, v_closed_646_);
lean_inc(v___y_647_);
v___x_652_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_652_, 0, lean_box(0));
lean_closure_set(v___x_652_, 1, lean_box(0));
lean_closure_set(v___x_652_, 2, v___y_647_);
lean_closure_set(v___x_652_, 3, v___x_651_);
v___x_653_ = lean_apply_2(v_inst_648_, lean_box(0), v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object* v___x_654_, lean_object* v_knownSize_655_, lean_object* v_closeError_656_, lean_object* v_closed_657_, lean_object* v___y_658_, lean_object* v_inst_659_, lean_object* v_a_660_){
_start:
{
uint8_t v___x_1161__boxed_661_; uint8_t v_closed_boxed_662_; lean_object* v_res_663_; 
v___x_1161__boxed_661_ = lean_unbox(v___x_654_);
v_closed_boxed_662_ = lean_unbox(v_closed_657_);
v_res_663_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(v___x_1161__boxed_661_, v_knownSize_655_, v_closeError_656_, v_closed_boxed_662_, v___y_658_, v_inst_659_, v_a_660_);
lean_dec(v___y_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object* v_val_664_, lean_object* v_toPure_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_val_664_);
lean_ctor_set(v___x_667_, 1, v_a_666_);
v___x_668_ = lean_apply_2(v_toPure_665_, lean_box(0), v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(uint8_t v___x_670_, lean_object* v_knownSize_671_, lean_object* v_closeError_672_, uint8_t v_closed_673_, lean_object* v_inst_674_, lean_object* v_leftover_675_, lean_object* v_toApplicative_676_, lean_object* v_toBind_677_, lean_object* v_inst_678_, lean_object* v___f_679_, lean_object* v_____r_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___f_684_; 
v___x_682_ = lean_box(v___x_670_);
v___x_683_ = lean_box(v_closed_673_);
lean_inc(v___y_681_);
v___f_684_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_684_, 0, v___x_682_);
lean_closure_set(v___f_684_, 1, v_knownSize_671_);
lean_closure_set(v___f_684_, 2, v_closeError_672_);
lean_closure_set(v___f_684_, 3, v___x_683_);
lean_closure_set(v___f_684_, 4, v___y_681_);
lean_closure_set(v___f_684_, 5, v_inst_674_);
if (lean_obj_tag(v_leftover_675_) == 0)
{
lean_object* v_toPure_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec_ref(v___f_679_);
lean_dec(v_inst_678_);
v_toPure_685_ = lean_ctor_get(v_toApplicative_676_, 1);
lean_inc(v_toPure_685_);
lean_dec_ref(v_toApplicative_676_);
v___x_686_ = lean_box(0);
v___x_687_ = lean_apply_2(v_toPure_685_, lean_box(0), v___x_686_);
v___x_688_ = lean_apply_4(v_toBind_677_, lean_box(0), lean_box(0), v___x_687_, v___f_684_);
return v___x_688_;
}
else
{
lean_object* v_toFunctor_689_; lean_object* v_val_690_; lean_object* v_toPure_691_; lean_object* v_map_692_; lean_object* v___f_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_toFunctor_689_ = lean_ctor_get(v_toApplicative_676_, 0);
lean_inc_ref(v_toFunctor_689_);
v_val_690_ = lean_ctor_get(v_leftover_675_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v_leftover_675_, 1);
v_toPure_691_ = lean_ctor_get(v_toApplicative_676_, 1);
lean_inc(v_toPure_691_);
lean_dec_ref(v_toApplicative_676_);
v_map_692_ = lean_ctor_get(v_toFunctor_689_, 0);
lean_inc(v_map_692_);
lean_dec_ref(v_toFunctor_689_);
v___f_693_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_693_, 0, v_val_690_);
lean_closure_set(v___f_693_, 1, v_toPure_691_);
v___x_694_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___closed__0));
v___x_695_ = lean_apply_2(v_inst_678_, lean_box(0), v___x_694_);
lean_inc(v_toBind_677_);
v___x_696_ = lean_apply_4(v_toBind_677_, lean_box(0), lean_box(0), v___x_695_, v___f_693_);
v___x_697_ = lean_apply_4(v_map_692_, lean_box(0), lean_box(0), v___f_679_, v___x_696_);
v___x_698_ = lean_apply_4(v_toBind_677_, lean_box(0), lean_box(0), v___x_697_, v___f_684_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object* v___x_699_, lean_object* v_knownSize_700_, lean_object* v_closeError_701_, lean_object* v_closed_702_, lean_object* v_inst_703_, lean_object* v_leftover_704_, lean_object* v_toApplicative_705_, lean_object* v_toBind_706_, lean_object* v_inst_707_, lean_object* v___f_708_, lean_object* v_____r_709_, lean_object* v___y_710_){
_start:
{
uint8_t v___x_1186__boxed_711_; uint8_t v_closed_boxed_712_; lean_object* v_res_713_; 
v___x_1186__boxed_711_ = lean_unbox(v___x_699_);
v_closed_boxed_712_ = lean_unbox(v_closed_702_);
v_res_713_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(v___x_1186__boxed_711_, v_knownSize_700_, v_closeError_701_, v_closed_boxed_712_, v_inst_703_, v_leftover_704_, v_toApplicative_705_, v_toBind_706_, v_inst_707_, v___f_708_, v_____r_709_, v___y_710_);
lean_dec(v___y_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object* v___f_714_, lean_object* v___y_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___x_717_; 
lean_inc(v___y_715_);
v___x_717_ = lean_apply_2(v___f_714_, v_a_716_, v___y_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object* v___f_718_, lean_object* v___y_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v___f_718_, v___y_719_, v_a_720_);
lean_dec(v___y_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object* v_pendingProducer_722_, lean_object* v_toApplicative_723_, lean_object* v___f_724_, uint8_t v_closed_725_, lean_object* v_inst_726_, lean_object* v_toBind_727_, lean_object* v_____r_728_, lean_object* v___y_729_){
_start:
{
if (lean_obj_tag(v_pendingProducer_722_) == 1)
{
lean_object* v_val_730_; lean_object* v_toFunctor_731_; lean_object* v_done_732_; lean_object* v_mapConst_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_val_730_ = lean_ctor_get(v_pendingProducer_722_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v_pendingProducer_722_, 1);
v_toFunctor_731_ = lean_ctor_get(v_toApplicative_723_, 0);
lean_inc_ref(v_toFunctor_731_);
lean_dec_ref(v_toApplicative_723_);
v_done_732_ = lean_ctor_get(v_val_730_, 1);
lean_inc(v_done_732_);
lean_dec(v_val_730_);
v_mapConst_733_ = lean_ctor_get(v_toFunctor_731_, 1);
lean_inc(v_mapConst_733_);
lean_dec_ref(v_toFunctor_731_);
lean_inc(v___y_729_);
v___f_734_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_734_, 0, v___f_724_);
lean_closure_set(v___f_734_, 1, v___y_729_);
v___x_735_ = lean_box(v_closed_725_);
v___x_736_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_736_, 0, lean_box(0));
lean_closure_set(v___x_736_, 1, v___x_735_);
lean_closure_set(v___x_736_, 2, v_done_732_);
v___x_737_ = lean_apply_2(v_inst_726_, lean_box(0), v___x_736_);
v___x_738_ = lean_box(0);
v___x_739_ = lean_apply_4(v_mapConst_733_, lean_box(0), lean_box(0), v___x_738_, v___x_737_);
v___x_740_ = lean_apply_4(v_toBind_727_, lean_box(0), lean_box(0), v___x_739_, v___f_734_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v_toBind_727_);
lean_dec(v_inst_726_);
lean_dec_ref(v_toApplicative_723_);
lean_dec(v_pendingProducer_722_);
v___x_741_ = lean_box(0);
lean_inc(v___y_729_);
v___x_742_ = lean_apply_2(v___f_724_, v___x_741_, v___y_729_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object* v_pendingProducer_743_, lean_object* v_toApplicative_744_, lean_object* v___f_745_, lean_object* v_closed_746_, lean_object* v_inst_747_, lean_object* v_toBind_748_, lean_object* v_____r_749_, lean_object* v___y_750_){
_start:
{
uint8_t v_closed_boxed_751_; lean_object* v_res_752_; 
v_closed_boxed_751_ = lean_unbox(v_closed_746_);
v_res_752_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(v_pendingProducer_743_, v_toApplicative_744_, v___f_745_, v_closed_boxed_751_, v_inst_747_, v_toBind_748_, v_____r_749_, v___y_750_);
lean_dec(v___y_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7(uint8_t v___x_753_, lean_object* v_closeError_754_, uint8_t v_closed_755_, lean_object* v_inst_756_, lean_object* v_toApplicative_757_, lean_object* v_toBind_758_, lean_object* v_inst_759_, lean_object* v___f_760_, lean_object* v_pendingProducer_761_, lean_object* v_interestWaiter_762_, lean_object* v_____r_763_, lean_object* v_leftover_764_, lean_object* v_knownSize_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___f_771_; 
v___x_767_ = lean_box(v___x_753_);
v___x_768_ = lean_box(v_closed_755_);
lean_inc_n(v_inst_759_, 2);
lean_inc_n(v_toBind_758_, 2);
lean_inc_ref_n(v_toApplicative_757_, 2);
v___f_769_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed), 12, 10);
lean_closure_set(v___f_769_, 0, v___x_767_);
lean_closure_set(v___f_769_, 1, v_knownSize_765_);
lean_closure_set(v___f_769_, 2, v_closeError_754_);
lean_closure_set(v___f_769_, 3, v___x_768_);
lean_closure_set(v___f_769_, 4, v_inst_756_);
lean_closure_set(v___f_769_, 5, v_leftover_764_);
lean_closure_set(v___f_769_, 6, v_toApplicative_757_);
lean_closure_set(v___f_769_, 7, v_toBind_758_);
lean_closure_set(v___f_769_, 8, v_inst_759_);
lean_closure_set(v___f_769_, 9, v___f_760_);
v___x_770_ = lean_box(v_closed_755_);
lean_inc_ref(v___f_769_);
lean_inc(v_pendingProducer_761_);
v___f_771_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_771_, 0, v_pendingProducer_761_);
lean_closure_set(v___f_771_, 1, v_toApplicative_757_);
lean_closure_set(v___f_771_, 2, v___f_769_);
lean_closure_set(v___f_771_, 3, v___x_770_);
lean_closure_set(v___f_771_, 4, v_inst_759_);
lean_closure_set(v___f_771_, 5, v_toBind_758_);
if (lean_obj_tag(v_interestWaiter_762_) == 1)
{
lean_object* v_toFunctor_772_; lean_object* v_val_773_; lean_object* v_mapConst_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v___f_769_);
lean_dec(v_pendingProducer_761_);
v_toFunctor_772_ = lean_ctor_get(v_toApplicative_757_, 0);
lean_inc_ref(v_toFunctor_772_);
lean_dec_ref(v_toApplicative_757_);
v_val_773_ = lean_ctor_get(v_interestWaiter_762_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v_interestWaiter_762_, 1);
v_mapConst_774_ = lean_ctor_get(v_toFunctor_772_, 1);
lean_inc(v_mapConst_774_);
lean_dec_ref(v_toFunctor_772_);
lean_inc(v___y_766_);
v___f_775_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_775_, 0, v___f_771_);
lean_closure_set(v___f_775_, 1, v___y_766_);
v___x_776_ = lean_box(v_closed_755_);
v___x_777_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_777_, 0, v_val_773_);
lean_closure_set(v___x_777_, 1, v___x_776_);
v___x_778_ = lean_apply_2(v_inst_759_, lean_box(0), v___x_777_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_apply_4(v_mapConst_774_, lean_box(0), lean_box(0), v___x_779_, v___x_778_);
v___x_781_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_780_, v___f_775_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref(v___f_771_);
lean_dec(v_interestWaiter_762_);
v___x_782_ = lean_box(0);
v___x_783_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(v_pendingProducer_761_, v_toApplicative_757_, v___f_769_, v_closed_755_, v_inst_759_, v_toBind_758_, v___x_782_, v___y_766_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7___boxed(lean_object* v___x_784_, lean_object* v_closeError_785_, lean_object* v_closed_786_, lean_object* v_inst_787_, lean_object* v_toApplicative_788_, lean_object* v_toBind_789_, lean_object* v_inst_790_, lean_object* v___f_791_, lean_object* v_pendingProducer_792_, lean_object* v_interestWaiter_793_, lean_object* v_____r_794_, lean_object* v_leftover_795_, lean_object* v_knownSize_796_, lean_object* v___y_797_){
_start:
{
uint8_t v___x_1271__boxed_798_; uint8_t v_closed_boxed_799_; lean_object* v_res_800_; 
v___x_1271__boxed_798_ = lean_unbox(v___x_784_);
v_closed_boxed_799_ = lean_unbox(v_closed_786_);
v_res_800_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7(v___x_1271__boxed_798_, v_closeError_785_, v_closed_boxed_799_, v_inst_787_, v_toApplicative_788_, v_toBind_789_, v_inst_790_, v___f_791_, v_pendingProducer_792_, v_interestWaiter_793_, v_____r_794_, v_leftover_795_, v_knownSize_796_, v___y_797_);
lean_dec(v___y_797_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6(lean_object* v___f_801_, lean_object* v___y_802_, lean_object* v_knownSize_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_806_; 
lean_inc(v_a_804_);
v___x_806_ = lean_apply_4(v___f_801_, v_a_805_, v___y_802_, v_knownSize_803_, v_a_804_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6___boxed(lean_object* v___f_807_, lean_object* v___y_808_, lean_object* v_knownSize_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6(v___f_807_, v___y_808_, v_knownSize_809_, v_a_810_, v_a_811_);
lean_dec(v_a_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8(lean_object* v___f_813_, lean_object* v___y_814_, lean_object* v_knownSize_815_, lean_object* v_a_816_, lean_object* v_val_817_, uint8_t v_a_818_){
_start:
{
if (v_a_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_box(0);
lean_inc(v_a_816_);
v___x_820_ = lean_apply_4(v___f_813_, v___x_819_, v___y_814_, v_knownSize_815_, v_a_816_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v___y_814_);
v___x_821_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_815_, v_val_817_);
v___x_822_ = lean_box(0);
v___x_823_ = lean_box(0);
lean_inc(v_a_816_);
v___x_824_ = lean_apply_4(v___f_813_, v___x_823_, v___x_822_, v___x_821_, v_a_816_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8___boxed(lean_object* v___f_825_, lean_object* v___y_826_, lean_object* v_knownSize_827_, lean_object* v_a_828_, lean_object* v_val_829_, lean_object* v_a_830_){
_start:
{
uint8_t v_a_boxed_831_; lean_object* v_res_832_; 
v_a_boxed_831_ = lean_unbox(v_a_830_);
v_res_832_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8(v___f_825_, v___y_826_, v_knownSize_827_, v_a_828_, v_val_829_, v_a_boxed_831_);
lean_dec_ref(v_val_829_);
lean_dec(v_a_828_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9(lean_object* v_toApplicative_833_, lean_object* v_inst_834_, lean_object* v_toBind_835_, lean_object* v_inst_836_, lean_object* v___f_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; uint8_t v_closed_851_; 
v_closed_851_ = lean_ctor_get_uint8(v_a_839_, sizeof(void*)*6);
if (v_closed_851_ == 0)
{
lean_object* v_pendingProducer_852_; lean_object* v_pendingConsumer_853_; lean_object* v_interestWaiter_854_; lean_object* v_knownSize_855_; lean_object* v_pendingIncomplete_856_; lean_object* v_closeError_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___f_861_; lean_object* v___y_863_; 
v_pendingProducer_852_ = lean_ctor_get(v_a_839_, 0);
lean_inc_n(v_pendingProducer_852_, 2);
v_pendingConsumer_853_ = lean_ctor_get(v_a_839_, 1);
lean_inc(v_pendingConsumer_853_);
v_interestWaiter_854_ = lean_ctor_get(v_a_839_, 2);
lean_inc_n(v_interestWaiter_854_, 2);
v_knownSize_855_ = lean_ctor_get(v_a_839_, 3);
lean_inc(v_knownSize_855_);
v_pendingIncomplete_856_ = lean_ctor_get(v_a_839_, 4);
lean_inc(v_pendingIncomplete_856_);
v_closeError_857_ = lean_ctor_get(v_a_839_, 5);
lean_inc_n(v_closeError_857_, 2);
lean_dec_ref(v_a_839_);
v___x_858_ = 1;
v___x_859_ = lean_box(v___x_858_);
v___x_860_ = lean_box(v_closed_851_);
lean_inc_ref(v___f_837_);
lean_inc(v_inst_834_);
lean_inc(v_toBind_835_);
lean_inc_ref(v_toApplicative_833_);
lean_inc(v_inst_836_);
v___f_861_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7___boxed), 14, 10);
lean_closure_set(v___f_861_, 0, v___x_859_);
lean_closure_set(v___f_861_, 1, v_closeError_857_);
lean_closure_set(v___f_861_, 2, v___x_860_);
lean_closure_set(v___f_861_, 3, v_inst_836_);
lean_closure_set(v___f_861_, 4, v_toApplicative_833_);
lean_closure_set(v___f_861_, 5, v_toBind_835_);
lean_closure_set(v___f_861_, 6, v_inst_834_);
lean_closure_set(v___f_861_, 7, v___f_837_);
lean_closure_set(v___f_861_, 8, v_pendingProducer_852_);
lean_closure_set(v___f_861_, 9, v_interestWaiter_854_);
if (lean_obj_tag(v_pendingProducer_852_) == 0)
{
if (lean_obj_tag(v_pendingIncomplete_856_) == 0)
{
lean_object* v___x_896_; 
v___x_896_ = lean_box(0);
v___y_863_ = v___x_896_;
goto v___jp_862_;
}
else
{
lean_object* v_val_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_910_; 
v_val_897_ = lean_ctor_get(v_pendingIncomplete_856_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_pendingIncomplete_856_);
if (v_isSharedCheck_910_ == 0)
{
v___x_899_ = v_pendingIncomplete_856_;
v_isShared_900_ = v_isSharedCheck_910_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_val_897_);
lean_dec(v_pendingIncomplete_856_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_910_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v_data_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_901_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(v_val_897_);
v_data_902_ = lean_ctor_get(v___x_901_, 0);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_byte_array_size(v_data_902_);
v___x_905_ = lean_nat_dec_lt(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec_ref(v___x_901_);
lean_del_object(v___x_899_);
v___x_906_ = lean_box(0);
v___y_863_ = v___x_906_;
goto v___jp_862_;
}
else
{
lean_object* v___x_908_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_908_ = v___x_899_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_901_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
v___y_863_ = v___x_908_;
goto v___jp_862_;
}
}
}
}
}
else
{
lean_object* v___x_911_; 
lean_dec(v_pendingIncomplete_856_);
v___x_911_ = lean_box(0);
v___y_863_ = v___x_911_;
goto v___jp_862_;
}
v___jp_862_:
{
if (lean_obj_tag(v_pendingConsumer_853_) == 1)
{
lean_dec(v_interestWaiter_854_);
lean_dec(v_pendingProducer_852_);
lean_dec_ref(v___f_837_);
lean_dec(v_inst_836_);
if (lean_obj_tag(v___y_863_) == 0)
{
lean_object* v_val_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_880_; 
v_val_864_ = lean_ctor_get(v_pendingConsumer_853_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_pendingConsumer_853_);
if (v_isSharedCheck_880_ == 0)
{
v___x_866_ = v_pendingConsumer_853_;
v_isShared_867_ = v_isSharedCheck_880_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_val_864_);
lean_dec(v_pendingConsumer_853_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_880_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___f_868_; 
lean_inc(v_a_838_);
v___f_868_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_868_, 0, v___f_861_);
lean_closure_set(v___f_868_, 1, v___y_863_);
lean_closure_set(v___f_868_, 2, v_knownSize_855_);
lean_closure_set(v___f_868_, 3, v_a_838_);
if (lean_obj_tag(v_closeError_857_) == 0)
{
lean_object* v___x_870_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___y_863_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___y_863_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
v___y_841_ = v___f_868_;
v___y_842_ = v_val_864_;
v___y_843_ = v___x_870_;
goto v___jp_840_;
}
}
else
{
lean_object* v_val_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_del_object(v___x_866_);
v_val_872_ = lean_ctor_get(v_closeError_857_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v_closeError_857_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v_closeError_857_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_val_872_);
lean_dec(v_closeError_857_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 0);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_val_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
v___y_841_ = v___f_868_;
v___y_842_ = v_val_864_;
v___y_843_ = v___x_877_;
goto v___jp_840_;
}
}
}
}
}
else
{
lean_object* v_val_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_closeError_857_);
lean_dec_ref(v_toApplicative_833_);
v_val_881_ = lean_ctor_get(v_pendingConsumer_853_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_pendingConsumer_853_);
if (v_isSharedCheck_893_ == 0)
{
v___x_883_ = v_pendingConsumer_853_;
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_val_881_);
lean_dec(v_pendingConsumer_853_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_val_885_; lean_object* v___f_886_; lean_object* v___x_888_; 
v_val_885_ = lean_ctor_get(v___y_863_, 0);
lean_inc(v_val_885_);
lean_inc(v_a_838_);
lean_inc_ref(v___y_863_);
v___f_886_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8___boxed), 6, 5);
lean_closure_set(v___f_886_, 0, v___f_861_);
lean_closure_set(v___f_886_, 1, v___y_863_);
lean_closure_set(v___f_886_, 2, v_knownSize_855_);
lean_closure_set(v___f_886_, 3, v_a_838_);
lean_closure_set(v___f_886_, 4, v_val_885_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___y_863_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___y_863_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed), 3, 2);
lean_closure_set(v___x_889_, 0, v_val_881_);
lean_closure_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_apply_2(v_inst_834_, lean_box(0), v___x_889_);
v___x_891_ = lean_apply_4(v_toBind_835_, lean_box(0), lean_box(0), v___x_890_, v___f_886_);
return v___x_891_;
}
}
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref(v___f_861_);
lean_dec(v_pendingConsumer_853_);
v___x_894_ = lean_box(0);
v___x_895_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7(v___x_858_, v_closeError_857_, v_closed_851_, v_inst_836_, v_toApplicative_833_, v_toBind_835_, v_inst_834_, v___f_837_, v_pendingProducer_852_, v_interestWaiter_854_, v___x_894_, v___y_863_, v_knownSize_855_, v_a_838_);
return v___x_895_;
}
}
}
else
{
lean_object* v_toPure_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref(v_a_839_);
lean_dec_ref(v___f_837_);
lean_dec(v_inst_836_);
lean_dec(v_toBind_835_);
lean_dec(v_inst_834_);
v_toPure_912_ = lean_ctor_get(v_toApplicative_833_, 1);
lean_inc(v_toPure_912_);
lean_dec_ref(v_toApplicative_833_);
v___x_913_ = lean_box(0);
v___x_914_ = lean_apply_2(v_toPure_912_, lean_box(0), v___x_913_);
return v___x_914_;
}
v___jp_840_:
{
lean_object* v_toFunctor_844_; lean_object* v_mapConst_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_toFunctor_844_ = lean_ctor_get(v_toApplicative_833_, 0);
lean_inc_ref(v_toFunctor_844_);
lean_dec_ref(v_toApplicative_833_);
v_mapConst_845_ = lean_ctor_get(v_toFunctor_844_, 1);
lean_inc(v_mapConst_845_);
lean_dec_ref(v_toFunctor_844_);
v___x_846_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed), 3, 2);
lean_closure_set(v___x_846_, 0, v___y_842_);
lean_closure_set(v___x_846_, 1, v___y_843_);
v___x_847_ = lean_apply_2(v_inst_834_, lean_box(0), v___x_846_);
v___x_848_ = lean_box(0);
v___x_849_ = lean_apply_4(v_mapConst_845_, lean_box(0), lean_box(0), v___x_848_, v___x_847_);
v___x_850_ = lean_apply_4(v_toBind_835_, lean_box(0), lean_box(0), v___x_849_, v___y_841_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9___boxed(lean_object* v_toApplicative_915_, lean_object* v_inst_916_, lean_object* v_toBind_917_, lean_object* v_inst_918_, lean_object* v___f_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9(v_toApplicative_915_, v_inst_916_, v_toBind_917_, v_inst_918_, v___f_919_, v_a_920_, v_a_921_);
lean_dec(v_a_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_toApplicative_928_; lean_object* v_toBind_929_; lean_object* v___f_930_; lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_toApplicative_928_ = lean_ctor_get(v_inst_924_, 0);
lean_inc_ref(v_toApplicative_928_);
v_toBind_929_ = lean_ctor_get(v_inst_924_, 1);
lean_inc_n(v_toBind_929_, 2);
lean_dec_ref(v_inst_924_);
v___f_930_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___closed__0));
lean_inc_n(v_a_927_, 2);
lean_inc(v_inst_925_);
v___f_931_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_931_, 0, v_toApplicative_928_);
lean_closure_set(v___f_931_, 1, v_inst_926_);
lean_closure_set(v___f_931_, 2, v_toBind_929_);
lean_closure_set(v___f_931_, 3, v_inst_925_);
lean_closure_set(v___f_931_, 4, v___f_930_);
lean_closure_set(v___f_931_, 5, v_a_927_);
v___x_932_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_932_, 0, lean_box(0));
lean_closure_set(v___x_932_, 1, lean_box(0));
lean_closure_set(v___x_932_, 2, v_a_927_);
v___x_933_ = lean_apply_2(v_inst_925_, lean_box(0), v___x_932_);
v___x_934_ = lean_apply_4(v_toBind_929_, lean_box(0), lean_box(0), v___x_933_, v___f_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_935_, v_inst_936_, v_inst_937_, v_a_938_);
lean_dec(v_a_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object* v_m_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_941_, v_inst_942_, v_inst_943_, v_a_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object* v_m_946_, lean_object* v_inst_947_, lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(v_m_946_, v_inst_947_, v_inst_948_, v_inst_949_, v_a_950_);
lean_dec(v_a_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_952_, lean_object* v_chunk_953_, lean_object* v_____r_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_toPure_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_toPure_956_ = lean_ctor_get(v_toApplicative_952_, 1);
lean_inc(v_toPure_956_);
lean_dec_ref(v_toApplicative_952_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v_chunk_953_);
v___x_958_ = lean_apply_2(v_toPure_956_, lean_box(0), v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_959_, lean_object* v_chunk_960_, lean_object* v_____r_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(v_toApplicative_959_, v_chunk_960_, v_____r_961_, v___y_962_);
lean_dec(v___y_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object* v___f_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v___x_967_; 
lean_inc(v_a_965_);
v___x_967_ = lean_apply_2(v___f_964_, v_a_966_, v_a_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1___boxed(lean_object* v___f_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(v___f_968_, v_a_969_, v_a_970_);
lean_dec(v_a_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(uint8_t v_closeAfterProducer_972_, lean_object* v___f_973_, lean_object* v_a_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_toBind_978_, lean_object* v___f_979_, lean_object* v_a_980_){
_start:
{
if (v_closeAfterProducer_972_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec(v___f_979_);
lean_dec(v_toBind_978_);
lean_dec(v_inst_977_);
lean_dec(v_inst_976_);
lean_dec_ref(v_inst_975_);
v___x_981_ = lean_box(0);
lean_inc(v_a_974_);
v___x_982_ = lean_apply_2(v___f_973_, v___x_981_, v_a_974_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec(v___f_973_);
v___x_983_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_975_, v_inst_976_, v_inst_977_, v_a_974_);
v___x_984_ = lean_apply_4(v_toBind_978_, lean_box(0), lean_box(0), v___x_983_, v___f_979_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_closeAfterProducer_985_, lean_object* v___f_986_, lean_object* v_a_987_, lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_inst_990_, lean_object* v_toBind_991_, lean_object* v___f_992_, lean_object* v_a_993_){
_start:
{
uint8_t v_closeAfterProducer_boxed_994_; lean_object* v_res_995_; 
v_closeAfterProducer_boxed_994_ = lean_unbox(v_closeAfterProducer_985_);
v_res_995_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(v_closeAfterProducer_boxed_994_, v___f_986_, v_a_987_, v_inst_988_, v_inst_989_, v_inst_990_, v_toBind_991_, v___f_992_, v_a_993_);
lean_dec(v_a_987_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_996_, lean_object* v_done_997_, lean_object* v_inst_998_, lean_object* v_toBind_999_, lean_object* v___f_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_toFunctor_1002_; lean_object* v_mapConst_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_toFunctor_1002_ = lean_ctor_get(v_toApplicative_996_, 0);
lean_inc_ref(v_toFunctor_1002_);
lean_dec_ref(v_toApplicative_996_);
v_mapConst_1003_ = lean_ctor_get(v_toFunctor_1002_, 1);
lean_inc(v_mapConst_1003_);
lean_dec_ref(v_toFunctor_1002_);
v___x_1004_ = 1;
v___x_1005_ = lean_box(v___x_1004_);
v___x_1006_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1006_, 0, lean_box(0));
lean_closure_set(v___x_1006_, 1, v___x_1005_);
lean_closure_set(v___x_1006_, 2, v_done_997_);
v___x_1007_ = lean_apply_2(v_inst_998_, lean_box(0), v___x_1006_);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_apply_4(v_mapConst_1003_, lean_box(0), lean_box(0), v___x_1008_, v___x_1007_);
v___x_1010_ = lean_apply_4(v_toBind_999_, lean_box(0), lean_box(0), v___x_1009_, v___f_1000_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_1011_, lean_object* v_a_1012_, lean_object* v_inst_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_toBind_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_pendingProducer_1018_; 
v_pendingProducer_1018_ = lean_ctor_get(v_a_1017_, 0);
if (lean_obj_tag(v_pendingProducer_1018_) == 1)
{
lean_object* v_val_1019_; lean_object* v_pendingConsumer_1020_; lean_object* v_interestWaiter_1021_; uint8_t v_closed_1022_; lean_object* v_knownSize_1023_; lean_object* v_pendingIncomplete_1024_; lean_object* v_closeError_1025_; uint8_t v_closeAfterProducer_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1046_; 
v_val_1019_ = lean_ctor_get(v_pendingProducer_1018_, 0);
lean_inc(v_val_1019_);
v_pendingConsumer_1020_ = lean_ctor_get(v_a_1017_, 1);
v_interestWaiter_1021_ = lean_ctor_get(v_a_1017_, 2);
v_closed_1022_ = lean_ctor_get_uint8(v_a_1017_, sizeof(void*)*6);
v_knownSize_1023_ = lean_ctor_get(v_a_1017_, 3);
v_pendingIncomplete_1024_ = lean_ctor_get(v_a_1017_, 4);
v_closeError_1025_ = lean_ctor_get(v_a_1017_, 5);
v_closeAfterProducer_1026_ = lean_ctor_get_uint8(v_a_1017_, sizeof(void*)*6 + 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_1017_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_a_1017_, 0);
lean_dec(v_unused_1047_);
v___x_1028_ = v_a_1017_;
v_isShared_1029_ = v_isSharedCheck_1046_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_closeError_1025_);
lean_inc(v_pendingIncomplete_1024_);
lean_inc(v_knownSize_1023_);
lean_inc(v_interestWaiter_1021_);
lean_inc(v_pendingConsumer_1020_);
lean_dec(v_a_1017_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1046_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_chunk_1030_; lean_object* v_done_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; lean_object* v___x_1041_; 
v_chunk_1030_ = lean_ctor_get(v_val_1019_, 0);
lean_inc_ref_n(v_chunk_1030_, 2);
v_done_1031_ = lean_ctor_get(v_val_1019_, 1);
lean_inc(v_done_1031_);
lean_dec(v_val_1019_);
v___x_1032_ = lean_box(0);
lean_inc_ref(v_toApplicative_1011_);
v___f_1033_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1033_, 0, v_toApplicative_1011_);
lean_closure_set(v___f_1033_, 1, v_chunk_1030_);
lean_inc_n(v_a_1012_, 2);
lean_inc_ref(v___f_1033_);
v___f_1034_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1034_, 0, v___f_1033_);
lean_closure_set(v___f_1034_, 1, v_a_1012_);
v___x_1035_ = lean_box(v_closeAfterProducer_1026_);
lean_inc_n(v_toBind_1016_, 2);
lean_inc(v_inst_1015_);
lean_inc(v_inst_1014_);
v___f_1036_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_1036_, 0, v___x_1035_);
lean_closure_set(v___f_1036_, 1, v___f_1033_);
lean_closure_set(v___f_1036_, 2, v_a_1012_);
lean_closure_set(v___f_1036_, 3, v_inst_1013_);
lean_closure_set(v___f_1036_, 4, v_inst_1014_);
lean_closure_set(v___f_1036_, 5, v_inst_1015_);
lean_closure_set(v___f_1036_, 6, v_toBind_1016_);
lean_closure_set(v___f_1036_, 7, v___f_1034_);
v___f_1037_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1037_, 0, v_toApplicative_1011_);
lean_closure_set(v___f_1037_, 1, v_done_1031_);
lean_closure_set(v___f_1037_, 2, v_inst_1015_);
lean_closure_set(v___f_1037_, 3, v_toBind_1016_);
lean_closure_set(v___f_1037_, 4, v___f_1036_);
v___x_1038_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1023_, v_chunk_1030_);
lean_dec_ref(v_chunk_1030_);
v___x_1039_ = 0;
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 3, v___x_1038_);
lean_ctor_set(v___x_1028_, 0, v___x_1032_);
v___x_1041_ = v___x_1028_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_pendingConsumer_1020_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_interestWaiter_1021_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_pendingIncomplete_1024_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v_closeError_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*6, v_closed_1022_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*6 + 1, v___x_1039_);
lean_inc(v_a_1012_);
v___x_1042_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1042_, 0, lean_box(0));
lean_closure_set(v___x_1042_, 1, lean_box(0));
lean_closure_set(v___x_1042_, 2, v_a_1012_);
lean_closure_set(v___x_1042_, 3, v___x_1041_);
v___x_1043_ = lean_apply_2(v_inst_1014_, lean_box(0), v___x_1042_);
v___x_1044_ = lean_apply_4(v_toBind_1016_, lean_box(0), lean_box(0), v___x_1043_, v___f_1037_);
return v___x_1044_;
}
}
}
else
{
lean_object* v_toPure_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec_ref(v_a_1017_);
lean_dec(v_toBind_1016_);
lean_dec(v_inst_1015_);
lean_dec(v_inst_1014_);
lean_dec_ref(v_inst_1013_);
v_toPure_1048_ = lean_ctor_get(v_toApplicative_1011_, 1);
lean_inc(v_toPure_1048_);
lean_dec_ref(v_toApplicative_1011_);
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_apply_2(v_toPure_1048_, lean_box(0), v___x_1049_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_1051_, lean_object* v_a_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_toBind_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4(v_toApplicative_1051_, v_a_1052_, v_inst_1053_, v_inst_1054_, v_inst_1055_, v_toBind_1056_, v_a_1057_);
lean_dec(v_a_1052_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_toApplicative_1063_; lean_object* v_toBind_1064_; lean_object* v___f_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_toApplicative_1063_ = lean_ctor_get(v_inst_1059_, 0);
lean_inc_ref(v_toApplicative_1063_);
v_toBind_1064_ = lean_ctor_get(v_inst_1059_, 1);
lean_inc_n(v_toBind_1064_, 2);
lean_inc(v_inst_1060_);
lean_inc_n(v_a_1062_, 2);
v___f_1065_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_1065_, 0, v_toApplicative_1063_);
lean_closure_set(v___f_1065_, 1, v_a_1062_);
lean_closure_set(v___f_1065_, 2, v_inst_1059_);
lean_closure_set(v___f_1065_, 3, v_inst_1060_);
lean_closure_set(v___f_1065_, 4, v_inst_1061_);
lean_closure_set(v___f_1065_, 5, v_toBind_1064_);
v___x_1066_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1066_, 0, lean_box(0));
lean_closure_set(v___x_1066_, 1, lean_box(0));
lean_closure_set(v___x_1066_, 2, v_a_1062_);
v___x_1067_ = lean_apply_2(v_inst_1060_, lean_box(0), v___x_1066_);
v___x_1068_ = lean_apply_4(v_toBind_1064_, lean_box(0), lean_box(0), v___x_1067_, v___f_1065_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_1069_, v_inst_1070_, v_inst_1071_, v_a_1072_);
lean_dec(v_a_1072_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(lean_object* v_m_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_1075_, v_inst_1076_, v_inst_1077_, v_a_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(lean_object* v_m_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(v_m_1080_, v_inst_1081_, v_inst_1082_, v_inst_1083_, v_a_1084_);
lean_dec(v_a_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0(lean_object* v_toApplicative_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_closeError_1090_; 
v_closeError_1090_ = lean_ctor_get(v_a_1089_, 5);
lean_inc(v_closeError_1090_);
lean_dec_ref(v_a_1089_);
if (lean_obj_tag(v_closeError_1090_) == 1)
{
lean_object* v_val_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1100_; 
v_val_1091_ = lean_ctor_get(v_closeError_1090_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_closeError_1090_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1093_ = v_closeError_1090_;
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_val_1091_);
lean_dec(v_closeError_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_toPure_1095_; lean_object* v___x_1097_; 
v_toPure_1095_ = lean_ctor_get(v_toApplicative_1088_, 1);
lean_inc(v_toPure_1095_);
lean_dec_ref(v_toApplicative_1088_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 0);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_val_1091_);
v___x_1097_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_apply_2(v_toPure_1095_, lean_box(0), v___x_1097_);
return v___x_1098_;
}
}
}
else
{
lean_object* v_toPure_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v_closeError_1090_);
v_toPure_1101_ = lean_ctor_get(v_toApplicative_1088_, 1);
lean_inc(v_toPure_1101_);
lean_dec_ref(v_toApplicative_1088_);
v___x_1102_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_1103_ = lean_apply_2(v_toPure_1101_, lean_box(0), v___x_1102_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(lean_object* v_toApplicative_1104_, lean_object* v_a_1105_, lean_object* v_inst_1106_, lean_object* v_toBind_1107_, lean_object* v___f_1108_, lean_object* v_a_1109_){
_start:
{
if (lean_obj_tag(v_a_1109_) == 1)
{
lean_object* v_toPure_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v___f_1108_);
lean_dec(v_toBind_1107_);
lean_dec(v_inst_1106_);
v_toPure_1110_ = lean_ctor_get(v_toApplicative_1104_, 1);
lean_inc(v_toPure_1110_);
lean_dec_ref(v_toApplicative_1104_);
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_a_1109_);
v___x_1112_ = lean_apply_2(v_toPure_1110_, lean_box(0), v___x_1111_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_a_1109_);
lean_dec_ref(v_toApplicative_1104_);
lean_inc(v_a_1105_);
v___x_1113_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1113_, 0, lean_box(0));
lean_closure_set(v___x_1113_, 1, lean_box(0));
lean_closure_set(v___x_1113_, 2, v_a_1105_);
v___x_1114_ = lean_apply_2(v_inst_1106_, lean_box(0), v___x_1113_);
v___x_1115_ = lean_apply_4(v_toBind_1107_, lean_box(0), lean_box(0), v___x_1114_, v___f_1108_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_1116_, lean_object* v_a_1117_, lean_object* v_inst_1118_, lean_object* v_toBind_1119_, lean_object* v___f_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(v_toApplicative_1116_, v_a_1117_, v_inst_1118_, v_toBind_1119_, v___f_1120_, v_a_1121_);
lean_dec(v_a_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_toApplicative_1127_; lean_object* v_toBind_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_toApplicative_1127_ = lean_ctor_get(v_inst_1123_, 0);
v_toBind_1128_ = lean_ctor_get(v_inst_1123_, 1);
lean_inc_n(v_toBind_1128_, 2);
lean_inc_ref_n(v_toApplicative_1127_, 2);
v___f_1129_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1129_, 0, v_toApplicative_1127_);
lean_inc(v_inst_1124_);
lean_inc(v_a_1126_);
v___f_1130_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1130_, 0, v_toApplicative_1127_);
lean_closure_set(v___f_1130_, 1, v_a_1126_);
lean_closure_set(v___f_1130_, 2, v_inst_1124_);
lean_closure_set(v___f_1130_, 3, v_toBind_1128_);
lean_closure_set(v___f_1130_, 4, v___f_1129_);
v___x_1131_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_1123_, v_inst_1124_, v_inst_1125_, v_a_1126_);
v___x_1132_ = lean_apply_4(v_toBind_1128_, lean_box(0), lean_box(0), v___x_1131_, v___f_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___boxed(lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_1133_, v_inst_1134_, v_inst_1135_, v_a_1136_);
lean_dec(v_a_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(lean_object* v_m_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_1139_, v_inst_1140_, v_inst_1141_, v_a_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___boxed(lean_object* v_m_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(v_m_1144_, v_inst_1145_, v_inst_1146_, v_inst_1147_, v_a_1148_);
lean_dec(v_a_1148_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object* v_pendingProducer_1154_, lean_object* v_pendingConsumer_1155_, uint8_t v_closed_1156_, lean_object* v_knownSize_1157_, lean_object* v_pendingIncomplete_1158_, lean_object* v_closeError_1159_, uint8_t v_closeAfterProducer_1160_, lean_object* v_interestWaiter_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1164_, 0, v_pendingProducer_1154_);
lean_ctor_set(v___x_1164_, 1, v_pendingConsumer_1155_);
lean_ctor_set(v___x_1164_, 2, v_interestWaiter_1161_);
lean_ctor_set(v___x_1164_, 3, v_knownSize_1157_);
lean_ctor_set(v___x_1164_, 4, v_pendingIncomplete_1158_);
lean_ctor_set(v___x_1164_, 5, v_closeError_1159_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*6, v_closed_1156_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*6 + 1, v_closeAfterProducer_1160_);
v___x_1165_ = lean_st_ref_swap(v___y_1162_, v___x_1164_);
lean_dec(v___x_1165_);
v___x_1166_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object* v_pendingProducer_1167_, lean_object* v_pendingConsumer_1168_, lean_object* v_closed_1169_, lean_object* v_knownSize_1170_, lean_object* v_pendingIncomplete_1171_, lean_object* v_closeError_1172_, lean_object* v_closeAfterProducer_1173_, lean_object* v_interestWaiter_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v_closed_boxed_1177_; uint8_t v_closeAfterProducer_boxed_1178_; lean_object* v_res_1179_; 
v_closed_boxed_1177_ = lean_unbox(v_closed_1169_);
v_closeAfterProducer_boxed_1178_ = lean_unbox(v_closeAfterProducer_1173_);
v_res_1179_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_1167_, v_pendingConsumer_1168_, v_closed_boxed_1177_, v_knownSize_1170_, v_pendingIncomplete_1171_, v_closeError_1172_, v_closeAfterProducer_boxed_1178_, v_interestWaiter_1174_, v___y_1175_);
lean_dec(v___y_1175_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object* v___f_1180_, lean_object* v___y_1181_, lean_object* v_x_1182_){
_start:
{
if (lean_obj_tag(v_x_1182_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v___f_1180_);
v_a_1184_ = lean_ctor_get(v_x_1182_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1186_ = v_x_1182_;
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v_x_1182_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
v_a_1193_ = lean_ctor_get(v_x_1182_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v_x_1182_, 1);
lean_inc(v___y_1181_);
v___x_1194_ = lean_apply_3(v___f_1180_, v_a_1193_, v___y_1181_, lean_box(0));
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object* v___f_1195_, lean_object* v___y_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_1195_, v___y_1196_, v_x_1197_);
lean_dec(v___y_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object* v_interestWaiter_1204_, lean_object* v___f_1205_, lean_object* v___f_1206_, lean_object* v_x_1207_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v___f_1206_);
lean_dec_ref(v___f_1205_);
lean_dec(v_interestWaiter_1204_);
v_a_1209_ = lean_ctor_get(v_x_1207_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1211_ = v_x_1207_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v_x_1207_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1234_; 
v_a_1218_ = lean_ctor_get(v_x_1207_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1220_ = v_x_1207_;
v_isShared_1221_ = v_isSharedCheck_1234_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v_x_1207_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1234_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_unbox(v_a_1218_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
lean_dec_ref(v___f_1206_);
v___x_1223_ = lean_unsigned_to_nat(0u);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v_interestWaiter_1204_);
v___x_1225_ = v___x_1220_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_interestWaiter_1204_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
v___x_1227_ = lean_unbox(v_a_1218_);
lean_dec(v_a_1218_);
v___x_1228_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1223_, v___x_1227_, v___x_1226_, v___f_1205_);
return v___x_1228_;
}
}
else
{
lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_del_object(v___x_1220_);
lean_dec(v_a_1218_);
lean_dec_ref(v___f_1205_);
lean_dec(v_interestWaiter_1204_);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = 0;
v___x_1232_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1));
v___x_1233_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1230_, v___x_1231_, v___x_1232_, v___f_1206_);
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object* v_interestWaiter_1235_, lean_object* v___f_1236_, lean_object* v___f_1237_, lean_object* v_x_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_1235_, v___f_1236_, v___f_1237_, v_x_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object* v_pendingProducer_1241_, uint8_t v_closed_1242_, lean_object* v_knownSize_1243_, lean_object* v_pendingIncomplete_1244_, lean_object* v_closeError_1245_, uint8_t v_closeAfterProducer_1246_, lean_object* v_interestWaiter_1247_, lean_object* v_pendingConsumer_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___f_1253_; 
v___x_1251_ = lean_box(v_closed_1242_);
v___x_1252_ = lean_box(v_closeAfterProducer_1246_);
v___f_1253_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1253_, 0, v_pendingProducer_1241_);
lean_closure_set(v___f_1253_, 1, v_pendingConsumer_1248_);
lean_closure_set(v___f_1253_, 2, v___x_1251_);
lean_closure_set(v___f_1253_, 3, v_knownSize_1243_);
lean_closure_set(v___f_1253_, 4, v_pendingIncomplete_1244_);
lean_closure_set(v___f_1253_, 5, v_closeError_1245_);
lean_closure_set(v___f_1253_, 6, v___x_1252_);
if (lean_obj_tag(v_interestWaiter_1247_) == 0)
{
lean_object* v___f_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_inc(v___y_1249_);
v___f_1254_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1254_, 0, v___f_1253_);
lean_closure_set(v___f_1254_, 1, v___y_1249_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = 0;
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_interestWaiter_1247_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
v___x_1259_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1255_, v___x_1256_, v___x_1258_, v___f_1254_);
return v___x_1259_;
}
else
{
lean_object* v_val_1260_; lean_object* v_finished_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_val_1260_ = lean_ctor_get(v_interestWaiter_1247_, 0);
v_finished_1261_ = lean_ctor_get(v_val_1260_, 0);
lean_inc(v_finished_1261_);
lean_inc(v___y_1249_);
v___f_1262_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1262_, 0, v___f_1253_);
lean_closure_set(v___f_1262_, 1, v___y_1249_);
lean_inc_ref(v___f_1262_);
v___f_1263_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1263_, 0, v_interestWaiter_1247_);
lean_closure_set(v___f_1263_, 1, v___f_1262_);
lean_closure_set(v___f_1263_, 2, v___f_1262_);
v___x_1264_ = lean_unsigned_to_nat(0u);
v___x_1265_ = 0;
v___x_1266_ = lean_st_ref_get(v_finished_1261_);
lean_dec(v_finished_1261_);
v___x_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
v___x_1269_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1264_, v___x_1265_, v___x_1268_, v___f_1263_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object* v_pendingProducer_1270_, lean_object* v_closed_1271_, lean_object* v_knownSize_1272_, lean_object* v_pendingIncomplete_1273_, lean_object* v_closeError_1274_, lean_object* v_closeAfterProducer_1275_, lean_object* v_interestWaiter_1276_, lean_object* v_pendingConsumer_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v_closed_boxed_1280_; uint8_t v_closeAfterProducer_boxed_1281_; lean_object* v_res_1282_; 
v_closed_boxed_1280_ = lean_unbox(v_closed_1271_);
v_closeAfterProducer_boxed_1281_ = lean_unbox(v_closeAfterProducer_1275_);
v_res_1282_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_1270_, v_closed_boxed_1280_, v_knownSize_1272_, v_pendingIncomplete_1273_, v_closeError_1274_, v_closeAfterProducer_boxed_1281_, v_interestWaiter_1276_, v_pendingConsumer_1277_, v___y_1278_);
lean_dec(v___y_1278_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object* v___f_1283_, lean_object* v___y_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v___f_1283_);
v_a_1287_ = lean_ctor_get(v_x_1285_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_x_1285_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1289_ = v_x_1285_;
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v_x_1285_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
return v___x_1293_;
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1297_; 
v_a_1296_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v_x_1285_, 1);
lean_inc(v___y_1284_);
v___x_1297_ = lean_apply_3(v___f_1283_, v_a_1296_, v___y_1284_, lean_box(0));
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object* v___f_1298_, lean_object* v___y_1299_, lean_object* v_x_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_1298_, v___y_1299_, v_x_1300_);
lean_dec(v___y_1299_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object* v___f_1303_, lean_object* v_a_1304_, lean_object* v_x_1305_){
_start:
{
if (lean_obj_tag(v_x_1305_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref(v___f_1303_);
v_a_1307_ = lean_ctor_get(v_x_1305_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_x_1305_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1309_ = v_x_1305_;
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v_x_1305_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1317_; 
v_a_1316_ = lean_ctor_get(v_x_1305_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v_x_1305_, 1);
lean_inc(v_a_1304_);
v___x_1317_ = lean_apply_3(v___f_1303_, v_a_1316_, v_a_1304_, lean_box(0));
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object* v___f_1318_, lean_object* v_a_1319_, lean_object* v_x_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_1318_, v_a_1319_, v_x_1320_);
lean_dec(v_a_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object* v_pendingConsumer_1327_, lean_object* v___f_1328_, lean_object* v___f_1329_, lean_object* v_x_1330_){
_start:
{
if (lean_obj_tag(v_x_1330_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v___f_1329_);
lean_dec_ref(v___f_1328_);
lean_dec(v_pendingConsumer_1327_);
v_a_1332_ = lean_ctor_get(v_x_1330_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_x_1330_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1334_ = v_x_1330_;
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v_x_1330_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1357_; 
v_a_1341_ = lean_ctor_get(v_x_1330_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_x_1330_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1343_ = v_x_1330_;
v_isShared_1344_ = v_isSharedCheck_1357_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v_x_1330_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1357_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_unbox(v_a_1341_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_dec_ref(v___f_1329_);
v___x_1346_ = lean_unsigned_to_nat(0u);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v_pendingConsumer_1327_);
v___x_1348_ = v___x_1343_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_pendingConsumer_1327_);
v___x_1348_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
v___x_1350_ = lean_unbox(v_a_1341_);
lean_dec(v_a_1341_);
v___x_1351_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1346_, v___x_1350_, v___x_1349_, v___f_1328_);
return v___x_1351_;
}
}
else
{
lean_object* v___x_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_del_object(v___x_1343_);
lean_dec(v_a_1341_);
lean_dec_ref(v___f_1328_);
lean_dec(v_pendingConsumer_1327_);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = 0;
v___x_1355_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1));
v___x_1356_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1353_, v___x_1354_, v___x_1355_, v___f_1329_);
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object* v_pendingConsumer_1358_, lean_object* v___f_1359_, lean_object* v___f_1360_, lean_object* v_x_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_1358_, v___f_1359_, v___f_1360_, v_x_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object* v_a_1364_, lean_object* v_x_1365_){
_start:
{
if (lean_obj_tag(v_x_1365_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1375_; 
v_a_1367_ = lean_ctor_get(v_x_1365_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_x_1365_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1369_ = v_x_1365_;
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v_x_1365_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1418_; 
v_a_1376_ = lean_ctor_get(v_x_1365_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1365_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1378_ = v_x_1365_;
v_isShared_1379_ = v_isSharedCheck_1418_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v_x_1365_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1418_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_pendingProducer_1380_; lean_object* v_pendingConsumer_1381_; lean_object* v_interestWaiter_1382_; uint8_t v_closed_1383_; lean_object* v_knownSize_1384_; lean_object* v_pendingIncomplete_1385_; lean_object* v_closeError_1386_; uint8_t v_closeAfterProducer_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___f_1390_; lean_object* v___y_1392_; 
v_pendingProducer_1380_ = lean_ctor_get(v_a_1376_, 0);
lean_inc(v_pendingProducer_1380_);
v_pendingConsumer_1381_ = lean_ctor_get(v_a_1376_, 1);
lean_inc(v_pendingConsumer_1381_);
v_interestWaiter_1382_ = lean_ctor_get(v_a_1376_, 2);
lean_inc(v_interestWaiter_1382_);
v_closed_1383_ = lean_ctor_get_uint8(v_a_1376_, sizeof(void*)*6);
v_knownSize_1384_ = lean_ctor_get(v_a_1376_, 3);
lean_inc(v_knownSize_1384_);
v_pendingIncomplete_1385_ = lean_ctor_get(v_a_1376_, 4);
lean_inc(v_pendingIncomplete_1385_);
v_closeError_1386_ = lean_ctor_get(v_a_1376_, 5);
lean_inc(v_closeError_1386_);
v_closeAfterProducer_1387_ = lean_ctor_get_uint8(v_a_1376_, sizeof(void*)*6 + 1);
lean_dec(v_a_1376_);
v___x_1388_ = lean_box(v_closed_1383_);
v___x_1389_ = lean_box(v_closeAfterProducer_1387_);
v___f_1390_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed), 10, 7);
lean_closure_set(v___f_1390_, 0, v_pendingProducer_1380_);
lean_closure_set(v___f_1390_, 1, v___x_1388_);
lean_closure_set(v___f_1390_, 2, v_knownSize_1384_);
lean_closure_set(v___f_1390_, 3, v_pendingIncomplete_1385_);
lean_closure_set(v___f_1390_, 4, v_closeError_1386_);
lean_closure_set(v___f_1390_, 5, v___x_1389_);
lean_closure_set(v___f_1390_, 6, v_interestWaiter_1382_);
if (lean_obj_tag(v_pendingConsumer_1381_) == 1)
{
lean_object* v_val_1401_; 
v_val_1401_ = lean_ctor_get(v_pendingConsumer_1381_, 0);
lean_inc(v_val_1401_);
if (lean_obj_tag(v_val_1401_) == 1)
{
lean_object* v_finished_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1417_; 
lean_del_object(v___x_1378_);
v_finished_1402_ = lean_ctor_get(v_val_1401_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_val_1401_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1404_ = v_val_1401_;
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_finished_1402_);
lean_dec(v_val_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_finished_1406_; lean_object* v___f_1407_; lean_object* v___f_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
v_finished_1406_ = lean_ctor_get(v_finished_1402_, 0);
lean_inc(v_finished_1406_);
lean_dec_ref(v_finished_1402_);
lean_inc(v_a_1364_);
v___f_1407_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1407_, 0, v___f_1390_);
lean_closure_set(v___f_1407_, 1, v_a_1364_);
lean_inc_ref(v___f_1407_);
v___f_1408_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1408_, 0, v_pendingConsumer_1381_);
lean_closure_set(v___f_1408_, 1, v___f_1407_);
lean_closure_set(v___f_1408_, 2, v___f_1407_);
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = 0;
v___x_1411_ = lean_st_ref_get(v_finished_1406_);
lean_dec(v_finished_1406_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1411_);
v___x_1413_ = v___x_1404_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
v___x_1415_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1409_, v___x_1410_, v___x_1414_, v___f_1408_);
return v___x_1415_;
}
}
}
else
{
lean_dec(v_val_1401_);
v___y_1392_ = v_a_1364_;
goto v___jp_1391_;
}
}
else
{
v___y_1392_ = v_a_1364_;
goto v___jp_1391_;
}
v___jp_1391_:
{
lean_object* v___f_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1397_; 
lean_inc(v___y_1392_);
v___f_1393_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1393_, 0, v___f_1390_);
lean_closure_set(v___f_1393_, 1, v___y_1392_);
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = 0;
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v_pendingConsumer_1381_);
v___x_1397_ = v___x_1378_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_pendingConsumer_1381_);
v___x_1397_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
v___x_1399_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1394_, v___x_1395_, v___x_1398_, v___f_1393_);
return v___x_1399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object* v_a_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_1419_, v_x_1420_);
lean_dec(v_a_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object* v_a_1423_){
_start:
{
lean_object* v___f_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_inc(v_a_1423_);
v___f_1425_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1425_, 0, v_a_1423_);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = 0;
v___x_1428_ = lean_st_ref_get(v_a_1423_);
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
v___x_1431_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1426_, v___x_1427_, v___x_1430_, v___f_1425_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object* v_a_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_1432_);
lean_dec(v_a_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object* v___y_1435_){
_start:
{
if (lean_obj_tag(v___y_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___y_1435_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___y_1435_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___y_1435_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___y_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
v_a_1444_ = lean_ctor_get(v___y_1435_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___y_1435_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1446_ = v___y_1435_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___y_1435_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_fst_1448_; lean_object* v___x_1450_; 
v_fst_1448_ = lean_ctor_get(v_a_1444_, 0);
lean_inc(v_fst_1448_);
lean_dec(v_a_1444_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v_fst_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_fst_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object* v_mutex_1453_, lean_object* v_x_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_io_basemutex_unlock(v_mutex_1453_);
v___x_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_1459_, lean_object* v_x_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(v_mutex_1459_, v_x_1460_);
lean_dec(v_x_1460_);
lean_dec(v_mutex_1459_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object* v_k_1463_, lean_object* v_ref_1464_, lean_object* v_x_1465_){
_start:
{
if (lean_obj_tag(v_x_1465_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_ref_1464_);
lean_dec_ref(v_k_1463_);
v_a_1467_ = lean_ctor_get(v_x_1465_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_x_1465_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1469_ = v_x_1465_;
v_isShared_1470_ = v_isSharedCheck_1475_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v_x_1465_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1475_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
}
else
{
lean_object* v___x_1476_; 
lean_dec_ref_known(v_x_1465_, 1);
v___x_1476_ = lean_apply_2(v_k_1463_, v_ref_1464_, lean_box(0));
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object* v_k_1477_, lean_object* v_ref_1478_, lean_object* v_x_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(v_k_1477_, v_ref_1478_, v_x_1479_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object* v_mutex_1482_, lean_object* v___f_1483_){
_start:
{
lean_object* v___x_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1485_ = lean_unsigned_to_nat(0u);
v___x_1486_ = 0;
v___x_1487_ = lean_io_basemutex_lock(v_mutex_1482_);
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
v___x_1490_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1485_, v___x_1486_, v___x_1489_, v___f_1483_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_1491_, lean_object* v___f_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(v_mutex_1491_, v___f_1492_);
lean_dec(v_mutex_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(lean_object* v_mutex_1496_, lean_object* v_k_1497_){
_start:
{
lean_object* v_ref_1499_; lean_object* v_mutex_1500_; lean_object* v___f_1501_; lean_object* v___f_1502_; lean_object* v___f_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___y_1509_; 
v_ref_1499_ = lean_ctor_get(v_mutex_1496_, 0);
lean_inc(v_ref_1499_);
v_mutex_1500_ = lean_ctor_get(v_mutex_1496_, 1);
lean_inc_n(v_mutex_1500_, 2);
lean_dec_ref(v_mutex_1496_);
v___f_1501_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0));
v___f_1502_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1502_, 0, v_mutex_1500_);
v___f_1503_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1503_, 0, v_k_1497_);
lean_closure_set(v___f_1503_, 1, v_ref_1499_);
v___f_1504_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1504_, 0, v_mutex_1500_);
lean_closure_set(v___f_1504_, 1, v___f_1503_);
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = 0;
v___x_1507_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1504_, v___f_1502_, v___x_1505_, v___x_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1511_; 
v_a_1511_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1507_, 1);
if (lean_obj_tag(v_a_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_a_1512_ = lean_ctor_get(v_a_1511_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_a_1511_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v_a_1511_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v_a_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
v___y_1509_ = v___x_1517_;
goto v___jp_1508_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1528_; 
v_a_1520_ = lean_ctor_get(v_a_1511_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_a_1511_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1522_ = v_a_1511_;
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v_a_1511_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_fst_1524_; lean_object* v___x_1526_; 
v_fst_1524_ = lean_ctor_get(v_a_1520_, 0);
lean_inc(v_fst_1524_);
lean_dec(v_a_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v_fst_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_fst_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
v___y_1509_ = v___x_1526_;
goto v___jp_1508_;
}
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1537_; 
v_a_1529_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1531_ = v___x_1507_;
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1507_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_task_map(v___f_1501_, v_a_1529_, v___x_1505_, v___x_1506_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
v___jp_1508_:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___y_1509_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___boxed(lean_object* v_mutex_1538_, lean_object* v_k_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1538_, v_k_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(lean_object* v_00_u03b1_1542_, lean_object* v_00_u03b2_1543_, lean_object* v_mutex_1544_, lean_object* v_k_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1544_, v_k_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed(lean_object* v_00_u03b1_1548_, lean_object* v_00_u03b2_1549_, lean_object* v_mutex_1550_, lean_object* v_k_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(v_00_u03b1_1548_, v_00_u03b2_1549_, v_mutex_1550_, v_k_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0(lean_object* v_x_1554_){
_start:
{
if (lean_obj_tag(v_x_1554_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1564_; 
v_a_1556_ = lean_ctor_get(v_x_1554_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_x_1554_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1558_ = v_x_1554_;
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v_x_1554_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v_x_1554_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v_x_1554_, 1);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_a_1565_);
return v___x_1566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(lean_object* v_x_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_Http_Body_Stream_tryRecv___lam__0(v_x_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object* v_a_1570_, lean_object* v___f_1571_, lean_object* v_x_1572_){
_start:
{
if (lean_obj_tag(v_x_1572_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v___f_1571_);
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
if (lean_obj_tag(v_a_1583_) == 1)
{
lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v___f_1571_);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_a_1583_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_a_1583_, 0);
lean_dec(v_unused_1592_);
v___x_1585_ = v_a_1583_;
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
else
{
lean_dec(v_a_1583_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v_x_1572_);
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_x_1572_);
v___x_1588_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
return v___x_1589_;
}
}
}
else
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_a_1583_);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v_x_1572_, 0);
lean_dec(v_unused_1605_);
v___x_1594_ = v_x_1572_;
v_isShared_1595_ = v_isSharedCheck_1604_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v_x_1572_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1604_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = 0;
v___x_1598_ = lean_st_ref_get(v_a_1570_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1598_);
v___x_1600_ = v___x_1594_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
v___x_1602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1596_, v___x_1597_, v___x_1601_, v___f_1571_);
return v___x_1602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object* v_a_1606_, lean_object* v___f_1607_, lean_object* v_x_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_a_1606_, v___f_1607_, v_x_1608_);
lean_dec(v_a_1606_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object* v_x_1615_){
_start:
{
if (lean_obj_tag(v_x_1615_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1625_; 
v_a_1617_ = lean_ctor_get(v_x_1615_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1615_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1619_ = v_x_1615_;
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v_x_1615_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
return v___x_1623_;
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1644_; 
v_a_1626_ = lean_ctor_get(v_x_1615_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_x_1615_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1628_ = v_x_1615_;
v_isShared_1629_ = v_isSharedCheck_1644_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v_x_1615_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1644_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_closeError_1630_; 
v_closeError_1630_ = lean_ctor_get(v_a_1626_, 5);
lean_inc(v_closeError_1630_);
lean_dec(v_a_1626_);
if (lean_obj_tag(v_closeError_1630_) == 1)
{
lean_object* v_val_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1642_; 
v_val_1631_ = lean_ctor_get(v_closeError_1630_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_closeError_1630_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1633_ = v_closeError_1630_;
v_isShared_1634_ = v_isSharedCheck_1642_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_val_1631_);
lean_dec(v_closeError_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1642_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 0);
lean_ctor_set(v___x_1628_, 0, v_val_1631_);
v___x_1636_ = v___x_1628_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_val_1631_);
v___x_1636_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1636_);
v___x_1638_ = v___x_1633_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
}
}
else
{
lean_object* v___x_1643_; 
lean_dec(v_closeError_1630_);
lean_del_object(v___x_1628_);
v___x_1643_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__1));
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object* v_x_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_x_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(lean_object* v___f_1648_, lean_object* v_a_1649_, lean_object* v_x_1650_){
_start:
{
if (lean_obj_tag(v_x_1650_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v___f_1648_);
v_a_1652_ = lean_ctor_get(v_x_1650_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_x_1650_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1654_ = v_x_1650_;
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v_x_1650_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v_x_1650_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v_x_1650_, 1);
lean_inc(v_a_1649_);
v___x_1662_ = lean_apply_3(v___f_1648_, v_a_1661_, v_a_1649_, lean_box(0));
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed(lean_object* v___f_1663_, lean_object* v_a_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(v___f_1663_, v_a_1664_, v_x_1665_);
lean_dec(v_a_1664_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__0(lean_object* v___y_1668_){
_start:
{
if (lean_obj_tag(v___y_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___y_1668_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___y_1668_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___y_1668_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___y_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1685_; 
v_a_1677_ = lean_ctor_get(v___y_1668_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___y_1668_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1679_ = v___y_1668_;
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___y_1668_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v_a_1677_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8(lean_object* v___f_1686_, lean_object* v___y_1687_, lean_object* v_knownSize_1688_, lean_object* v_a_1689_, lean_object* v_val_1690_, lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_knownSize_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___f_1686_);
v_a_1693_ = lean_ctor_get(v_x_1691_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1691_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1695_ = v_x_1691_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v_x_1691_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; uint8_t v___x_1703_; 
v_a_1702_ = lean_ctor_get(v_x_1691_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v_x_1691_, 1);
v___x_1703_ = lean_unbox(v_a_1702_);
lean_dec(v_a_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_box(0);
lean_inc(v_a_1689_);
v___x_1705_ = lean_apply_5(v___f_1686_, v___x_1704_, v___y_1687_, v_knownSize_1688_, v_a_1689_, lean_box(0));
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec(v___y_1687_);
v___x_1706_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1688_, v_val_1690_);
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_box(0);
lean_inc(v_a_1689_);
v___x_1709_ = lean_apply_5(v___f_1686_, v___x_1708_, v___x_1707_, v___x_1706_, v_a_1689_, lean_box(0));
return v___x_1709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8___boxed(lean_object* v___f_1710_, lean_object* v___y_1711_, lean_object* v_knownSize_1712_, lean_object* v_a_1713_, lean_object* v_val_1714_, lean_object* v_x_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8(v___f_1710_, v___y_1711_, v_knownSize_1712_, v_a_1713_, v_val_1714_, v_x_1715_);
lean_dec_ref(v_val_1714_);
lean_dec(v_a_1713_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6(lean_object* v___f_1718_, lean_object* v___y_1719_, lean_object* v_knownSize_1720_, lean_object* v_a_1721_, lean_object* v_x_1722_){
_start:
{
if (lean_obj_tag(v_x_1722_) == 0)
{
lean_object* v___x_1724_; 
lean_dec(v_knownSize_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___f_1718_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_x_1722_);
return v___x_1724_;
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v_x_1722_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v_x_1722_, 1);
lean_inc(v_a_1721_);
v___x_1726_ = lean_apply_5(v___f_1718_, v_a_1725_, v___y_1719_, v_knownSize_1720_, v_a_1721_, lean_box(0));
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6___boxed(lean_object* v___f_1727_, lean_object* v___y_1728_, lean_object* v_knownSize_1729_, lean_object* v_a_1730_, lean_object* v_x_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6(v___f_1727_, v___y_1728_, v_knownSize_1729_, v_a_1730_, v_x_1731_);
lean_dec(v_a_1730_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4(lean_object* v___f_1734_, lean_object* v___y_1735_, lean_object* v_x_1736_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
lean_object* v___x_1738_; 
lean_dec_ref(v___f_1734_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_x_1736_);
return v___x_1738_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v_x_1736_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v_x_1736_, 1);
lean_inc(v___y_1735_);
v___x_1740_ = lean_apply_3(v___f_1734_, v_a_1739_, v___y_1735_, lean_box(0));
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed(lean_object* v___f_1741_, lean_object* v___y_1742_, lean_object* v_x_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4(v___f_1741_, v___y_1742_, v_x_1743_);
lean_dec(v___y_1742_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1(uint8_t v___x_1746_, lean_object* v_knownSize_1747_, lean_object* v_closeError_1748_, uint8_t v_closed_1749_, lean_object* v___y_1750_, lean_object* v_x_1751_){
_start:
{
if (lean_obj_tag(v_x_1751_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_closeError_1748_);
lean_dec(v_knownSize_1747_);
v_a_1753_ = lean_ctor_get(v_x_1751_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_x_1751_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1755_ = v_x_1751_;
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v_x_1751_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_a_1762_ = lean_ctor_get(v_x_1751_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v_x_1751_, 1);
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1764_, 0, v_a_1762_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
lean_ctor_set(v___x_1764_, 2, v___x_1763_);
lean_ctor_set(v___x_1764_, 3, v_knownSize_1747_);
lean_ctor_set(v___x_1764_, 4, v___x_1763_);
lean_ctor_set(v___x_1764_, 5, v_closeError_1748_);
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*6, v___x_1746_);
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*6 + 1, v_closed_1749_);
v___x_1765_ = lean_st_ref_swap(v___y_1750_, v___x_1764_);
lean_dec(v___x_1765_);
v___x_1766_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1___boxed(lean_object* v___x_1767_, lean_object* v_knownSize_1768_, lean_object* v_closeError_1769_, lean_object* v_closed_1770_, lean_object* v___y_1771_, lean_object* v_x_1772_, lean_object* v___y_1773_){
_start:
{
uint8_t v___x_11055__boxed_1774_; uint8_t v_closed_boxed_1775_; lean_object* v_res_1776_; 
v___x_11055__boxed_1774_ = lean_unbox(v___x_1767_);
v_closed_boxed_1775_ = lean_unbox(v_closed_1770_);
v_res_1776_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1(v___x_11055__boxed_1774_, v_knownSize_1768_, v_closeError_1769_, v_closed_boxed_1775_, v___y_1771_, v_x_1772_);
lean_dec(v___y_1771_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3(lean_object* v_val_1777_, lean_object* v_x_1778_){
_start:
{
if (lean_obj_tag(v_x_1778_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v_val_1777_);
v_a_1780_ = lean_ctor_get(v_x_1778_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_x_1778_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1782_ = v_x_1778_;
v_isShared_1783_ = v_isSharedCheck_1788_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v_x_1778_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1788_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
return v___x_1786_;
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1798_; 
v_a_1789_ = lean_ctor_get(v_x_1778_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_x_1778_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1791_ = v_x_1778_;
v_isShared_1792_ = v_isSharedCheck_1798_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v_x_1778_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1798_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_val_1777_);
lean_ctor_set(v___x_1793_, 1, v_a_1789_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1793_);
v___x_1795_ = v___x_1791_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3___boxed(lean_object* v_val_1799_, lean_object* v_x_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3(v_val_1799_, v_x_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2(lean_object* v_leftover_1807_, uint8_t v___x_1808_, lean_object* v_knownSize_1809_, lean_object* v_closeError_1810_, uint8_t v_closed_1811_, lean_object* v___f_1812_, lean_object* v_____r_1813_, lean_object* v___y_1814_){
_start:
{
if (lean_obj_tag(v_leftover_1807_) == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec_ref(v___f_1812_);
v___x_1816_ = lean_box(v___x_1808_);
v___x_1817_ = lean_box(v_closed_1811_);
lean_inc(v___y_1814_);
v___f_1818_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1818_, 0, v___x_1816_);
lean_closure_set(v___f_1818_, 1, v_knownSize_1809_);
lean_closure_set(v___f_1818_, 2, v_closeError_1810_);
lean_closure_set(v___f_1818_, 3, v___x_1817_);
lean_closure_set(v___f_1818_, 4, v___y_1814_);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__1));
v___x_1821_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1819_, v_closed_1811_, v___x_1820_, v___f_1818_);
return v___x_1821_;
}
else
{
lean_object* v_val_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1869_; 
v_val_1822_ = lean_ctor_get(v_leftover_1807_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_leftover_1807_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1824_ = v_leftover_1807_;
v_isShared_1825_ = v_isSharedCheck_1869_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_val_1822_);
lean_dec(v_leftover_1807_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1869_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___y_1836_; 
v___x_1826_ = lean_box(v___x_1808_);
v___x_1827_ = lean_box(v_closed_1811_);
lean_inc(v___y_1814_);
v___f_1828_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1828_, 0, v___x_1826_);
lean_closure_set(v___f_1828_, 1, v_knownSize_1809_);
lean_closure_set(v___f_1828_, 2, v_closeError_1810_);
lean_closure_set(v___f_1828_, 3, v___x_1827_);
lean_closure_set(v___f_1828_, 4, v___y_1814_);
v___f_1829_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1829_, 0, v_val_1822_);
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_io_promise_new();
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
v___x_1834_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1830_, v_closed_1811_, v___x_1833_, v___f_1829_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1839_; 
lean_dec_ref(v___f_1812_);
v_a_1839_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1834_, 1);
if (lean_obj_tag(v_a_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_del_object(v___x_1824_);
v_a_1840_ = lean_ctor_get(v_a_1839_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_a_1839_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v_a_1839_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v_a_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
v___y_1836_ = v___x_1845_;
goto v___jp_1835_;
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1858_; 
v_a_1848_ = lean_ctor_get(v_a_1839_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_a_1839_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1850_ = v_a_1839_;
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v_a_1839_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v_a_1848_);
v___x_1853_ = v___x_1824_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1853_);
v___x_1855_ = v___x_1850_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
v___y_1836_ = v___x_1855_;
goto v___jp_1835_;
}
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1868_; 
lean_del_object(v___x_1824_);
v_a_1859_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1861_ = v___x_1834_;
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1834_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = lean_task_map(v___f_1812_, v_a_1859_, v___x_1830_, v_closed_1811_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; 
v___x_1866_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1830_, v_closed_1811_, v___x_1865_, v___f_1828_);
return v___x_1866_;
}
}
}
v___jp_1835_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___y_1836_);
v___x_1838_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1830_, v_closed_1811_, v___x_1837_, v___f_1828_);
return v___x_1838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___boxed(lean_object* v_leftover_1870_, lean_object* v___x_1871_, lean_object* v_knownSize_1872_, lean_object* v_closeError_1873_, lean_object* v_closed_1874_, lean_object* v___f_1875_, lean_object* v_____r_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
uint8_t v___x_11152__boxed_1879_; uint8_t v_closed_boxed_1880_; lean_object* v_res_1881_; 
v___x_11152__boxed_1879_ = lean_unbox(v___x_1871_);
v_closed_boxed_1880_ = lean_unbox(v_closed_1874_);
v_res_1881_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2(v_leftover_1870_, v___x_11152__boxed_1879_, v_knownSize_1872_, v_closeError_1873_, v_closed_boxed_1880_, v___f_1875_, v_____r_1876_, v___y_1877_);
lean_dec(v___y_1877_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5(lean_object* v_pendingProducer_1882_, lean_object* v___f_1883_, uint8_t v_closed_1884_, lean_object* v_____r_1885_, lean_object* v___y_1886_){
_start:
{
if (lean_obj_tag(v_pendingProducer_1882_) == 1)
{
lean_object* v_val_1888_; lean_object* v_done_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_val_1888_ = lean_ctor_get(v_pendingProducer_1882_, 0);
v_done_1889_ = lean_ctor_get(v_val_1888_, 1);
lean_inc(v___y_1886_);
v___f_1890_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1890_, 0, v___f_1883_);
lean_closure_set(v___f_1890_, 1, v___y_1886_);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = lean_box(v_closed_1884_);
v___x_1893_ = lean_io_promise_resolve(v___x_1892_, v_done_1889_);
v___x_1894_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1895_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1891_, v_closed_1884_, v___x_1894_, v___f_1890_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_box(0);
lean_inc(v___y_1886_);
v___x_1897_ = lean_apply_3(v___f_1883_, v___x_1896_, v___y_1886_, lean_box(0));
return v___x_1897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5___boxed(lean_object* v_pendingProducer_1898_, lean_object* v___f_1899_, lean_object* v_closed_1900_, lean_object* v_____r_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
uint8_t v_closed_boxed_1904_; lean_object* v_res_1905_; 
v_closed_boxed_1904_ = lean_unbox(v_closed_1900_);
v_res_1905_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5(v_pendingProducer_1898_, v___f_1899_, v_closed_boxed_1904_, v_____r_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec(v_pendingProducer_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7(uint8_t v___x_1906_, lean_object* v_closeError_1907_, uint8_t v_closed_1908_, lean_object* v___f_1909_, lean_object* v_pendingProducer_1910_, lean_object* v_interestWaiter_1911_, lean_object* v_____r_1912_, lean_object* v_leftover_1913_, lean_object* v_knownSize_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; lean_object* v___f_1921_; 
v___x_1917_ = lean_box(v___x_1906_);
v___x_1918_ = lean_box(v_closed_1908_);
v___f_1919_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___boxed), 9, 6);
lean_closure_set(v___f_1919_, 0, v_leftover_1913_);
lean_closure_set(v___f_1919_, 1, v___x_1917_);
lean_closure_set(v___f_1919_, 2, v_knownSize_1914_);
lean_closure_set(v___f_1919_, 3, v_closeError_1907_);
lean_closure_set(v___f_1919_, 4, v___x_1918_);
lean_closure_set(v___f_1919_, 5, v___f_1909_);
v___x_1920_ = lean_box(v_closed_1908_);
lean_inc_ref(v___f_1919_);
lean_inc(v_pendingProducer_1910_);
v___f_1921_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1921_, 0, v_pendingProducer_1910_);
lean_closure_set(v___f_1921_, 1, v___f_1919_);
lean_closure_set(v___f_1921_, 2, v___x_1920_);
if (lean_obj_tag(v_interestWaiter_1911_) == 1)
{
lean_object* v_val_1922_; lean_object* v___f_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec_ref(v___f_1919_);
lean_dec(v_pendingProducer_1910_);
v_val_1922_ = lean_ctor_get(v_interestWaiter_1911_, 0);
lean_inc(v___y_1915_);
v___f_1923_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1923_, 0, v___f_1921_);
lean_closure_set(v___f_1923_, 1, v___y_1915_);
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1922_, v_closed_1908_);
v___x_1926_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1927_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1924_, v_closed_1908_, v___x_1926_, v___f_1923_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec_ref(v___f_1921_);
v___x_1928_ = lean_box(0);
v___x_1929_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5(v_pendingProducer_1910_, v___f_1919_, v_closed_1908_, v___x_1928_, v___y_1915_);
lean_dec(v_pendingProducer_1910_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7___boxed(lean_object* v___x_1930_, lean_object* v_closeError_1931_, lean_object* v_closed_1932_, lean_object* v___f_1933_, lean_object* v_pendingProducer_1934_, lean_object* v_interestWaiter_1935_, lean_object* v_____r_1936_, lean_object* v_leftover_1937_, lean_object* v_knownSize_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
uint8_t v___x_11319__boxed_1941_; uint8_t v_closed_boxed_1942_; lean_object* v_res_1943_; 
v___x_11319__boxed_1941_ = lean_unbox(v___x_1930_);
v_closed_boxed_1942_ = lean_unbox(v_closed_1932_);
v_res_1943_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7(v___x_11319__boxed_1941_, v_closeError_1931_, v_closed_boxed_1942_, v___f_1933_, v_pendingProducer_1934_, v_interestWaiter_1935_, v_____r_1936_, v_leftover_1937_, v_knownSize_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec(v_interestWaiter_1935_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9(lean_object* v___f_1944_, lean_object* v_a_1945_, lean_object* v_x_1946_){
_start:
{
if (lean_obj_tag(v_x_1946_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v___f_1944_);
v_a_1948_ = lean_ctor_get(v_x_1946_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_x_1946_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1950_ = v_x_1946_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v_x_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2035_; 
v_a_1957_ = lean_ctor_get(v_x_1946_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_x_1946_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_1959_ = v_x_1946_;
v_isShared_1960_ = v_isSharedCheck_2035_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v_x_1946_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2035_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v_pendingProducer_1961_; lean_object* v_pendingConsumer_1962_; lean_object* v_interestWaiter_1963_; uint8_t v_closed_1964_; lean_object* v_knownSize_1965_; lean_object* v_pendingIncomplete_1966_; lean_object* v_closeError_1967_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; 
v_pendingProducer_1961_ = lean_ctor_get(v_a_1957_, 0);
lean_inc(v_pendingProducer_1961_);
v_pendingConsumer_1962_ = lean_ctor_get(v_a_1957_, 1);
lean_inc(v_pendingConsumer_1962_);
v_interestWaiter_1963_ = lean_ctor_get(v_a_1957_, 2);
lean_inc(v_interestWaiter_1963_);
v_closed_1964_ = lean_ctor_get_uint8(v_a_1957_, sizeof(void*)*6);
v_knownSize_1965_ = lean_ctor_get(v_a_1957_, 3);
lean_inc(v_knownSize_1965_);
v_pendingIncomplete_1966_ = lean_ctor_get(v_a_1957_, 4);
lean_inc(v_pendingIncomplete_1966_);
v_closeError_1967_ = lean_ctor_get(v_a_1957_, 5);
lean_inc(v_closeError_1967_);
lean_dec(v_a_1957_);
if (v_closed_1964_ == 0)
{
uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___f_1979_; lean_object* v___y_1981_; 
v___x_1976_ = 1;
v___x_1977_ = lean_box(v___x_1976_);
v___x_1978_ = lean_box(v_closed_1964_);
lean_inc(v_interestWaiter_1963_);
lean_inc(v_pendingProducer_1961_);
lean_inc_ref(v___f_1944_);
lean_inc(v_closeError_1967_);
v___f_1979_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7___boxed), 11, 6);
lean_closure_set(v___f_1979_, 0, v___x_1977_);
lean_closure_set(v___f_1979_, 1, v_closeError_1967_);
lean_closure_set(v___f_1979_, 2, v___x_1978_);
lean_closure_set(v___f_1979_, 3, v___f_1944_);
lean_closure_set(v___f_1979_, 4, v_pendingProducer_1961_);
lean_closure_set(v___f_1979_, 5, v_interestWaiter_1963_);
if (lean_obj_tag(v_pendingProducer_1961_) == 0)
{
if (lean_obj_tag(v_pendingIncomplete_1966_) == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_box(0);
v___y_1981_ = v___x_2018_;
goto v___jp_1980_;
}
else
{
lean_object* v_val_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2032_; 
v_val_2019_ = lean_ctor_get(v_pendingIncomplete_1966_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_pendingIncomplete_1966_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2021_ = v_pendingIncomplete_1966_;
v_isShared_2022_ = v_isSharedCheck_2032_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_val_2019_);
lean_dec(v_pendingIncomplete_1966_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2032_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v_data_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2023_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(v_val_2019_);
v_data_2024_ = lean_ctor_get(v___x_2023_, 0);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = lean_byte_array_size(v_data_2024_);
v___x_2027_ = lean_nat_dec_lt(v___x_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
lean_dec_ref(v___x_2023_);
lean_del_object(v___x_2021_);
v___x_2028_ = lean_box(0);
v___y_1981_ = v___x_2028_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_2030_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2023_);
v___x_2030_ = v___x_2021_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2023_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
v___y_1981_ = v___x_2030_;
goto v___jp_1980_;
}
}
}
}
}
else
{
lean_object* v___x_2033_; 
lean_dec(v_pendingIncomplete_1966_);
v___x_2033_ = lean_box(0);
v___y_1981_ = v___x_2033_;
goto v___jp_1980_;
}
v___jp_1980_:
{
if (lean_obj_tag(v_pendingConsumer_1962_) == 1)
{
lean_dec(v_interestWaiter_1963_);
lean_dec(v_pendingProducer_1961_);
lean_dec_ref(v___f_1944_);
if (lean_obj_tag(v___y_1981_) == 0)
{
lean_object* v_val_1982_; lean_object* v___f_1983_; 
v_val_1982_ = lean_ctor_get(v_pendingConsumer_1962_, 0);
lean_inc(v_val_1982_);
lean_dec_ref_known(v_pendingConsumer_1962_, 1);
lean_inc(v_a_1945_);
v___f_1983_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1983_, 0, v___f_1979_);
lean_closure_set(v___f_1983_, 1, v___y_1981_);
lean_closure_set(v___f_1983_, 2, v_knownSize_1965_);
lean_closure_set(v___f_1983_, 3, v_a_1945_);
if (lean_obj_tag(v_closeError_1967_) == 0)
{
lean_object* v___x_1985_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___y_1981_);
v___x_1985_ = v___x_1959_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___y_1981_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
v___y_1969_ = v___f_1983_;
v___y_1970_ = v_val_1982_;
v___y_1971_ = v___x_1985_;
goto v___jp_1968_;
}
}
else
{
lean_object* v_val_1987_; lean_object* v___x_1989_; 
v_val_1987_ = lean_ctor_get(v_closeError_1967_, 0);
lean_inc(v_val_1987_);
lean_dec_ref_known(v_closeError_1967_, 1);
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 0);
lean_ctor_set(v___x_1959_, 0, v_val_1987_);
v___x_1989_ = v___x_1959_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_val_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
v___y_1969_ = v___f_1983_;
v___y_1970_ = v_val_1982_;
v___y_1971_ = v___x_1989_;
goto v___jp_1968_;
}
}
}
else
{
lean_object* v_val_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_closeError_1967_);
v_val_1991_ = lean_ctor_get(v_pendingConsumer_1962_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_pendingConsumer_1962_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1993_ = v_pendingConsumer_1962_;
v_isShared_1994_ = v_isSharedCheck_2015_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_val_1991_);
lean_dec(v_pendingConsumer_1962_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2015_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_val_1995_; lean_object* v___f_1996_; lean_object* v___x_1998_; 
v_val_1995_ = lean_ctor_get(v___y_1981_, 0);
lean_inc(v_val_1995_);
lean_inc(v_a_1945_);
lean_inc_ref_n(v___y_1981_, 2);
v___f_1996_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8___boxed), 7, 5);
lean_closure_set(v___f_1996_, 0, v___f_1979_);
lean_closure_set(v___f_1996_, 1, v___y_1981_);
lean_closure_set(v___f_1996_, 2, v_knownSize_1965_);
lean_closure_set(v___f_1996_, 3, v_a_1945_);
lean_closure_set(v___f_1996_, 4, v_val_1995_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___y_1981_);
v___x_1998_ = v___x_1959_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___y_1981_);
v___x_1998_ = v_reuseFailAlloc_2014_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2012_; 
v_isSharedCheck_2012_ = !lean_is_exclusive(v___y_1981_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v___y_1981_, 0);
lean_dec(v_unused_2013_);
v___x_2000_ = v___y_1981_;
v_isShared_2001_ = v_isSharedCheck_2012_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v___y_1981_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2012_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_1991_, v___x_1998_);
lean_dec(v_val_1991_);
v___x_2004_ = lean_box(v___x_2003_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2004_);
v___x_2006_ = v___x_2000_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 0);
lean_ctor_set(v___x_1993_, 0, v___x_2006_);
v___x_2008_ = v___x_1993_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; 
v___x_2009_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2002_, v_closed_1964_, v___x_2008_, v___f_1996_);
return v___x_2009_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec_ref(v___f_1979_);
lean_dec(v_pendingConsumer_1962_);
lean_del_object(v___x_1959_);
v___x_2016_ = lean_box(0);
v___x_2017_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7(v___x_1976_, v_closeError_1967_, v_closed_1964_, v___f_1944_, v_pendingProducer_1961_, v_interestWaiter_1963_, v___x_2016_, v___y_1981_, v_knownSize_1965_, v_a_1945_);
lean_dec(v_interestWaiter_1963_);
return v___x_2017_;
}
}
}
else
{
lean_object* v___x_2034_; 
lean_dec(v_closeError_1967_);
lean_dec(v_pendingIncomplete_1966_);
lean_dec(v_knownSize_1965_);
lean_dec(v_interestWaiter_1963_);
lean_dec(v_pendingConsumer_1962_);
lean_dec(v_pendingProducer_1961_);
lean_del_object(v___x_1959_);
lean_dec_ref(v___f_1944_);
v___x_2034_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2034_;
}
v___jp_1968_:
{
lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1972_ = lean_unsigned_to_nat(0u);
v___x_1973_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v___y_1970_, v___y_1971_);
lean_dec_ref(v___y_1970_);
v___x_1974_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1975_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1972_, v_closed_1964_, v___x_1974_, v___y_1969_);
return v___x_1975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9___boxed(lean_object* v___f_2036_, lean_object* v_a_2037_, lean_object* v_x_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9(v___f_2036_, v_a_2037_, v_x_2038_);
lean_dec(v_a_2037_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(lean_object* v_a_2042_){
_start:
{
lean_object* v___f_2044_; lean_object* v___f_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___f_2044_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___closed__0));
lean_inc(v_a_2042_);
v___f_2045_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9___boxed), 4, 2);
lean_closure_set(v___f_2045_, 0, v___f_2044_);
lean_closure_set(v___f_2045_, 1, v_a_2042_);
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = 0;
v___x_2048_ = lean_st_ref_get(v_a_2042_);
v___x_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
v___x_2051_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2046_, v___x_2047_, v___x_2050_, v___f_2045_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_a_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v_a_2052_);
lean_dec(v_a_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(uint8_t v_closeAfterProducer_2055_, lean_object* v___f_2056_, lean_object* v___x_2057_, lean_object* v_a_2058_, uint8_t v___x_2059_, lean_object* v___f_2060_, lean_object* v_x_2061_){
_start:
{
if (lean_obj_tag(v_x_2061_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v___f_2060_);
lean_dec_ref(v___f_2056_);
v_a_2063_ = lean_ctor_get(v_x_2061_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_x_2061_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2065_ = v_x_2061_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v_x_2061_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
}
else
{
lean_dec_ref_known(v_x_2061_, 1);
if (v_closeAfterProducer_2055_ == 0)
{
lean_object* v___x_2072_; 
lean_dec_ref(v___f_2060_);
lean_inc(v_a_2058_);
v___x_2072_ = lean_apply_3(v___f_2056_, v___x_2057_, v_a_2058_, lean_box(0));
return v___x_2072_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec_ref(v___f_2056_);
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v_a_2058_);
v___x_2075_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2073_, v___x_2059_, v___x_2074_, v___f_2060_);
return v___x_2075_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed(lean_object* v_closeAfterProducer_2076_, lean_object* v___f_2077_, lean_object* v___x_2078_, lean_object* v_a_2079_, lean_object* v___x_2080_, lean_object* v___f_2081_, lean_object* v_x_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v_closeAfterProducer_boxed_2084_; uint8_t v___x_11569__boxed_2085_; lean_object* v_res_2086_; 
v_closeAfterProducer_boxed_2084_ = lean_unbox(v_closeAfterProducer_2076_);
v___x_11569__boxed_2085_ = lean_unbox(v___x_2080_);
v_res_2086_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(v_closeAfterProducer_boxed_2084_, v___f_2077_, v___x_2078_, v_a_2079_, v___x_11569__boxed_2085_, v___f_2081_, v_x_2082_);
lean_dec(v_a_2079_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3(uint8_t v_closeAfterProducer_2087_, lean_object* v___f_2088_, lean_object* v_a_2089_, uint8_t v___x_2090_, lean_object* v___f_2091_, lean_object* v_done_2092_, lean_object* v_x_2093_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v___f_2091_);
lean_dec_ref(v___f_2088_);
v_a_2095_ = lean_ctor_get(v_x_2093_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2097_ = v_x_2093_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v_x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
}
else
{
uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___f_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec_ref_known(v_x_2093_, 1);
v___x_2104_ = 1;
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_box(v_closeAfterProducer_2087_);
v___x_2107_ = lean_box(v___x_2090_);
lean_inc(v_a_2089_);
v___f_2108_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed), 8, 6);
lean_closure_set(v___f_2108_, 0, v___x_2106_);
lean_closure_set(v___f_2108_, 1, v___f_2088_);
lean_closure_set(v___f_2108_, 2, v___x_2105_);
lean_closure_set(v___f_2108_, 3, v_a_2089_);
lean_closure_set(v___f_2108_, 4, v___x_2107_);
lean_closure_set(v___f_2108_, 5, v___f_2091_);
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = lean_box(v___x_2104_);
v___x_2111_ = lean_io_promise_resolve(v___x_2110_, v_done_2092_);
v___x_2112_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2113_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2109_, v___x_2090_, v___x_2112_, v___f_2108_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3___boxed(lean_object* v_closeAfterProducer_2114_, lean_object* v___f_2115_, lean_object* v_a_2116_, lean_object* v___x_2117_, lean_object* v___f_2118_, lean_object* v_done_2119_, lean_object* v_x_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v_closeAfterProducer_boxed_2122_; uint8_t v___x_11616__boxed_2123_; lean_object* v_res_2124_; 
v_closeAfterProducer_boxed_2122_ = lean_unbox(v_closeAfterProducer_2114_);
v___x_11616__boxed_2123_ = lean_unbox(v___x_2117_);
v_res_2124_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3(v_closeAfterProducer_boxed_2122_, v___f_2115_, v_a_2116_, v___x_11616__boxed_2123_, v___f_2118_, v_done_2119_, v_x_2120_);
lean_dec(v_done_2119_);
lean_dec(v_a_2116_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(lean_object* v_chunk_2125_, lean_object* v_____r_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_chunk_2125_);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed(lean_object* v_chunk_2132_, lean_object* v_____r_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(v_chunk_2132_, v_____r_2133_, v___y_2134_);
lean_dec(v___y_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4(lean_object* v_a_2139_, lean_object* v_x_2140_){
_start:
{
if (lean_obj_tag(v_x_2140_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2150_; 
v_a_2142_ = lean_ctor_get(v_x_2140_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_x_2140_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2144_ = v_x_2140_;
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v_x_2140_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v_pendingProducer_2152_; 
v_a_2151_ = lean_ctor_get(v_x_2140_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v_x_2140_, 1);
v_pendingProducer_2152_ = lean_ctor_get(v_a_2151_, 0);
if (lean_obj_tag(v_pendingProducer_2152_) == 1)
{
lean_object* v_val_2153_; lean_object* v_pendingConsumer_2154_; lean_object* v_interestWaiter_2155_; uint8_t v_closed_2156_; lean_object* v_knownSize_2157_; lean_object* v_pendingIncomplete_2158_; lean_object* v_closeError_2159_; uint8_t v_closeAfterProducer_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2181_; 
v_val_2153_ = lean_ctor_get(v_pendingProducer_2152_, 0);
lean_inc(v_val_2153_);
v_pendingConsumer_2154_ = lean_ctor_get(v_a_2151_, 1);
v_interestWaiter_2155_ = lean_ctor_get(v_a_2151_, 2);
v_closed_2156_ = lean_ctor_get_uint8(v_a_2151_, sizeof(void*)*6);
v_knownSize_2157_ = lean_ctor_get(v_a_2151_, 3);
v_pendingIncomplete_2158_ = lean_ctor_get(v_a_2151_, 4);
v_closeError_2159_ = lean_ctor_get(v_a_2151_, 5);
v_closeAfterProducer_2160_ = lean_ctor_get_uint8(v_a_2151_, sizeof(void*)*6 + 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_a_2151_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v_a_2151_, 0);
lean_dec(v_unused_2182_);
v___x_2162_ = v_a_2151_;
v_isShared_2163_ = v_isSharedCheck_2181_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_closeError_2159_);
lean_inc(v_pendingIncomplete_2158_);
lean_inc(v_knownSize_2157_);
lean_inc(v_interestWaiter_2155_);
lean_inc(v_pendingConsumer_2154_);
lean_dec(v_a_2151_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2181_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_chunk_2164_; lean_object* v_done_2165_; lean_object* v___x_2166_; lean_object* v___f_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___f_2173_; lean_object* v___x_2175_; 
v_chunk_2164_ = lean_ctor_get(v_val_2153_, 0);
lean_inc_ref_n(v_chunk_2164_, 2);
v_done_2165_ = lean_ctor_get(v_val_2153_, 1);
lean_inc(v_done_2165_);
lean_dec(v_val_2153_);
v___x_2166_ = lean_box(0);
v___f_2167_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2167_, 0, v_chunk_2164_);
lean_inc_n(v_a_2139_, 2);
lean_inc_ref(v___f_2167_);
v___f_2168_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2168_, 0, v___f_2167_);
lean_closure_set(v___f_2168_, 1, v_a_2139_);
v___x_2169_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_2157_, v_chunk_2164_);
lean_dec_ref(v_chunk_2164_);
v___x_2170_ = 0;
v___x_2171_ = lean_box(v_closeAfterProducer_2160_);
v___x_2172_ = lean_box(v___x_2170_);
v___f_2173_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3___boxed), 8, 6);
lean_closure_set(v___f_2173_, 0, v___x_2171_);
lean_closure_set(v___f_2173_, 1, v___f_2167_);
lean_closure_set(v___f_2173_, 2, v_a_2139_);
lean_closure_set(v___f_2173_, 3, v___x_2172_);
lean_closure_set(v___f_2173_, 4, v___f_2168_);
lean_closure_set(v___f_2173_, 5, v_done_2165_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 3, v___x_2169_);
lean_ctor_set(v___x_2162_, 0, v___x_2166_);
v___x_2175_ = v___x_2162_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_pendingConsumer_2154_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_interestWaiter_2155_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v_pendingIncomplete_2158_);
lean_ctor_set(v_reuseFailAlloc_2180_, 5, v_closeError_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2180_, sizeof(void*)*6, v_closed_2156_);
v___x_2175_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_ctor_set_uint8(v___x_2175_, sizeof(void*)*6 + 1, v___x_2170_);
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2177_ = lean_st_ref_swap(v_a_2139_, v___x_2175_);
lean_dec(v___x_2177_);
v___x_2178_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2179_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2176_, v___x_2170_, v___x_2178_, v___f_2173_);
return v___x_2179_;
}
}
}
else
{
lean_object* v___x_2183_; 
lean_dec(v_a_2151_);
v___x_2183_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___closed__0));
return v___x_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___boxed(lean_object* v_a_2184_, lean_object* v_x_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4(v_a_2184_, v_x_2185_);
lean_dec(v_a_2184_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(lean_object* v_a_2188_){
_start:
{
lean_object* v___f_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_inc(v_a_2188_);
v___f_2190_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2190_, 0, v_a_2188_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = 0;
v___x_2193_ = lean_st_ref_get(v_a_2188_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
v___x_2196_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2191_, v___x_2192_, v___x_2195_, v___f_2190_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___boxed(lean_object* v_a_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_2197_);
lean_dec(v_a_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object* v_a_2201_){
_start:
{
lean_object* v___f_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___f_2203_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0));
lean_inc(v_a_2201_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2204_, 0, v_a_2201_);
lean_closure_set(v___f_2204_, 1, v___f_2203_);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = 0;
v___x_2207_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_2201_);
v___x_2208_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2205_, v___x_2206_, v___x_2207_, v___f_2204_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object* v_a_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_2209_);
lean_dec(v_a_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1(lean_object* v___y_2212_, lean_object* v___f_2213_, lean_object* v_x_2214_){
_start:
{
if (lean_obj_tag(v_x_2214_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v___f_2213_);
v_a_2216_ = lean_ctor_get(v_x_2214_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_x_2214_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2218_ = v_x_2214_;
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v_x_2214_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
}
else
{
lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref_known(v_x_2214_, 1);
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = 0;
v___x_2227_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2212_);
v___x_2228_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2225_, v___x_2226_, v___x_2227_, v___f_2213_);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(lean_object* v___y_2229_, lean_object* v___f_2230_, lean_object* v_x_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Std_Http_Body_Stream_tryRecv___lam__1(v___y_2229_, v___f_2230_, v_x_2231_);
lean_dec(v___y_2229_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2(lean_object* v___f_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___f_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_inc(v___y_2235_);
v___f_2237_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecv___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2237_, 0, v___y_2235_);
lean_closure_set(v___f_2237_, 1, v___f_2234_);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = 0;
v___x_2240_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2235_);
v___x_2241_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2238_, v___x_2239_, v___x_2240_, v___f_2237_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2___boxed(lean_object* v___f_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Std_Http_Body_Stream_tryRecv___lam__2(v___f_2242_, v___y_2243_);
lean_dec(v___y_2243_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv(lean_object* v_stream_2249_){
_start:
{
lean_object* v___f_2251_; lean_object* v___x_2252_; 
v___f_2251_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecv___closed__1));
v___x_2252_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2249_, v___f_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___boxed(lean_object* v_stream_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Std_Http_Body_Stream_tryRecv(v_stream_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(lean_object* v_x_2256_){
_start:
{
uint8_t v___y_2259_; 
if (lean_obj_tag(v_x_2256_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2271_; 
v_a_2263_ = lean_ctor_get(v_x_2256_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_x_2256_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2265_ = v_x_2256_;
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v_x_2256_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v_pendingProducer_2273_; 
v_a_2272_ = lean_ctor_get(v_x_2256_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v_x_2256_, 1);
v_pendingProducer_2273_ = lean_ctor_get(v_a_2272_, 0);
if (lean_obj_tag(v_pendingProducer_2273_) == 0)
{
uint8_t v_closed_2274_; 
v_closed_2274_ = lean_ctor_get_uint8(v_a_2272_, sizeof(void*)*6);
lean_dec(v_a_2272_);
v___y_2259_ = v_closed_2274_;
goto v___jp_2258_;
}
else
{
uint8_t v___x_2275_; 
lean_dec(v_a_2272_);
v___x_2275_ = 1;
v___y_2259_ = v___x_2275_;
goto v___jp_2258_;
}
}
v___jp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_box(v___y_2259_);
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed(lean_object* v_x_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(v_x_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(lean_object* v_a_2280_){
_start:
{
lean_object* v___f_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___f_2282_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0));
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2284_ = 0;
v___x_2285_ = lean_st_ref_get(v_a_2280_);
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
v___x_2288_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2283_, v___x_2284_, v___x_2287_, v___f_2282_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___boxed(lean_object* v_a_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v_a_2289_);
lean_dec(v_a_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0(lean_object* v_x_2292_){
_start:
{
if (lean_obj_tag(v_x_2292_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_a_2294_ = lean_ctor_get(v_x_2292_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_x_2292_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v_x_2292_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v_x_2292_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
return v___x_2300_;
}
}
}
else
{
lean_object* v_a_2303_; 
v_a_2303_ = lean_ctor_get(v_x_2292_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v_x_2292_, 1);
if (lean_obj_tag(v_a_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2312_; 
v_a_2304_ = lean_ctor_get(v_a_2303_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_a_2303_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2306_ = v_a_2303_;
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v_a_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2310_; 
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2322_; 
v_a_2313_ = lean_ctor_get(v_a_2303_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2303_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2315_ = v_a_2303_;
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v_a_2303_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2317_, 0, v_a_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
return v___x_2320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed(lean_object* v_x_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Std_Http_Body_Stream_tryRecvBody___lam__0(v_x_2323_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1(lean_object* v___y_2330_, lean_object* v___f_2331_, lean_object* v_x_2332_){
_start:
{
if (lean_obj_tag(v_x_2332_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v___f_2331_);
v_a_2334_ = lean_ctor_get(v_x_2332_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_x_2332_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2336_ = v_x_2332_;
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v_x_2332_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2343_; uint8_t v___x_2344_; 
v_a_2343_ = lean_ctor_get(v_x_2332_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v_x_2332_, 1);
v___x_2344_ = lean_unbox(v_a_2343_);
lean_dec(v_a_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec_ref(v___f_2331_);
v___x_2345_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1));
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = 0;
v___x_2348_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2330_);
v___x_2349_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2346_, v___x_2347_, v___x_2348_, v___f_2331_);
return v___x_2349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed(lean_object* v___y_2350_, lean_object* v___f_2351_, lean_object* v_x_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1(v___y_2350_, v___f_2351_, v_x_2352_);
lean_dec(v___y_2350_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2(lean_object* v___y_2355_, lean_object* v___f_2356_, lean_object* v_x_2357_){
_start:
{
if (lean_obj_tag(v_x_2357_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v___f_2356_);
v_a_2359_ = lean_ctor_get(v_x_2357_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_x_2357_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2361_ = v_x_2357_;
v_isShared_2362_ = v_isSharedCheck_2367_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v_x_2357_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2367_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
}
}
else
{
lean_object* v___x_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
lean_dec_ref_known(v_x_2357_, 1);
v___x_2368_ = lean_unsigned_to_nat(0u);
v___x_2369_ = 0;
v___x_2370_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_2355_);
v___x_2371_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2368_, v___x_2369_, v___x_2370_, v___f_2356_);
return v___x_2371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed(lean_object* v___y_2372_, lean_object* v___f_2373_, lean_object* v_x_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Std_Http_Body_Stream_tryRecvBody___lam__2(v___y_2372_, v___f_2373_, v_x_2374_);
lean_dec(v___y_2372_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3(lean_object* v___f_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___f_2380_; lean_object* v___f_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_inc_n(v___y_2378_, 2);
v___f_2380_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2380_, 0, v___y_2378_);
lean_closure_set(v___f_2380_, 1, v___f_2377_);
v___f_2381_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2381_, 0, v___y_2378_);
lean_closure_set(v___f_2381_, 1, v___f_2380_);
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = 0;
v___x_2384_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2378_);
v___x_2385_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2382_, v___x_2383_, v___x_2384_, v___f_2381_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed(lean_object* v___f_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Std_Http_Body_Stream_tryRecvBody___lam__3(v___f_2386_, v___y_2387_);
lean_dec(v___y_2387_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody(lean_object* v_stream_2393_){
_start:
{
lean_object* v___f_2395_; lean_object* v___x_2396_; 
v___f_2395_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_2396_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2393_, v___f_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___boxed(lean_object* v_stream_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_2397_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v_pendingProducer_2403_; lean_object* v_pendingConsumer_2404_; lean_object* v_interestWaiter_2405_; uint8_t v_closed_2406_; lean_object* v_knownSize_2407_; lean_object* v_pendingIncomplete_2408_; lean_object* v_closeError_2409_; uint8_t v_closeAfterProducer_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2437_; 
v___x_2402_ = lean_st_ref_get(v_a_2400_);
v_pendingProducer_2403_ = lean_ctor_get(v___x_2402_, 0);
v_pendingConsumer_2404_ = lean_ctor_get(v___x_2402_, 1);
v_interestWaiter_2405_ = lean_ctor_get(v___x_2402_, 2);
v_closed_2406_ = lean_ctor_get_uint8(v___x_2402_, sizeof(void*)*6);
v_knownSize_2407_ = lean_ctor_get(v___x_2402_, 3);
v_pendingIncomplete_2408_ = lean_ctor_get(v___x_2402_, 4);
v_closeError_2409_ = lean_ctor_get(v___x_2402_, 5);
v_closeAfterProducer_2410_ = lean_ctor_get_uint8(v___x_2402_, sizeof(void*)*6 + 1);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2412_ = v___x_2402_;
v_isShared_2413_ = v_isSharedCheck_2437_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_closeError_2409_);
lean_inc(v_pendingIncomplete_2408_);
lean_inc(v_knownSize_2407_);
lean_inc(v_interestWaiter_2405_);
lean_inc(v_pendingConsumer_2404_);
lean_inc(v_pendingProducer_2403_);
lean_dec(v___x_2402_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2437_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___y_2415_; lean_object* v_interestWaiter_2416_; lean_object* v___y_2417_; lean_object* v_pendingConsumer_2424_; lean_object* v___y_2425_; 
if (lean_obj_tag(v_pendingConsumer_2404_) == 1)
{
lean_object* v_val_2431_; 
v_val_2431_ = lean_ctor_get(v_pendingConsumer_2404_, 0);
if (lean_obj_tag(v_val_2431_) == 1)
{
lean_object* v_finished_2432_; lean_object* v_finished_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v_finished_2432_ = lean_ctor_get(v_val_2431_, 0);
v_finished_2433_ = lean_ctor_get(v_finished_2432_, 0);
v___x_2434_ = lean_st_ref_get(v_finished_2433_);
v___x_2435_ = lean_unbox(v___x_2434_);
lean_dec(v___x_2434_);
if (v___x_2435_ == 0)
{
v_pendingConsumer_2424_ = v_pendingConsumer_2404_;
v___y_2425_ = v_a_2400_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2436_; 
lean_dec_ref_known(v_pendingConsumer_2404_, 1);
v___x_2436_ = lean_box(0);
v_pendingConsumer_2424_ = v___x_2436_;
v___y_2425_ = v_a_2400_;
goto v___jp_2423_;
}
}
else
{
v_pendingConsumer_2424_ = v_pendingConsumer_2404_;
v___y_2425_ = v_a_2400_;
goto v___jp_2423_;
}
}
else
{
v_pendingConsumer_2424_ = v_pendingConsumer_2404_;
v___y_2425_ = v_a_2400_;
goto v___jp_2423_;
}
v___jp_2414_:
{
lean_object* v___x_2419_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 2, v_interestWaiter_2416_);
lean_ctor_set(v___x_2412_, 1, v___y_2415_);
v___x_2419_ = v___x_2412_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_pendingProducer_2403_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v___y_2415_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_interestWaiter_2416_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_knownSize_2407_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v_pendingIncomplete_2408_);
lean_ctor_set(v_reuseFailAlloc_2422_, 5, v_closeError_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2422_, sizeof(void*)*6, v_closed_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2422_, sizeof(void*)*6 + 1, v_closeAfterProducer_2410_);
v___x_2419_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_st_ref_swap(v___y_2417_, v___x_2419_);
lean_dec(v___x_2421_);
return v___x_2420_;
}
}
v___jp_2423_:
{
if (lean_obj_tag(v_interestWaiter_2405_) == 0)
{
v___y_2415_ = v_pendingConsumer_2424_;
v_interestWaiter_2416_ = v_interestWaiter_2405_;
v___y_2417_ = v___y_2425_;
goto v___jp_2414_;
}
else
{
lean_object* v_val_2426_; lean_object* v_finished_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v_val_2426_ = lean_ctor_get(v_interestWaiter_2405_, 0);
v_finished_2427_ = lean_ctor_get(v_val_2426_, 0);
v___x_2428_ = lean_st_ref_get(v_finished_2427_);
v___x_2429_ = lean_unbox(v___x_2428_);
lean_dec(v___x_2428_);
if (v___x_2429_ == 0)
{
v___y_2415_ = v_pendingConsumer_2424_;
v_interestWaiter_2416_ = v_interestWaiter_2405_;
v___y_2417_ = v___y_2425_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2430_; 
lean_dec_ref_known(v_interestWaiter_2405_, 1);
v___x_2430_ = lean_box(0);
v___y_2415_ = v_pendingConsumer_2424_;
v_interestWaiter_2416_ = v___x_2430_;
v___y_2417_ = v___y_2425_;
goto v___jp_2414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object* v_a_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_2438_);
lean_dec(v_a_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object* v_a_2441_){
_start:
{
lean_object* v___x_2443_; lean_object* v_interestWaiter_2444_; 
v___x_2443_ = lean_st_ref_get(v_a_2441_);
v_interestWaiter_2444_ = lean_ctor_get(v___x_2443_, 2);
lean_inc(v_interestWaiter_2444_);
if (lean_obj_tag(v_interestWaiter_2444_) == 1)
{
lean_object* v_pendingProducer_2445_; lean_object* v_pendingConsumer_2446_; uint8_t v_closed_2447_; lean_object* v_knownSize_2448_; lean_object* v_pendingIncomplete_2449_; lean_object* v_closeError_2450_; uint8_t v_closeAfterProducer_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2464_; 
v_pendingProducer_2445_ = lean_ctor_get(v___x_2443_, 0);
v_pendingConsumer_2446_ = lean_ctor_get(v___x_2443_, 1);
v_closed_2447_ = lean_ctor_get_uint8(v___x_2443_, sizeof(void*)*6);
v_knownSize_2448_ = lean_ctor_get(v___x_2443_, 3);
v_pendingIncomplete_2449_ = lean_ctor_get(v___x_2443_, 4);
v_closeError_2450_ = lean_ctor_get(v___x_2443_, 5);
v_closeAfterProducer_2451_ = lean_ctor_get_uint8(v___x_2443_, sizeof(void*)*6 + 1);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2443_, 2);
lean_dec(v_unused_2465_);
v___x_2453_ = v___x_2443_;
v_isShared_2454_ = v_isSharedCheck_2464_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_closeError_2450_);
lean_inc(v_pendingIncomplete_2449_);
lean_inc(v_knownSize_2448_);
lean_inc(v_pendingConsumer_2446_);
lean_inc(v_pendingProducer_2445_);
lean_dec(v___x_2443_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2464_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_val_2455_; uint8_t v___x_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2460_; 
v_val_2455_ = lean_ctor_get(v_interestWaiter_2444_, 0);
lean_inc(v_val_2455_);
lean_dec_ref_known(v_interestWaiter_2444_, 1);
v___x_2456_ = 1;
v___x_2457_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2455_, v___x_2456_);
lean_dec(v_val_2455_);
v___x_2458_ = lean_box(0);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 2, v___x_2458_);
v___x_2460_ = v___x_2453_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_pendingProducer_2445_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_pendingConsumer_2446_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_knownSize_2448_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_pendingIncomplete_2449_);
lean_ctor_set(v_reuseFailAlloc_2463_, 5, v_closeError_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2463_, sizeof(void*)*6, v_closed_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2463_, sizeof(void*)*6 + 1, v_closeAfterProducer_2451_);
v___x_2460_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_st_ref_swap(v_a_2441_, v___x_2460_);
lean_dec(v___x_2462_);
return v___x_2461_;
}
}
}
else
{
lean_object* v___x_2466_; 
lean_dec(v_interestWaiter_2444_);
lean_dec(v___x_2443_);
v___x_2466_ = lean_box(0);
return v___x_2466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object* v_a_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_2467_);
lean_dec(v_a_2467_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object* v_mutex_2470_, lean_object* v_k_2471_){
_start:
{
lean_object* v_ref_2473_; lean_object* v_mutex_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_ref_2473_ = lean_ctor_get(v_mutex_2470_, 0);
lean_inc(v_ref_2473_);
v_mutex_2474_ = lean_ctor_get(v_mutex_2470_, 1);
lean_inc(v_mutex_2474_);
lean_dec_ref(v_mutex_2470_);
v___x_2475_ = lean_io_basemutex_lock(v_mutex_2474_);
v___x_2476_ = lean_apply_2(v_k_2471_, v_ref_2473_, lean_box(0));
v___x_2477_ = lean_io_basemutex_unlock(v_mutex_2474_);
lean_dec(v_mutex_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object* v_mutex_2478_, lean_object* v_k_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_2478_, v_k_2479_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object* v_00_u03b1_2482_, lean_object* v_00_u03b2_2483_, lean_object* v_mutex_2484_, lean_object* v_k_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_2484_, v_k_2485_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object* v_00_u03b1_2488_, lean_object* v_00_u03b2_2489_, lean_object* v_mutex_2490_, lean_object* v_k_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(v_00_u03b1_2488_, v_00_u03b2_2489_, v_mutex_2490_, v_k_2491_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object* v_x_2499_){
_start:
{
if (lean_obj_tag(v_x_2499_) == 0)
{
lean_object* v___x_2500_; 
v___x_2500_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2));
return v___x_2500_;
}
else
{
lean_object* v_val_2501_; 
v_val_2501_ = lean_ctor_get(v_x_2499_, 0);
lean_inc(v_val_2501_);
return v_val_2501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___boxed(lean_object* v_x_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(v_x_2502_);
lean_dec(v_x_2502_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1(lean_object* v_a_2504_){
_start:
{
lean_object* v___x_2506_; uint8_t v_closed_2507_; 
v___x_2506_ = lean_st_ref_get(v_a_2504_);
v_closed_2507_ = lean_ctor_get_uint8(v___x_2506_, sizeof(void*)*6);
if (v_closed_2507_ == 0)
{
lean_object* v_pendingProducer_2508_; lean_object* v_pendingConsumer_2509_; lean_object* v_interestWaiter_2510_; lean_object* v_knownSize_2511_; lean_object* v_pendingIncomplete_2512_; lean_object* v_closeError_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2610_; 
v_pendingProducer_2508_ = lean_ctor_get(v___x_2506_, 0);
v_pendingConsumer_2509_ = lean_ctor_get(v___x_2506_, 1);
v_interestWaiter_2510_ = lean_ctor_get(v___x_2506_, 2);
v_knownSize_2511_ = lean_ctor_get(v___x_2506_, 3);
v_pendingIncomplete_2512_ = lean_ctor_get(v___x_2506_, 4);
v_closeError_2513_ = lean_ctor_get(v___x_2506_, 5);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2515_ = v___x_2506_;
v_isShared_2516_ = v_isSharedCheck_2610_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_closeError_2513_);
lean_inc(v_pendingIncomplete_2512_);
lean_inc(v_knownSize_2511_);
lean_inc(v_interestWaiter_2510_);
lean_inc(v_pendingConsumer_2509_);
lean_inc(v_pendingProducer_2508_);
lean_dec(v___x_2506_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2610_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
uint8_t v___x_2517_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v_leftover_2553_; lean_object* v_knownSize_2554_; lean_object* v___y_2555_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2564_; 
v___x_2517_ = 1;
if (lean_obj_tag(v_pendingProducer_2508_) == 0)
{
if (lean_obj_tag(v_pendingIncomplete_2512_) == 0)
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_box(0);
v___y_2564_ = v___x_2594_;
goto v___jp_2563_;
}
else
{
lean_object* v_val_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2608_; 
v_val_2595_ = lean_ctor_get(v_pendingIncomplete_2512_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_pendingIncomplete_2512_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2597_ = v_pendingIncomplete_2512_;
v_isShared_2598_ = v_isSharedCheck_2608_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_val_2595_);
lean_dec(v_pendingIncomplete_2512_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2608_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v_data_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2599_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(v_val_2595_);
v_data_2600_ = lean_ctor_get(v___x_2599_, 0);
v___x_2601_ = lean_unsigned_to_nat(0u);
v___x_2602_ = lean_byte_array_size(v_data_2600_);
v___x_2603_ = lean_nat_dec_lt(v___x_2601_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; 
lean_dec_ref(v___x_2599_);
lean_del_object(v___x_2597_);
v___x_2604_ = lean_box(0);
v___y_2564_ = v___x_2604_;
goto v___jp_2563_;
}
else
{
lean_object* v___x_2606_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2599_);
v___x_2606_ = v___x_2597_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2599_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
v___y_2564_ = v___x_2606_;
goto v___jp_2563_;
}
}
}
}
}
else
{
lean_object* v___x_2609_; 
lean_dec(v_pendingIncomplete_2512_);
v___x_2609_ = lean_box(0);
v___y_2564_ = v___x_2609_;
goto v___jp_2563_;
}
v___jp_2518_:
{
if (lean_obj_tag(v___y_2519_) == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = lean_box(0);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 4, v___x_2522_);
lean_ctor_set(v___x_2515_, 3, v___y_2520_);
lean_ctor_set(v___x_2515_, 2, v___x_2522_);
lean_ctor_set(v___x_2515_, 1, v___x_2522_);
lean_ctor_set(v___x_2515_, 0, v___x_2522_);
v___x_2524_ = v___x_2515_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2527_, 3, v___y_2520_);
lean_ctor_set(v_reuseFailAlloc_2527_, 4, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2527_, 5, v_closeError_2513_);
v___x_2524_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_ctor_set_uint8(v___x_2524_, sizeof(void*)*6, v___x_2517_);
lean_ctor_set_uint8(v___x_2524_, sizeof(void*)*6 + 1, v_closed_2507_);
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_st_ref_swap(v___y_2521_, v___x_2524_);
lean_dec(v___x_2526_);
return v___x_2525_;
}
}
else
{
lean_object* v_val_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2543_; 
v_val_2528_ = lean_ctor_get(v___y_2519_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___y_2519_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2530_ = v___y_2519_;
v_isShared_2531_ = v_isSharedCheck_2543_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_val_2528_);
lean_dec(v___y_2519_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2543_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = lean_io_promise_new();
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v_val_2528_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2533_);
v___x_2535_ = v___x_2530_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
v___x_2536_ = lean_box(0);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 4, v___x_2536_);
lean_ctor_set(v___x_2515_, 3, v___y_2520_);
lean_ctor_set(v___x_2515_, 2, v___x_2536_);
lean_ctor_set(v___x_2515_, 1, v___x_2536_);
lean_ctor_set(v___x_2515_, 0, v___x_2535_);
v___x_2538_ = v___x_2515_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2541_, 3, v___y_2520_);
lean_ctor_set(v_reuseFailAlloc_2541_, 4, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2541_, 5, v_closeError_2513_);
v___x_2538_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*6, v___x_2517_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*6 + 1, v_closed_2507_);
v___x_2539_ = lean_box(0);
v___x_2540_ = lean_st_ref_swap(v___y_2521_, v___x_2538_);
lean_dec(v___x_2540_);
return v___x_2539_;
}
}
}
}
}
v___jp_2544_:
{
if (lean_obj_tag(v_pendingProducer_2508_) == 1)
{
lean_object* v_val_2548_; lean_object* v_done_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_val_2548_ = lean_ctor_get(v_pendingProducer_2508_, 0);
lean_inc(v_val_2548_);
lean_dec_ref_known(v_pendingProducer_2508_, 1);
v_done_2549_ = lean_ctor_get(v_val_2548_, 1);
lean_inc(v_done_2549_);
lean_dec(v_val_2548_);
v___x_2550_ = lean_box(v_closed_2507_);
v___x_2551_ = lean_io_promise_resolve(v___x_2550_, v_done_2549_);
lean_dec(v_done_2549_);
v___y_2519_ = v___y_2545_;
v___y_2520_ = v___y_2546_;
v___y_2521_ = v___y_2547_;
goto v___jp_2518_;
}
else
{
lean_dec(v_pendingProducer_2508_);
v___y_2519_ = v___y_2545_;
v___y_2520_ = v___y_2546_;
v___y_2521_ = v___y_2547_;
goto v___jp_2518_;
}
}
v___jp_2552_:
{
if (lean_obj_tag(v_interestWaiter_2510_) == 1)
{
lean_object* v_val_2556_; uint8_t v___x_2557_; 
v_val_2556_ = lean_ctor_get(v_interestWaiter_2510_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v_interestWaiter_2510_, 1);
v___x_2557_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2556_, v_closed_2507_);
lean_dec(v_val_2556_);
v___y_2545_ = v_leftover_2553_;
v___y_2546_ = v_knownSize_2554_;
v___y_2547_ = v___y_2555_;
goto v___jp_2544_;
}
else
{
lean_dec(v_interestWaiter_2510_);
v___y_2545_ = v_leftover_2553_;
v___y_2546_ = v_knownSize_2554_;
v___y_2547_ = v___y_2555_;
goto v___jp_2544_;
}
}
v___jp_2558_:
{
uint8_t v___x_2562_; 
v___x_2562_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v___y_2560_, v___y_2561_);
lean_dec_ref(v___y_2560_);
v_leftover_2553_ = v___y_2559_;
v_knownSize_2554_ = v_knownSize_2511_;
v___y_2555_ = v_a_2504_;
goto v___jp_2552_;
}
v___jp_2563_:
{
if (lean_obj_tag(v_pendingConsumer_2509_) == 1)
{
if (lean_obj_tag(v___y_2564_) == 0)
{
if (lean_obj_tag(v_closeError_2513_) == 0)
{
lean_object* v_val_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_val_2565_ = lean_ctor_get(v_pendingConsumer_2509_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_pendingConsumer_2509_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v_pendingConsumer_2509_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_val_2565_);
lean_dec(v_pendingConsumer_2509_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___y_2564_);
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___y_2564_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
v___y_2559_ = v___y_2564_;
v___y_2560_ = v_val_2565_;
v___y_2561_ = v___x_2570_;
goto v___jp_2558_;
}
}
}
else
{
lean_object* v_val_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2581_; 
v_val_2573_ = lean_ctor_get(v_pendingConsumer_2509_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_pendingConsumer_2509_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2575_ = v_pendingConsumer_2509_;
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_val_2573_);
lean_dec(v_pendingConsumer_2509_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v_val_2577_; lean_object* v___x_2579_; 
v_val_2577_ = lean_ctor_get(v_closeError_2513_, 0);
lean_inc(v_val_2577_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set_tag(v___x_2575_, 0);
lean_ctor_set(v___x_2575_, 0, v_val_2577_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_val_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
v___y_2559_ = v___y_2564_;
v___y_2560_ = v_val_2573_;
v___y_2561_ = v___x_2579_;
goto v___jp_2558_;
}
}
}
}
else
{
lean_object* v_val_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2593_; 
v_val_2582_ = lean_ctor_get(v_pendingConsumer_2509_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_pendingConsumer_2509_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2584_ = v_pendingConsumer_2509_;
v_isShared_2585_ = v_isSharedCheck_2593_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_val_2582_);
lean_dec(v_pendingConsumer_2509_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2593_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v_val_2586_; lean_object* v___x_2588_; 
v_val_2586_ = lean_ctor_get(v___y_2564_, 0);
lean_inc_ref(v___y_2564_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___y_2564_);
v___x_2588_ = v___x_2584_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___y_2564_);
v___x_2588_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
uint8_t v___x_2589_; 
v___x_2589_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_2582_, v___x_2588_);
lean_dec(v_val_2582_);
if (v___x_2589_ == 0)
{
v_leftover_2553_ = v___y_2564_;
v_knownSize_2554_ = v_knownSize_2511_;
v___y_2555_ = v_a_2504_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_inc(v_val_2586_);
lean_dec_ref_known(v___y_2564_, 1);
v___x_2590_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_2511_, v_val_2586_);
lean_dec(v_val_2586_);
v___x_2591_ = lean_box(0);
v_leftover_2553_ = v___x_2591_;
v_knownSize_2554_ = v___x_2590_;
v___y_2555_ = v_a_2504_;
goto v___jp_2552_;
}
}
}
}
}
else
{
lean_dec(v_pendingConsumer_2509_);
v_leftover_2553_ = v___y_2564_;
v_knownSize_2554_ = v_knownSize_2511_;
v___y_2555_ = v_a_2504_;
goto v___jp_2552_;
}
}
}
}
else
{
lean_object* v___x_2611_; 
lean_dec(v___x_2506_);
v___x_2611_ = lean_box(0);
return v___x_2611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1___boxed(lean_object* v_a_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1(v_a_2612_);
lean_dec(v_a_2612_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object* v_a_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v_pendingProducer_2618_; 
v___x_2617_ = lean_st_ref_get(v_a_2615_);
v_pendingProducer_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_pendingProducer_2618_);
if (lean_obj_tag(v_pendingProducer_2618_) == 1)
{
lean_object* v_val_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2652_; 
v_val_2619_ = lean_ctor_get(v_pendingProducer_2618_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_pendingProducer_2618_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2621_ = v_pendingProducer_2618_;
v_isShared_2622_ = v_isSharedCheck_2652_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_val_2619_);
lean_dec(v_pendingProducer_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2652_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v_pendingConsumer_2623_; lean_object* v_interestWaiter_2624_; uint8_t v_closed_2625_; lean_object* v_knownSize_2626_; lean_object* v_pendingIncomplete_2627_; lean_object* v_closeError_2628_; uint8_t v_closeAfterProducer_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2650_; 
v_pendingConsumer_2623_ = lean_ctor_get(v___x_2617_, 1);
v_interestWaiter_2624_ = lean_ctor_get(v___x_2617_, 2);
v_closed_2625_ = lean_ctor_get_uint8(v___x_2617_, sizeof(void*)*6);
v_knownSize_2626_ = lean_ctor_get(v___x_2617_, 3);
v_pendingIncomplete_2627_ = lean_ctor_get(v___x_2617_, 4);
v_closeError_2628_ = lean_ctor_get(v___x_2617_, 5);
v_closeAfterProducer_2629_ = lean_ctor_get_uint8(v___x_2617_, sizeof(void*)*6 + 1);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v___x_2617_, 0);
lean_dec(v_unused_2651_);
v___x_2631_ = v___x_2617_;
v_isShared_2632_ = v_isSharedCheck_2650_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_closeError_2628_);
lean_inc(v_pendingIncomplete_2627_);
lean_inc(v_knownSize_2626_);
lean_inc(v_interestWaiter_2624_);
lean_inc(v_pendingConsumer_2623_);
lean_dec(v___x_2617_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2650_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_chunk_2633_; lean_object* v_done_2634_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2643_; 
v_chunk_2633_ = lean_ctor_get(v_val_2619_, 0);
lean_inc_ref(v_chunk_2633_);
v_done_2634_ = lean_ctor_get(v_val_2619_, 1);
lean_inc(v_done_2634_);
lean_dec(v_val_2619_);
v___x_2639_ = lean_box(0);
v___x_2640_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_2626_, v_chunk_2633_);
v___x_2641_ = 0;
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 3, v___x_2640_);
lean_ctor_set(v___x_2631_, 0, v___x_2639_);
v___x_2643_ = v___x_2631_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_pendingConsumer_2623_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_interestWaiter_2624_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_pendingIncomplete_2627_);
lean_ctor_set(v_reuseFailAlloc_2649_, 5, v_closeError_2628_);
lean_ctor_set_uint8(v_reuseFailAlloc_2649_, sizeof(void*)*6, v_closed_2625_);
v___x_2643_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2642_;
}
v___jp_2635_:
{
lean_object* v___x_2637_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v_chunk_2633_);
v___x_2637_ = v___x_2621_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_chunk_2633_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
v_reusejp_2642_:
{
lean_object* v___x_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*6 + 1, v___x_2641_);
v___x_2644_ = lean_st_ref_swap(v_a_2615_, v___x_2643_);
lean_dec(v___x_2644_);
v___x_2645_ = 1;
v___x_2646_ = lean_box(v___x_2645_);
v___x_2647_ = lean_io_promise_resolve(v___x_2646_, v_done_2634_);
lean_dec(v_done_2634_);
if (v_closeAfterProducer_2629_ == 0)
{
goto v___jp_2635_;
}
else
{
lean_object* v___x_2648_; 
v___x_2648_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1(v_a_2615_);
goto v___jp_2635_;
}
}
}
}
}
else
{
lean_object* v___x_2653_; 
lean_dec(v_pendingProducer_2618_);
lean_dec(v___x_2617_);
v___x_2653_ = lean_box(0);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object* v_a_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_2654_);
lean_dec(v_a_2654_);
return v_res_2656_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2));
v___x_2663_ = lean_task_pure(v___x_2662_);
return v___x_2663_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_2665_ = lean_task_pure(v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object* v___f_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_2667_);
v___x_2670_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_2667_);
if (lean_obj_tag(v___x_2670_) == 1)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_dec_ref(v___f_2666_);
v___x_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
v___x_2672_ = lean_task_pure(v___x_2671_);
return v___x_2672_;
}
else
{
lean_object* v___x_2673_; uint8_t v_closed_2674_; 
lean_dec(v___x_2670_);
v___x_2673_ = lean_st_ref_get(v___y_2667_);
v_closed_2674_ = lean_ctor_get_uint8(v___x_2673_, sizeof(void*)*6);
if (v_closed_2674_ == 0)
{
uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v_pendingConsumer_2677_; 
lean_dec(v___x_2673_);
v___x_2675_ = 1;
v___x_2676_ = lean_st_ref_get(v___y_2667_);
v_pendingConsumer_2677_ = lean_ctor_get(v___x_2676_, 1);
if (lean_obj_tag(v_pendingConsumer_2677_) == 0)
{
lean_object* v_pendingProducer_2678_; lean_object* v_interestWaiter_2679_; uint8_t v_closed_2680_; lean_object* v_knownSize_2681_; lean_object* v_pendingIncomplete_2682_; lean_object* v_closeError_2683_; uint8_t v_closeAfterProducer_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2699_; 
v_pendingProducer_2678_ = lean_ctor_get(v___x_2676_, 0);
v_interestWaiter_2679_ = lean_ctor_get(v___x_2676_, 2);
v_closed_2680_ = lean_ctor_get_uint8(v___x_2676_, sizeof(void*)*6);
v_knownSize_2681_ = lean_ctor_get(v___x_2676_, 3);
v_pendingIncomplete_2682_ = lean_ctor_get(v___x_2676_, 4);
v_closeError_2683_ = lean_ctor_get(v___x_2676_, 5);
v_closeAfterProducer_2684_ = lean_ctor_get_uint8(v___x_2676_, sizeof(void*)*6 + 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2676_, 1);
lean_dec(v_unused_2700_);
v___x_2686_ = v___x_2676_;
v_isShared_2687_ = v_isSharedCheck_2699_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_closeError_2683_);
lean_inc(v_pendingIncomplete_2682_);
lean_inc(v_knownSize_2681_);
lean_inc(v_interestWaiter_2679_);
lean_inc(v_pendingProducer_2678_);
lean_dec(v___x_2676_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2699_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2688_ = lean_io_promise_new();
lean_inc(v___x_2688_);
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
v___x_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 1, v___x_2690_);
v___x_2692_ = v___x_2686_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_pendingProducer_2678_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_interestWaiter_2679_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_knownSize_2681_);
lean_ctor_set(v_reuseFailAlloc_2698_, 4, v_pendingIncomplete_2682_);
lean_ctor_set(v_reuseFailAlloc_2698_, 5, v_closeError_2683_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*6, v_closed_2680_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*6 + 1, v_closeAfterProducer_2684_);
v___x_2692_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2693_ = lean_st_ref_swap(v___y_2667_, v___x_2692_);
lean_dec(v___x_2693_);
v___x_2694_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_2667_);
v___x_2695_ = lean_io_promise_result_opt(v___x_2688_);
lean_dec(v___x_2688_);
v___x_2696_ = lean_unsigned_to_nat(0u);
v___x_2697_ = lean_task_map(v___f_2666_, v___x_2695_, v___x_2696_, v___x_2675_);
return v___x_2697_;
}
}
}
else
{
lean_object* v___x_2701_; 
lean_dec(v___x_2676_);
lean_dec_ref(v___f_2666_);
v___x_2701_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3);
return v___x_2701_;
}
}
else
{
lean_object* v_closeError_2702_; 
lean_dec_ref(v___f_2666_);
v_closeError_2702_ = lean_ctor_get(v___x_2673_, 5);
lean_inc(v_closeError_2702_);
lean_dec(v___x_2673_);
if (lean_obj_tag(v_closeError_2702_) == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4);
return v___x_2703_;
}
else
{
lean_object* v_val_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2712_; 
v_val_2704_ = lean_ctor_get(v_closeError_2702_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_closeError_2702_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2706_ = v_closeError_2702_;
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_val_2704_);
lean_dec(v_closeError_2702_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 0);
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_val_2704_);
v___x_2709_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_task_pure(v___x_2709_);
return v___x_2710_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object* v___f_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(v___f_2713_, v___y_2714_);
lean_dec(v___y_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object* v_stream_2720_){
_start:
{
lean_object* v___f_2722_; lean_object* v___x_2723_; 
v___f_2722_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1));
v___x_2723_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_2720_, v___f_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object* v_stream_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_2724_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object* v_x_2727_){
_start:
{
if (lean_obj_tag(v_x_2727_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2737_; 
v_a_2729_ = lean_ctor_get(v_x_2727_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_x_2727_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2731_ = v_x_2727_;
v_isShared_2732_ = v_isSharedCheck_2737_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v_x_2727_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2737_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2739_; 
v_a_2738_ = lean_ctor_get(v_x_2727_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v_x_2727_, 1);
v___x_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2739_, 0, v_a_2738_);
return v___x_2739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object* v_x_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv(lean_object* v_stream_2744_){
_start:
{
lean_object* v___f_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___f_2746_ = ((lean_object*)(l_Std_Http_Body_Stream_recv___closed__0));
v___x_2747_ = lean_unsigned_to_nat(0u);
v___x_2748_ = 0;
v___x_2749_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_2744_);
v___x_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
v___x_2752_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2747_, v___x_2748_, v___x_2751_, v___f_2746_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object* v_stream_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Std_Http_Body_Stream_recv(v_stream_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close(lean_object* v_stream_2757_){
_start:
{
lean_object* v___f_2759_; lean_object* v___x_2760_; 
v___f_2759_ = ((lean_object*)(l_Std_Http_Body_Stream_close___closed__0));
v___x_2760_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2757_, v___f_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object* v_stream_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Std_Http_Body_Stream_close(v_stream_2761_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(uint8_t v___x_2764_, lean_object* v_x_2765_){
_start:
{
if (lean_obj_tag(v_x_2765_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2775_; 
v_a_2767_ = lean_ctor_get(v_x_2765_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_x_2765_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2769_ = v_x_2765_;
v_isShared_2770_ = v_isSharedCheck_2775_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v_x_2765_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2775_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
return v___x_2773_;
}
}
}
else
{
lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2784_; 
v_isSharedCheck_2784_ = !lean_is_exclusive(v_x_2765_);
if (v_isSharedCheck_2784_ == 0)
{
lean_object* v_unused_2785_; 
v_unused_2785_ = lean_ctor_get(v_x_2765_, 0);
lean_dec(v_unused_2785_);
v___x_2777_ = v_x_2765_;
v_isShared_2778_ = v_isSharedCheck_2784_;
goto v_resetjp_2776_;
}
else
{
lean_dec(v_x_2765_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2784_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = lean_box(v___x_2764_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2779_);
v___x_2781_ = v___x_2777_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
return v___x_2782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0___boxed(lean_object* v___x_2786_, lean_object* v_x_2787_, lean_object* v___y_2788_){
_start:
{
uint8_t v___x_1415__boxed_2789_; lean_object* v_res_2790_; 
v___x_1415__boxed_2789_ = lean_unbox(v___x_2786_);
v_res_2790_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(v___x_1415__boxed_2789_, v_x_2787_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(lean_object* v___y_2794_, lean_object* v_x_2795_){
_start:
{
uint8_t v___y_2798_; 
if (lean_obj_tag(v_x_2795_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2810_; 
v_a_2802_ = lean_ctor_get(v_x_2795_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_x_2795_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2804_ = v_x_2795_;
v_isShared_2805_ = v_isSharedCheck_2810_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v_x_2795_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2810_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2811_; uint8_t v_closed_2812_; 
v_a_2811_ = lean_ctor_get(v_x_2795_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v_x_2795_, 1);
v_closed_2812_ = lean_ctor_get_uint8(v_a_2811_, sizeof(void*)*6);
if (v_closed_2812_ == 0)
{
lean_object* v_pendingConsumer_2813_; 
v_pendingConsumer_2813_ = lean_ctor_get(v_a_2811_, 1);
lean_inc(v_pendingConsumer_2813_);
lean_dec(v_a_2811_);
if (lean_obj_tag(v_pendingConsumer_2813_) == 0)
{
lean_object* v___f_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___f_2814_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0));
v___x_2815_ = lean_unsigned_to_nat(0u);
v___x_2816_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___y_2794_);
v___x_2817_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2815_, v_closed_2812_, v___x_2816_, v___f_2814_);
return v___x_2817_;
}
else
{
lean_dec_ref_known(v_pendingConsumer_2813_, 1);
v___y_2798_ = v_closed_2812_;
goto v___jp_2797_;
}
}
else
{
uint8_t v___x_2818_; 
lean_dec(v_a_2811_);
v___x_2818_ = 0;
v___y_2798_ = v___x_2818_;
goto v___jp_2797_;
}
}
v___jp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_box(v___y_2798_);
v___x_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed(lean_object* v___y_2819_, lean_object* v_x_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(v___y_2819_, v_x_2820_);
lean_dec(v___y_2819_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(lean_object* v___y_2823_, lean_object* v___f_2824_, lean_object* v_x_2825_){
_start:
{
if (lean_obj_tag(v_x_2825_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref(v___f_2824_);
v_a_2827_ = lean_ctor_get(v_x_2825_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2829_ = v_x_2825_;
v_isShared_2830_ = v_isSharedCheck_2835_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v_x_2825_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2835_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; 
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
}
else
{
lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2847_; 
v_isSharedCheck_2847_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v_x_2825_, 0);
lean_dec(v_unused_2848_);
v___x_2837_ = v_x_2825_;
v_isShared_2838_ = v_isSharedCheck_2847_;
goto v_resetjp_2836_;
}
else
{
lean_dec(v_x_2825_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2847_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; uint8_t v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = 0;
v___x_2841_ = lean_st_ref_get(v___y_2823_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2841_);
v___x_2843_ = v___x_2837_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
v___x_2845_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2839_, v___x_2840_, v___x_2844_, v___f_2824_);
return v___x_2845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed(lean_object* v___y_2849_, lean_object* v___f_2850_, lean_object* v_x_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(v___y_2849_, v___f_2850_, v_x_2851_);
lean_dec(v___y_2849_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(lean_object* v___y_2854_){
_start:
{
lean_object* v___f_2856_; lean_object* v___f_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_inc_n(v___y_2854_, 2);
v___f_2856_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2856_, 0, v___y_2854_);
v___f_2857_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2857_, 0, v___y_2854_);
lean_closure_set(v___f_2857_, 1, v___f_2856_);
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = 0;
v___x_2860_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2854_);
v___x_2861_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2858_, v___x_2859_, v___x_2860_, v___f_2857_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3___boxed(lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(v___y_2862_);
lean_dec(v___y_2862_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned(lean_object* v_stream_2866_){
_start:
{
lean_object* v___f_2868_; lean_object* v___x_2869_; 
v___f_2868_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___closed__0));
v___x_2869_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2866_, v___f_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___boxed(lean_object* v_stream_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Std_Http_Body_Stream_closeIfAbandoned(v_stream_2870_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0(lean_object* v___y_2873_, lean_object* v_x_2874_){
_start:
{
if (lean_obj_tag(v_x_2874_) == 0)
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_x_2874_);
return v___x_2876_;
}
else
{
lean_object* v___x_2877_; 
lean_dec_ref_known(v_x_2874_, 1);
v___x_2877_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___y_2873_);
return v___x_2877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0___boxed(lean_object* v___y_2878_, lean_object* v_x_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Std_Http_Body_Stream_closeWithError___lam__0(v___y_2878_, v_x_2879_);
lean_dec(v___y_2878_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1(lean_object* v_err_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___f_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v_fst_2890_; lean_object* v_snd_2891_; lean_object* v_pendingProducer_2896_; lean_object* v_pendingConsumer_2897_; lean_object* v_interestWaiter_2898_; uint8_t v_closed_2899_; lean_object* v_knownSize_2900_; lean_object* v_pendingIncomplete_2901_; lean_object* v_closeError_2902_; uint8_t v_closeAfterProducer_2903_; lean_object* v___x_2904_; 
lean_inc(v___y_2883_);
v___f_2885_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2885_, 0, v___y_2883_);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = 0;
v___x_2888_ = lean_st_ref_take(v___y_2883_);
v_pendingProducer_2896_ = lean_ctor_get(v___x_2888_, 0);
v_pendingConsumer_2897_ = lean_ctor_get(v___x_2888_, 1);
v_interestWaiter_2898_ = lean_ctor_get(v___x_2888_, 2);
v_closed_2899_ = lean_ctor_get_uint8(v___x_2888_, sizeof(void*)*6);
v_knownSize_2900_ = lean_ctor_get(v___x_2888_, 3);
v_pendingIncomplete_2901_ = lean_ctor_get(v___x_2888_, 4);
v_closeError_2902_ = lean_ctor_get(v___x_2888_, 5);
v_closeAfterProducer_2903_ = lean_ctor_get_uint8(v___x_2888_, sizeof(void*)*6 + 1);
v___x_2904_ = lean_box(0);
if (lean_obj_tag(v_closeError_2902_) == 0)
{
lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2912_; 
lean_inc(v_pendingIncomplete_2901_);
lean_inc(v_knownSize_2900_);
lean_inc(v_interestWaiter_2898_);
lean_inc(v_pendingConsumer_2897_);
lean_inc(v_pendingProducer_2896_);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; lean_object* v_unused_2914_; lean_object* v_unused_2915_; lean_object* v_unused_2916_; lean_object* v_unused_2917_; lean_object* v_unused_2918_; 
v_unused_2913_ = lean_ctor_get(v___x_2888_, 5);
lean_dec(v_unused_2913_);
v_unused_2914_ = lean_ctor_get(v___x_2888_, 4);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v___x_2888_, 3);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v___x_2888_, 2);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v___x_2888_, 1);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v___x_2888_, 0);
lean_dec(v_unused_2918_);
v___x_2906_ = v___x_2888_;
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
else
{
lean_dec(v___x_2888_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2908_, 0, v_err_2882_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 5, v___x_2908_);
v___x_2910_ = v___x_2906_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_pendingProducer_2896_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_pendingConsumer_2897_);
lean_ctor_set(v_reuseFailAlloc_2911_, 2, v_interestWaiter_2898_);
lean_ctor_set(v_reuseFailAlloc_2911_, 3, v_knownSize_2900_);
lean_ctor_set(v_reuseFailAlloc_2911_, 4, v_pendingIncomplete_2901_);
lean_ctor_set(v_reuseFailAlloc_2911_, 5, v___x_2908_);
lean_ctor_set_uint8(v_reuseFailAlloc_2911_, sizeof(void*)*6, v_closed_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2911_, sizeof(void*)*6 + 1, v_closeAfterProducer_2903_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
v_fst_2890_ = v___x_2904_;
v_snd_2891_ = v___x_2910_;
goto v___jp_2889_;
}
}
}
else
{
lean_dec(v_err_2882_);
v_fst_2890_ = v___x_2904_;
v_snd_2891_ = v___x_2888_;
goto v___jp_2889_;
}
v___jp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2892_ = lean_st_ref_put(v___y_2883_, v_snd_2891_);
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_fst_2890_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
v___x_2895_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2886_, v___x_2887_, v___x_2894_, v___f_2885_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1___boxed(lean_object* v_err_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Std_Http_Body_Stream_closeWithError___lam__1(v_err_2919_, v___y_2920_);
lean_dec(v___y_2920_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError(lean_object* v_stream_2923_, lean_object* v_err_2924_){
_start:
{
lean_object* v___f_2926_; lean_object* v___x_2927_; 
v___f_2926_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2926_, 0, v_err_2924_);
v___x_2927_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2923_, v___f_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___boxed(lean_object* v_stream_2928_, lean_object* v_err_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Std_Http_Body_Stream_closeWithError(v_stream_2928_, v_err_2929_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object* v_____do__lift_2932_, lean_object* v___y_2933_){
_start:
{
uint8_t v_closed_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_closed_2935_ = lean_ctor_get_uint8(v_____do__lift_2932_, sizeof(void*)*6);
v___x_2936_ = lean_box(v_closed_2935_);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object* v_____do__lift_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v_____do__lift_2939_);
return v_res_2942_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__1(void){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_2944_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__2(void){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_2945_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__6(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___f_2952_; lean_object* v___f_2953_; 
v___x_2951_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2952_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___f_2953_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2953_, 0, v___f_2952_);
lean_closure_set(v___f_2953_, 1, v___x_2951_);
return v___f_2953_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__11(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___f_2963_; lean_object* v___f_2964_; 
v___x_2962_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2963_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__10));
v___f_2964_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2964_, 0, v___f_2963_);
lean_closure_set(v___f_2964_, 1, v___x_2962_);
return v___f_2964_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__12(void){
_start:
{
lean_object* v___f_2965_; lean_object* v___x_2966_; 
v___f_2965_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__11, &l_Std_Http_Body_Stream_isClosed___closed__11_once, _init_l_Std_Http_Body_Stream_isClosed___closed__11);
v___x_2966_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2966_, 0, lean_box(0));
lean_closure_set(v___x_2966_, 1, lean_box(0));
lean_closure_set(v___x_2966_, 2, lean_box(0));
lean_closure_set(v___x_2966_, 3, v___f_2965_);
return v___x_2966_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__13(void){
_start:
{
lean_object* v___f_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___f_2967_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__0));
v___x_2968_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2969_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2970_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2970_, 0, lean_box(0));
lean_closure_set(v___x_2970_, 1, lean_box(0));
lean_closure_set(v___x_2970_, 2, v___x_2969_);
lean_closure_set(v___x_2970_, 3, lean_box(0));
lean_closure_set(v___x_2970_, 4, lean_box(0));
lean_closure_set(v___x_2970_, 5, v___x_2968_);
lean_closure_set(v___x_2970_, 6, v___f_2967_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed(lean_object* v_stream_2971_){
_start:
{
lean_object* v___x_2973_; lean_object* v___f_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___x_214__overap_2977_; lean_object* v___x_2978_; 
v___x_2973_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2974_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2975_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2976_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__13, &l_Std_Http_Body_Stream_isClosed___closed__13_once, _init_l_Std_Http_Body_Stream_isClosed___closed__13);
v___x_214__overap_2977_ = l_Std_Mutex_atomically___redArg(v___x_2973_, v___f_2974_, v___f_2975_, v_stream_2971_, v___x_2976_);
v___x_2978_ = lean_apply_1(v___x_214__overap_2977_, lean_box(0));
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___boxed(lean_object* v_stream_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Std_Http_Body_Stream_isClosed(v_stream_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0(lean_object* v_____do__lift_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_knownSize_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_knownSize_2985_ = lean_ctor_get(v_____do__lift_2982_, 3);
lean_inc(v_knownSize_2985_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_knownSize_2985_);
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(lean_object* v_____do__lift_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v_____do__lift_2988_);
return v_res_2991_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_getKnownSize___closed__1(void){
_start:
{
lean_object* v___f_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___f_2993_ = ((lean_object*)(l_Std_Http_Body_Stream_getKnownSize___closed__0));
v___x_2994_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2995_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2996_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2996_, 0, lean_box(0));
lean_closure_set(v___x_2996_, 1, lean_box(0));
lean_closure_set(v___x_2996_, 2, v___x_2995_);
lean_closure_set(v___x_2996_, 3, lean_box(0));
lean_closure_set(v___x_2996_, 4, lean_box(0));
lean_closure_set(v___x_2996_, 5, v___x_2994_);
lean_closure_set(v___x_2996_, 6, v___f_2993_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize(lean_object* v_stream_2997_){
_start:
{
lean_object* v___x_2999_; lean_object* v___f_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; lean_object* v___x_214__overap_3003_; lean_object* v___x_3004_; 
v___x_2999_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_3000_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_3001_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_3002_ = lean_obj_once(&l_Std_Http_Body_Stream_getKnownSize___closed__1, &l_Std_Http_Body_Stream_getKnownSize___closed__1_once, _init_l_Std_Http_Body_Stream_getKnownSize___closed__1);
v___x_214__overap_3003_ = l_Std_Mutex_atomically___redArg(v___x_2999_, v___f_3000_, v___f_3001_, v_stream_2997_, v___x_3002_);
v___x_3004_ = lean_apply_1(v___x_214__overap_3003_, lean_box(0));
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___boxed(lean_object* v_stream_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0(lean_object* v_size_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; lean_object* v_pendingProducer_3012_; lean_object* v_pendingConsumer_3013_; lean_object* v_interestWaiter_3014_; uint8_t v_closed_3015_; lean_object* v_pendingIncomplete_3016_; lean_object* v_closeError_3017_; uint8_t v_closeAfterProducer_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3027_; 
v___x_3011_ = lean_st_ref_take(v___y_3009_);
v_pendingProducer_3012_ = lean_ctor_get(v___x_3011_, 0);
v_pendingConsumer_3013_ = lean_ctor_get(v___x_3011_, 1);
v_interestWaiter_3014_ = lean_ctor_get(v___x_3011_, 2);
v_closed_3015_ = lean_ctor_get_uint8(v___x_3011_, sizeof(void*)*6);
v_pendingIncomplete_3016_ = lean_ctor_get(v___x_3011_, 4);
v_closeError_3017_ = lean_ctor_get(v___x_3011_, 5);
v_closeAfterProducer_3018_ = lean_ctor_get_uint8(v___x_3011_, sizeof(void*)*6 + 1);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; 
v_unused_3028_ = lean_ctor_get(v___x_3011_, 3);
lean_dec(v_unused_3028_);
v___x_3020_ = v___x_3011_;
v_isShared_3021_ = v_isSharedCheck_3027_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_closeError_3017_);
lean_inc(v_pendingIncomplete_3016_);
lean_inc(v_interestWaiter_3014_);
lean_inc(v_pendingConsumer_3013_);
lean_inc(v_pendingProducer_3012_);
lean_dec(v___x_3011_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3027_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 3, v_size_3008_);
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_pendingProducer_3012_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_pendingConsumer_3013_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v_interestWaiter_3014_);
lean_ctor_set(v_reuseFailAlloc_3026_, 3, v_size_3008_);
lean_ctor_set(v_reuseFailAlloc_3026_, 4, v_pendingIncomplete_3016_);
lean_ctor_set(v_reuseFailAlloc_3026_, 5, v_closeError_3017_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, sizeof(void*)*6, v_closed_3015_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, sizeof(void*)*6 + 1, v_closeAfterProducer_3018_);
v___x_3023_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = lean_st_ref_put(v___y_3009_, v___x_3023_);
v___x_3025_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(lean_object* v_size_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_3029_, v___y_3030_);
lean_dec(v___y_3030_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize(lean_object* v_stream_3033_, lean_object* v_size_3034_){
_start:
{
lean_object* v___f_3036_; lean_object* v___x_3037_; lean_object* v___f_3038_; lean_object* v___f_3039_; lean_object* v___x_210__overap_3040_; lean_object* v___x_3041_; 
v___f_3036_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3036_, 0, v_size_3034_);
v___x_3037_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_3038_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_3039_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_210__overap_3040_ = l_Std_Mutex_atomically___redArg(v___x_3037_, v___f_3038_, v___f_3039_, v_stream_3033_, v___f_3036_);
v___x_3041_ = lean_apply_1(v___x_210__overap_3040_, lean_box(0));
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___boxed(lean_object* v_stream_3042_, lean_object* v_size_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_3042_, v_size_3043_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object* v_pendingProducer_3046_, lean_object* v_pendingConsumer_3047_, uint8_t v_closed_3048_, lean_object* v_knownSize_3049_, lean_object* v_pendingIncomplete_3050_, lean_object* v_closeError_3051_, uint8_t v_closeAfterProducer_3052_, lean_object* v_a_3053_, lean_object* v___x_3054_, lean_object* v_x_3055_){
_start:
{
if (lean_obj_tag(v_x_3055_) == 0)
{
lean_object* v___x_3057_; 
lean_dec(v_closeError_3051_);
lean_dec(v_pendingIncomplete_3050_);
lean_dec(v_knownSize_3049_);
lean_dec(v_pendingConsumer_3047_);
lean_dec(v_pendingProducer_3046_);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_x_3055_);
return v___x_3057_;
}
else
{
lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3068_; 
v_isSharedCheck_3068_ = !lean_is_exclusive(v_x_3055_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v_x_3055_, 0);
lean_dec(v_unused_3069_);
v___x_3059_ = v_x_3055_;
v_isShared_3060_ = v_isSharedCheck_3068_;
goto v_resetjp_3058_;
}
else
{
lean_dec(v_x_3055_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3068_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3061_ = lean_box(0);
v___x_3062_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_3062_, 0, v_pendingProducer_3046_);
lean_ctor_set(v___x_3062_, 1, v_pendingConsumer_3047_);
lean_ctor_set(v___x_3062_, 2, v___x_3061_);
lean_ctor_set(v___x_3062_, 3, v_knownSize_3049_);
lean_ctor_set(v___x_3062_, 4, v_pendingIncomplete_3050_);
lean_ctor_set(v___x_3062_, 5, v_closeError_3051_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*6, v_closed_3048_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*6 + 1, v_closeAfterProducer_3052_);
v___x_3063_ = lean_st_ref_swap(v_a_3053_, v___x_3062_);
lean_dec(v___x_3063_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3054_);
v___x_3065_ = v___x_3059_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3054_);
v___x_3065_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object* v_pendingProducer_3070_, lean_object* v_pendingConsumer_3071_, lean_object* v_closed_3072_, lean_object* v_knownSize_3073_, lean_object* v_pendingIncomplete_3074_, lean_object* v_closeError_3075_, lean_object* v_closeAfterProducer_3076_, lean_object* v_a_3077_, lean_object* v___x_3078_, lean_object* v_x_3079_, lean_object* v___y_3080_){
_start:
{
uint8_t v_closed_boxed_3081_; uint8_t v_closeAfterProducer_boxed_3082_; lean_object* v_res_3083_; 
v_closed_boxed_3081_ = lean_unbox(v_closed_3072_);
v_closeAfterProducer_boxed_3082_ = lean_unbox(v_closeAfterProducer_3076_);
v_res_3083_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_3070_, v_pendingConsumer_3071_, v_closed_boxed_3081_, v_knownSize_3073_, v_pendingIncomplete_3074_, v_closeError_3075_, v_closeAfterProducer_boxed_3082_, v_a_3077_, v___x_3078_, v_x_3079_);
lean_dec(v_a_3077_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object* v_a_3084_, lean_object* v_x_3085_){
_start:
{
if (lean_obj_tag(v_x_3085_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3095_; 
v_a_3087_ = lean_ctor_get(v_x_3085_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_x_3085_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3089_ = v_x_3085_;
v_isShared_3090_ = v_isSharedCheck_3095_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v_x_3085_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3095_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3093_; 
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v_interestWaiter_3097_; 
v_a_3096_ = lean_ctor_get(v_x_3085_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v_x_3085_, 1);
v_interestWaiter_3097_ = lean_ctor_get(v_a_3096_, 2);
lean_inc(v_interestWaiter_3097_);
if (lean_obj_tag(v_interestWaiter_3097_) == 1)
{
lean_object* v_pendingProducer_3098_; lean_object* v_pendingConsumer_3099_; uint8_t v_closed_3100_; lean_object* v_knownSize_3101_; lean_object* v_pendingIncomplete_3102_; lean_object* v_closeError_3103_; uint8_t v_closeAfterProducer_3104_; lean_object* v_val_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___f_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v_pendingProducer_3098_ = lean_ctor_get(v_a_3096_, 0);
lean_inc(v_pendingProducer_3098_);
v_pendingConsumer_3099_ = lean_ctor_get(v_a_3096_, 1);
lean_inc(v_pendingConsumer_3099_);
v_closed_3100_ = lean_ctor_get_uint8(v_a_3096_, sizeof(void*)*6);
v_knownSize_3101_ = lean_ctor_get(v_a_3096_, 3);
lean_inc(v_knownSize_3101_);
v_pendingIncomplete_3102_ = lean_ctor_get(v_a_3096_, 4);
lean_inc(v_pendingIncomplete_3102_);
v_closeError_3103_ = lean_ctor_get(v_a_3096_, 5);
lean_inc(v_closeError_3103_);
v_closeAfterProducer_3104_ = lean_ctor_get_uint8(v_a_3096_, sizeof(void*)*6 + 1);
lean_dec(v_a_3096_);
v_val_3105_ = lean_ctor_get(v_interestWaiter_3097_, 0);
lean_inc(v_val_3105_);
lean_dec_ref_known(v_interestWaiter_3097_, 1);
v___x_3106_ = 1;
v___x_3107_ = lean_box(0);
v___x_3108_ = lean_box(v_closed_3100_);
v___x_3109_ = lean_box(v_closeAfterProducer_3104_);
lean_inc(v_a_3084_);
v___f_3110_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed), 11, 9);
lean_closure_set(v___f_3110_, 0, v_pendingProducer_3098_);
lean_closure_set(v___f_3110_, 1, v_pendingConsumer_3099_);
lean_closure_set(v___f_3110_, 2, v___x_3108_);
lean_closure_set(v___f_3110_, 3, v_knownSize_3101_);
lean_closure_set(v___f_3110_, 4, v_pendingIncomplete_3102_);
lean_closure_set(v___f_3110_, 5, v_closeError_3103_);
lean_closure_set(v___f_3110_, 6, v___x_3109_);
lean_closure_set(v___f_3110_, 7, v_a_3084_);
lean_closure_set(v___f_3110_, 8, v___x_3107_);
v___x_3111_ = lean_unsigned_to_nat(0u);
v___x_3112_ = 0;
v___x_3113_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_3105_, v___x_3106_);
lean_dec(v_val_3105_);
v___x_3114_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3115_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3111_, v___x_3112_, v___x_3114_, v___f_3110_);
return v___x_3115_;
}
else
{
lean_object* v___x_3116_; 
lean_dec(v_interestWaiter_3097_);
lean_dec(v_a_3096_);
v___x_3116_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3116_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object* v_a_3117_, lean_object* v_x_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_3117_, v_x_3118_);
lean_dec(v_a_3117_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object* v_a_3121_){
_start:
{
lean_object* v___f_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
lean_inc(v_a_3121_);
v___f_3123_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3123_, 0, v_a_3121_);
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = 0;
v___x_3126_ = lean_st_ref_get(v_a_3121_);
v___x_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
v___x_3129_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3124_, v___x_3125_, v___x_3128_, v___f_3123_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object* v_a_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_3130_);
lean_dec(v_a_3130_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object* v_promise_3133_, lean_object* v_x_3134_){
_start:
{
if (lean_obj_tag(v_x_3134_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3144_; 
v_a_3136_ = lean_ctor_get(v_x_3134_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_x_3134_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3138_ = v_x_3134_;
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v_x_3134_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
return v___x_3142_;
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3154_; 
v_a_3145_ = lean_ctor_get(v_x_3134_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_x_3134_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3147_ = v_x_3134_;
v_isShared_3148_ = v_isSharedCheck_3154_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v_x_3134_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3154_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v___x_3151_; 
v___x_3149_ = lean_io_promise_resolve(v_a_3145_, v_promise_3133_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3149_);
v___x_3151_ = v___x_3147_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
lean_object* v___x_3152_; 
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
return v___x_3152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_3155_, lean_object* v_x_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(v_promise_3155_, v_x_3156_);
lean_dec(v_promise_3155_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object* v_lose_3159_, lean_object* v___y_3160_, lean_object* v___f_3161_, lean_object* v_x_3162_){
_start:
{
if (lean_obj_tag(v_x_3162_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3172_; 
lean_dec_ref(v___f_3161_);
lean_dec_ref(v_lose_3159_);
v_a_3164_ = lean_ctor_get(v_x_3162_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_x_3162_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3166_ = v_x_3162_;
v_isShared_3167_ = v_isSharedCheck_3172_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v_x_3162_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3172_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; 
v___x_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
return v___x_3170_;
}
}
}
else
{
lean_object* v_a_3173_; uint8_t v___x_3174_; 
v_a_3173_ = lean_ctor_get(v_x_3162_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v_x_3162_, 1);
v___x_3174_ = lean_unbox(v_a_3173_);
lean_dec(v_a_3173_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; 
lean_dec_ref(v___f_3161_);
lean_inc(v___y_3160_);
v___x_3175_ = lean_apply_2(v_lose_3159_, v___y_3160_, lean_box(0));
return v___x_3175_;
}
else
{
lean_object* v___x_3176_; uint8_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec_ref(v_lose_3159_);
v___x_3176_ = lean_unsigned_to_nat(0u);
v___x_3177_ = 0;
v___x_3178_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_3160_);
v___x_3179_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3176_, v___x_3177_, v___x_3178_, v___f_3161_);
return v___x_3179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object* v_lose_3180_, lean_object* v___y_3181_, lean_object* v___f_3182_, lean_object* v_x_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(v_lose_3180_, v___y_3181_, v___f_3182_, v_x_3183_);
lean_dec(v___y_3181_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object* v_w_3186_, lean_object* v_lose_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_finished_3190_; lean_object* v_promise_3191_; lean_object* v___f_3192_; lean_object* v___f_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; lean_object* v___x_3196_; uint8_t v___y_3198_; uint8_t v___x_3206_; 
v_finished_3190_ = lean_ctor_get(v_w_3186_, 0);
lean_inc(v_finished_3190_);
v_promise_3191_ = lean_ctor_get(v_w_3186_, 1);
lean_inc(v_promise_3191_);
lean_dec_ref(v_w_3186_);
v___f_3192_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3192_, 0, v_promise_3191_);
lean_inc(v___y_3188_);
v___f_3193_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3193_, 0, v_lose_3187_);
lean_closure_set(v___f_3193_, 1, v___y_3188_);
lean_closure_set(v___f_3193_, 2, v___f_3192_);
v___x_3194_ = lean_unsigned_to_nat(0u);
v___x_3195_ = 0;
v___x_3196_ = lean_st_ref_take(v_finished_3190_);
v___x_3206_ = lean_unbox(v___x_3196_);
lean_dec(v___x_3196_);
if (v___x_3206_ == 0)
{
uint8_t v___x_3207_; 
v___x_3207_ = 1;
v___y_3198_ = v___x_3207_;
goto v___jp_3197_;
}
else
{
v___y_3198_ = v___x_3195_;
goto v___jp_3197_;
}
v___jp_3197_:
{
uint8_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3199_ = 1;
v___x_3200_ = lean_box(v___x_3199_);
v___x_3201_ = lean_st_ref_put(v_finished_3190_, v___x_3200_);
lean_dec(v_finished_3190_);
v___x_3202_ = lean_box(v___y_3198_);
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
v___x_3205_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3194_, v___x_3195_, v___x_3204_, v___f_3193_);
return v___x_3205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object* v_w_3208_, lean_object* v_lose_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_3208_, v_lose_3209_, v___y_3210_);
lean_dec(v___y_3210_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object* v___y_3213_, lean_object* v_x_3214_){
_start:
{
if (lean_obj_tag(v_x_3214_) == 0)
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v_x_3214_);
return v___x_3216_;
}
else
{
lean_object* v___x_3217_; 
lean_dec_ref_known(v_x_3214_, 1);
v___x_3217_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_3213_);
return v___x_3217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object* v___y_3218_, lean_object* v_x_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_3218_, v_x_3219_);
lean_dec(v___y_3218_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object* v_waiter_3222_, lean_object* v_pendingProducer_3223_, lean_object* v_interestWaiter_3224_, uint8_t v_closed_3225_, lean_object* v_knownSize_3226_, lean_object* v_pendingIncomplete_3227_, lean_object* v_closeError_3228_, uint8_t v_closeAfterProducer_3229_, uint8_t v_a_3230_, lean_object* v_____r_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___f_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_inc(v___y_3232_);
v___f_3234_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3234_, 0, v___y_3232_);
v___x_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3235_, 0, v_waiter_3222_);
v___x_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
v___x_3237_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_3237_, 0, v_pendingProducer_3223_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
lean_ctor_set(v___x_3237_, 2, v_interestWaiter_3224_);
lean_ctor_set(v___x_3237_, 3, v_knownSize_3226_);
lean_ctor_set(v___x_3237_, 4, v_pendingIncomplete_3227_);
lean_ctor_set(v___x_3237_, 5, v_closeError_3228_);
lean_ctor_set_uint8(v___x_3237_, sizeof(void*)*6, v_closed_3225_);
lean_ctor_set_uint8(v___x_3237_, sizeof(void*)*6 + 1, v_closeAfterProducer_3229_);
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = lean_st_ref_swap(v___y_3232_, v___x_3237_);
lean_dec(v___x_3239_);
v___x_3240_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3241_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3238_, v_a_3230_, v___x_3240_, v___f_3234_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object* v_waiter_3242_, lean_object* v_pendingProducer_3243_, lean_object* v_interestWaiter_3244_, lean_object* v_closed_3245_, lean_object* v_knownSize_3246_, lean_object* v_pendingIncomplete_3247_, lean_object* v_closeError_3248_, lean_object* v_closeAfterProducer_3249_, lean_object* v_a_3250_, lean_object* v_____r_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v_closed_boxed_3254_; uint8_t v_closeAfterProducer_boxed_3255_; uint8_t v_a_5687__boxed_3256_; lean_object* v_res_3257_; 
v_closed_boxed_3254_ = lean_unbox(v_closed_3245_);
v_closeAfterProducer_boxed_3255_ = lean_unbox(v_closeAfterProducer_3249_);
v_a_5687__boxed_3256_ = lean_unbox(v_a_3250_);
v_res_3257_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_3242_, v_pendingProducer_3243_, v_interestWaiter_3244_, v_closed_boxed_3254_, v_knownSize_3246_, v_pendingIncomplete_3247_, v_closeError_3248_, v_closeAfterProducer_boxed_3255_, v_a_5687__boxed_3256_, v_____r_3251_, v___y_3252_);
lean_dec(v___y_3252_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object* v_waiter_3262_, uint8_t v_a_3263_, lean_object* v___y_3264_, lean_object* v_x_3265_){
_start:
{
if (lean_obj_tag(v_x_3265_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref(v_waiter_3262_);
v_a_3267_ = lean_ctor_get(v_x_3265_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_x_3265_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3269_ = v_x_3265_;
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v_x_3265_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3273_; 
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
return v___x_3273_;
}
}
}
else
{
lean_object* v_a_3276_; lean_object* v_pendingProducer_3277_; lean_object* v_pendingConsumer_3278_; lean_object* v_interestWaiter_3279_; uint8_t v_closed_3280_; lean_object* v_knownSize_3281_; lean_object* v_pendingIncomplete_3282_; lean_object* v_closeError_3283_; uint8_t v_closeAfterProducer_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___f_3288_; 
v_a_3276_ = lean_ctor_get(v_x_3265_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v_x_3265_, 1);
v_pendingProducer_3277_ = lean_ctor_get(v_a_3276_, 0);
lean_inc_n(v_pendingProducer_3277_, 2);
v_pendingConsumer_3278_ = lean_ctor_get(v_a_3276_, 1);
lean_inc(v_pendingConsumer_3278_);
v_interestWaiter_3279_ = lean_ctor_get(v_a_3276_, 2);
lean_inc_n(v_interestWaiter_3279_, 2);
v_closed_3280_ = lean_ctor_get_uint8(v_a_3276_, sizeof(void*)*6);
v_knownSize_3281_ = lean_ctor_get(v_a_3276_, 3);
lean_inc_n(v_knownSize_3281_, 2);
v_pendingIncomplete_3282_ = lean_ctor_get(v_a_3276_, 4);
lean_inc_n(v_pendingIncomplete_3282_, 2);
v_closeError_3283_ = lean_ctor_get(v_a_3276_, 5);
lean_inc_n(v_closeError_3283_, 2);
v_closeAfterProducer_3284_ = lean_ctor_get_uint8(v_a_3276_, sizeof(void*)*6 + 1);
lean_dec(v_a_3276_);
v___x_3285_ = lean_box(v_closed_3280_);
v___x_3286_ = lean_box(v_closeAfterProducer_3284_);
v___x_3287_ = lean_box(v_a_3263_);
lean_inc_ref(v_waiter_3262_);
v___f_3288_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__0___boxed), 12, 9);
lean_closure_set(v___f_3288_, 0, v_waiter_3262_);
lean_closure_set(v___f_3288_, 1, v_pendingProducer_3277_);
lean_closure_set(v___f_3288_, 2, v_interestWaiter_3279_);
lean_closure_set(v___f_3288_, 3, v___x_3285_);
lean_closure_set(v___f_3288_, 4, v_knownSize_3281_);
lean_closure_set(v___f_3288_, 5, v_pendingIncomplete_3282_);
lean_closure_set(v___f_3288_, 6, v_closeError_3283_);
lean_closure_set(v___f_3288_, 7, v___x_3286_);
lean_closure_set(v___f_3288_, 8, v___x_3287_);
if (lean_obj_tag(v_pendingConsumer_3278_) == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec_ref(v___f_3288_);
v___x_3289_ = lean_box(0);
v___x_3290_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_3262_, v_pendingProducer_3277_, v_interestWaiter_3279_, v_closed_3280_, v_knownSize_3281_, v_pendingIncomplete_3282_, v_closeError_3283_, v_closeAfterProducer_3284_, v_a_3263_, v___x_3289_, v___y_3264_);
return v___x_3290_;
}
else
{
lean_object* v___f_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec_ref_known(v_pendingConsumer_3278_, 1);
lean_dec(v_closeError_3283_);
lean_dec(v_pendingIncomplete_3282_);
lean_dec(v_knownSize_3281_);
lean_dec(v_interestWaiter_3279_);
lean_dec(v_pendingProducer_3277_);
lean_dec_ref(v_waiter_3262_);
lean_inc(v___y_3264_);
v___f_3291_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3291_, 0, v___f_3288_);
lean_closure_set(v___f_3291_, 1, v___y_3264_);
v___x_3292_ = lean_unsigned_to_nat(0u);
v___x_3293_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1));
v___x_3294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3292_, v_a_3263_, v___x_3293_, v___f_3291_);
return v___x_3294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object* v_waiter_3295_, lean_object* v_a_3296_, lean_object* v___y_3297_, lean_object* v_x_3298_, lean_object* v___y_3299_){
_start:
{
uint8_t v_a_5728__boxed_3300_; lean_object* v_res_3301_; 
v_a_5728__boxed_3300_ = lean_unbox(v_a_3296_);
v_res_3301_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v_waiter_3295_, v_a_5728__boxed_3300_, v___y_3297_, v_x_3298_);
lean_dec(v___y_3297_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object* v___x_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3302_);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object* v___x_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_3307_, v___y_3308_);
lean_dec(v___y_3308_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object* v_waiter_3313_, lean_object* v___y_3314_, lean_object* v_x_3315_){
_start:
{
if (lean_obj_tag(v_x_3315_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3325_; 
lean_dec_ref(v_waiter_3313_);
v_a_3317_ = lean_ctor_get(v_x_3315_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_x_3315_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3319_ = v_x_3315_;
v_isShared_3320_ = v_isSharedCheck_3325_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v_x_3315_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3325_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3342_; 
v_a_3326_ = lean_ctor_get(v_x_3315_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_x_3315_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3328_ = v_x_3315_;
v_isShared_3329_ = v_isSharedCheck_3342_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v_x_3315_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3342_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
uint8_t v___x_3330_; 
v___x_3330_ = lean_unbox(v_a_3326_);
if (v___x_3330_ == 0)
{
lean_object* v___f_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
lean_inc(v___y_3314_);
lean_inc(v_a_3326_);
v___f_3331_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3331_, 0, v_waiter_3313_);
lean_closure_set(v___f_3331_, 1, v_a_3326_);
lean_closure_set(v___f_3331_, 2, v___y_3314_);
v___x_3332_ = lean_unsigned_to_nat(0u);
v___x_3333_ = lean_st_ref_get(v___y_3314_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3333_);
v___x_3335_ = v___x_3328_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
v___x_3337_ = lean_unbox(v_a_3326_);
lean_dec(v_a_3326_);
v___x_3338_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3332_, v___x_3337_, v___x_3336_, v___f_3331_);
return v___x_3338_;
}
}
else
{
lean_object* v___f_3340_; lean_object* v___x_3341_; 
lean_del_object(v___x_3328_);
lean_dec(v_a_3326_);
v___f_3340_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_3341_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_waiter_3313_, v___f_3340_, v___y_3314_);
return v___x_3341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object* v_waiter_3343_, lean_object* v___y_3344_, lean_object* v_x_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v_waiter_3343_, v___y_3344_, v_x_3345_);
lean_dec(v___y_3344_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object* v___y_3348_, lean_object* v___f_3349_, lean_object* v_x_3350_){
_start:
{
if (lean_obj_tag(v_x_3350_) == 0)
{
lean_object* v___x_3352_; 
lean_dec_ref(v___f_3349_);
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v_x_3350_);
return v___x_3352_;
}
else
{
lean_object* v___x_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec_ref_known(v_x_3350_, 1);
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = 0;
v___x_3355_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_3348_);
v___x_3356_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3353_, v___x_3354_, v___x_3355_, v___f_3349_);
return v___x_3356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object* v___y_3357_, lean_object* v___f_3358_, lean_object* v_x_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_3357_, v___f_3358_, v_x_3359_);
lean_dec(v___y_3357_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object* v_waiter_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___f_3365_; lean_object* v___f_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_inc_n(v___y_3363_, 2);
v___f_3365_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3365_, 0, v_waiter_3362_);
lean_closure_set(v___f_3365_, 1, v___y_3363_);
v___f_3366_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_3366_, 0, v___y_3363_);
lean_closure_set(v___f_3366_, 1, v___f_3365_);
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = 0;
v___x_3369_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3363_);
v___x_3370_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3367_, v___x_3368_, v___x_3369_, v___f_3366_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object* v_waiter_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_3371_, v___y_3372_);
lean_dec(v___y_3372_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object* v_stream_3375_, lean_object* v_waiter_3376_){
_start:
{
lean_object* v___f_3378_; lean_object* v___x_3379_; 
v___f_3378_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(v___f_3378_, 0, v_waiter_3376_);
v___x_3379_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3375_, v___f_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object* v_stream_3380_, lean_object* v_waiter_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_3380_, v_waiter_3381_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object* v_stream_3385_){
_start:
{
lean_object* v___f_3386_; lean_object* v___f_3387_; lean_object* v___f_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___f_3386_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_3385_, 2);
v___f_3387_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3387_, 0, v_stream_3385_);
v___f_3388_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_3389_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_3389_, 0, lean_box(0));
lean_closure_set(v___x_3389_, 1, lean_box(0));
lean_closure_set(v___x_3389_, 2, v_stream_3385_);
lean_closure_set(v___x_3389_, 3, v___f_3388_);
v___x_3390_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_3390_, 0, lean_box(0));
lean_closure_set(v___x_3390_, 1, lean_box(0));
lean_closure_set(v___x_3390_, 2, v_stream_3385_);
lean_closure_set(v___x_3390_, 3, v___f_3386_);
v___x_3391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___f_3387_);
lean_ctor_set(v___x_3391_, 2, v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0(lean_object* v_step_3392_, lean_object* v_acc_3393_, lean_object* v_x_3394_){
_start:
{
if (lean_obj_tag(v_x_3394_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_acc_3393_);
lean_dec_ref(v_step_3392_);
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
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3416_; 
v_a_3405_ = lean_ctor_get(v_x_3394_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_x_3394_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3407_ = v_x_3394_;
v_isShared_3408_ = v_isSharedCheck_3416_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v_x_3394_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3416_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
if (lean_obj_tag(v_a_3405_) == 1)
{
lean_object* v_val_3409_; lean_object* v___x_3410_; 
lean_del_object(v___x_3407_);
v_val_3409_ = lean_ctor_get(v_a_3405_, 0);
lean_inc(v_val_3409_);
lean_dec_ref_known(v_a_3405_, 1);
v___x_3410_ = lean_apply_3(v_step_3392_, v_val_3409_, v_acc_3393_, lean_box(0));
return v___x_3410_;
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3413_; 
lean_dec(v_a_3405_);
lean_dec_ref(v_step_3392_);
v___x_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3411_, 0, v_acc_3393_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3411_);
v___x_3413_ = v___x_3407_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; 
v___x_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed(lean_object* v_step_3417_, lean_object* v_acc_3418_, lean_object* v_x_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Std_Http_Body_Stream_forIn___redArg___lam__0(v_step_3417_, v_acc_3418_, v_x_3419_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1(lean_object* v_step_3422_, lean_object* v_stream_3423_, lean_object* v_x_3424_, lean_object* v_acc_3425_){
_start:
{
lean_object* v___f_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___f_3427_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3427_, 0, v_step_3422_);
lean_closure_set(v___f_3427_, 1, v_acc_3425_);
v___x_3428_ = lean_unsigned_to_nat(0u);
v___x_3429_ = 0;
v___x_3430_ = l_Std_Http_Body_Stream_recv(v_stream_3423_);
v___x_3431_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3428_, v___x_3429_, v___x_3430_, v___f_3427_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed(lean_object* v_step_3432_, lean_object* v_stream_3433_, lean_object* v_x_3434_, lean_object* v_acc_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Std_Http_Body_Stream_forIn___redArg___lam__1(v_step_3432_, v_stream_3433_, v_x_3434_, v_acc_3435_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2(lean_object* v_a_3438_, lean_object* v_x_3439_){
_start:
{
if (lean_obj_tag(v_x_3439_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3449_; 
v_a_3441_ = lean_ctor_get(v_x_3439_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_x_3439_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3443_ = v_x_3439_;
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v_x_3439_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
return v___x_3447_;
}
}
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_dec_ref_known(v_x_3439_, 1);
v___x_3450_ = l_IO_Promise_result_x21___redArg(v_a_3438_);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed(lean_object* v_a_3452_, lean_object* v_x_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Std_Http_Body_Stream_forIn___redArg___lam__2(v_a_3452_, v_x_3453_);
lean_dec(v_a_3452_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3(lean_object* v___f_3456_, lean_object* v___x_3457_, lean_object* v_acc_3458_, lean_object* v_x_3459_){
_start:
{
if (lean_obj_tag(v_x_3459_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3469_; 
lean_dec(v_acc_3458_);
lean_dec(v___x_3457_);
lean_dec_ref(v___f_3456_);
v_a_3461_ = lean_ctor_get(v_x_3459_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_x_3459_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3463_ = v_x_3459_;
v_isShared_3464_ = v_isSharedCheck_3469_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v_x_3459_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3469_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3482_; 
v_a_3470_ = lean_ctor_get(v_x_3459_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_x_3459_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3472_ = v_x_3459_;
v_isShared_3473_ = v_isSharedCheck_3482_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v_x_3459_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3482_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___f_3474_; uint8_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3478_; 
lean_inc(v_a_3470_);
v___f_3474_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3474_, 0, v_a_3470_);
v___x_3475_ = 0;
lean_inc(v___x_3457_);
v___x_3476_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_3456_, v___x_3457_, v_a_3470_, v_acc_3458_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v___x_3476_);
v___x_3478_ = v___x_3472_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
v___x_3480_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3457_, v___x_3475_, v___x_3479_, v___f_3474_);
return v___x_3480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed(lean_object* v___f_3483_, lean_object* v___x_3484_, lean_object* v_acc_3485_, lean_object* v_x_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Std_Http_Body_Stream_forIn___redArg___lam__3(v___f_3483_, v___x_3484_, v_acc_3485_, v_x_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_3489_, lean_object* v_acc_3490_, lean_object* v_step_3491_){
_start:
{
lean_object* v___f_3493_; lean_object* v___x_3494_; lean_object* v___f_3495_; uint8_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___f_3493_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3493_, 0, v_step_3491_);
lean_closure_set(v___f_3493_, 1, v_stream_3489_);
v___x_3494_ = lean_unsigned_to_nat(0u);
v___f_3495_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3495_, 0, v___f_3493_);
lean_closure_set(v___f_3495_, 1, v___x_3494_);
lean_closure_set(v___f_3495_, 2, v_acc_3490_);
v___x_3496_ = 0;
v___x_3497_ = lean_io_promise_new();
v___x_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
v___x_3500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3494_, v___x_3496_, v___x_3499_, v___f_3495_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_3501_, lean_object* v_acc_3502_, lean_object* v_step_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_3501_, v_acc_3502_, v_step_3503_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_3506_, lean_object* v_stream_3507_, lean_object* v_acc_3508_, lean_object* v_step_3509_){
_start:
{
lean_object* v___f_3511_; lean_object* v___x_3512_; lean_object* v___f_3513_; uint8_t v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___f_3511_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3511_, 0, v_step_3509_);
lean_closure_set(v___f_3511_, 1, v_stream_3507_);
v___x_3512_ = lean_unsigned_to_nat(0u);
v___f_3513_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3513_, 0, v___f_3511_);
lean_closure_set(v___f_3513_, 1, v___x_3512_);
lean_closure_set(v___f_3513_, 2, v_acc_3508_);
v___x_3514_ = 0;
v___x_3515_ = lean_io_promise_new();
v___x_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
v___x_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
v___x_3518_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3512_, v___x_3514_, v___x_3517_, v___f_3513_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_3519_, lean_object* v_stream_3520_, lean_object* v_acc_3521_, lean_object* v_step_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_3519_, v_stream_3520_, v_acc_3521_, v_step_3522_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(lean_object* v___y_3525_){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___y_3525_);
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0___boxed(lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(v___y_3529_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(lean_object* v_x_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___closed__0));
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1___boxed(lean_object* v_x_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(v_x_3535_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(lean_object* v_x_3538_){
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
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3559_; 
v_a_3549_ = lean_ctor_get(v_x_3538_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_x_3538_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3551_ = v_x_3538_;
v_isShared_3552_ = v_isSharedCheck_3559_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v_x_3538_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3559_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v_token_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v_token_3553_ = lean_ctor_get(v_a_3549_, 1);
lean_inc_ref(v_token_3553_);
lean_dec(v_a_3549_);
v___x_3554_ = l_Std_CancellationToken_selector(v_token_3553_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3554_);
v___x_3556_ = v___x_3551_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
return v___x_3557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2___boxed(lean_object* v_x_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(v_x_3560_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(lean_object* v_step_3563_, lean_object* v_b_3564_, lean_object* v_a_3565_, lean_object* v_x_3566_){
_start:
{
if (lean_obj_tag(v_x_3566_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_b_3564_);
lean_dec_ref(v_step_3563_);
v_a_3568_ = lean_ctor_get(v_x_3566_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_x_3566_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3570_ = v_x_3566_;
v_isShared_3571_ = v_isSharedCheck_3576_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v_x_3566_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3576_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; 
v___x_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
return v___x_3574_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3588_; 
v_a_3577_ = lean_ctor_get(v_x_3566_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_x_3566_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3579_ = v_x_3566_;
v_isShared_3580_ = v_isSharedCheck_3588_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v_x_3566_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3588_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
if (lean_obj_tag(v_a_3577_) == 1)
{
lean_object* v_val_3581_; lean_object* v___x_3582_; 
lean_del_object(v___x_3579_);
v_val_3581_ = lean_ctor_get(v_a_3577_, 0);
lean_inc(v_val_3581_);
lean_dec_ref_known(v_a_3577_, 1);
lean_inc_ref(v_a_3565_);
v___x_3582_ = lean_apply_4(v_step_3563_, v_val_3581_, v_b_3564_, v_a_3565_, lean_box(0));
return v___x_3582_;
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
lean_dec(v_a_3577_);
lean_dec_ref(v_step_3563_);
v___x_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3583_, 0, v_b_3564_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3583_);
v___x_3585_ = v___x_3579_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
return v___x_3586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed(lean_object* v_step_3589_, lean_object* v_b_3590_, lean_object* v_a_3591_, lean_object* v_x_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(v_step_3589_, v_b_3590_, v_a_3591_, v_x_3592_);
lean_dec_ref(v_a_3591_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(lean_object* v_stream_3595_, lean_object* v___f_3596_, lean_object* v___f_3597_, lean_object* v___f_3598_, lean_object* v_x_3599_){
_start:
{
if (lean_obj_tag(v_x_3599_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3609_; 
lean_dec_ref(v___f_3598_);
lean_dec_ref(v___f_3597_);
lean_dec_ref(v___f_3596_);
lean_dec_ref(v_stream_3595_);
v_a_3601_ = lean_ctor_get(v_x_3599_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_x_3599_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3603_ = v_x_3599_;
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v_x_3599_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; 
v___x_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
return v___x_3607_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_a_3610_ = lean_ctor_get(v_x_3599_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v_x_3599_, 1);
v___x_3611_ = l_Std_Http_Body_Stream_recvSelector(v_stream_3595_);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set(v___x_3612_, 1, v___f_3596_);
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v_a_3610_);
lean_ctor_set(v___x_3613_, 1, v___f_3597_);
v___x_3614_ = lean_unsigned_to_nat(2u);
v___x_3615_ = lean_mk_empty_array_with_capacity(v___x_3614_);
v___x_3616_ = lean_array_push(v___x_3615_, v___x_3612_);
v___x_3617_ = lean_array_push(v___x_3616_, v___x_3613_);
v___x_3618_ = lean_unsigned_to_nat(0u);
v___x_3619_ = 0;
v___x_3620_ = l_Std_Async_Selectable_one___redArg(v___x_3617_);
v___x_3621_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3618_, v___x_3619_, v___x_3620_, v___f_3598_);
return v___x_3621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed(lean_object* v_stream_3622_, lean_object* v___f_3623_, lean_object* v___f_3624_, lean_object* v___f_3625_, lean_object* v_x_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(v_stream_3622_, v___f_3623_, v___f_3624_, v___f_3625_, v_x_3626_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(lean_object* v_step_3629_, lean_object* v_a_3630_, lean_object* v_stream_3631_, lean_object* v___f_3632_, lean_object* v___f_3633_, lean_object* v___f_3634_, lean_object* v_u_3635_, lean_object* v_b_3636_){
_start:
{
lean_object* v___f_3638_; lean_object* v___f_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_inc_ref_n(v_a_3630_, 2);
v___f_3638_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3638_, 0, v_step_3629_);
lean_closure_set(v___f_3638_, 1, v_b_3636_);
lean_closure_set(v___f_3638_, 2, v_a_3630_);
v___f_3639_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3639_, 0, v_stream_3631_);
lean_closure_set(v___f_3639_, 1, v___f_3632_);
lean_closure_set(v___f_3639_, 2, v___f_3633_);
lean_closure_set(v___f_3639_, 3, v___f_3638_);
v___x_3640_ = lean_unsigned_to_nat(0u);
v___x_3641_ = 0;
v___x_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3642_, 0, v_a_3630_);
v___x_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
v___x_3644_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3640_, v___x_3641_, v___x_3643_, v___f_3634_);
v___x_3645_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3640_, v___x_3641_, v___x_3644_, v___f_3639_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed(lean_object* v_step_3646_, lean_object* v_a_3647_, lean_object* v_stream_3648_, lean_object* v___f_3649_, lean_object* v___f_3650_, lean_object* v___f_3651_, lean_object* v_u_3652_, lean_object* v_b_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(v_step_3646_, v_a_3647_, v_stream_3648_, v___f_3649_, v___f_3650_, v___f_3651_, v_u_3652_, v_b_3653_);
lean_dec_ref(v_a_3647_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_3659_, lean_object* v_acc_3660_, lean_object* v_step_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v___f_3664_; lean_object* v___f_3665_; lean_object* v___f_3666_; lean_object* v___f_3667_; lean_object* v___x_3668_; lean_object* v___f_3669_; uint8_t v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___f_3664_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_3665_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_3666_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_3662_);
v___f_3667_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_3667_, 0, v_step_3661_);
lean_closure_set(v___f_3667_, 1, v_a_3662_);
lean_closure_set(v___f_3667_, 2, v_stream_3659_);
lean_closure_set(v___f_3667_, 3, v___f_3664_);
lean_closure_set(v___f_3667_, 4, v___f_3665_);
lean_closure_set(v___f_3667_, 5, v___f_3666_);
v___x_3668_ = lean_unsigned_to_nat(0u);
v___f_3669_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3669_, 0, v___f_3667_);
lean_closure_set(v___f_3669_, 1, v___x_3668_);
lean_closure_set(v___f_3669_, 2, v_acc_3660_);
v___x_3670_ = 0;
v___x_3671_ = lean_io_promise_new();
v___x_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3671_);
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
v___x_3674_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3668_, v___x_3670_, v___x_3673_, v___f_3669_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_3675_, lean_object* v_acc_3676_, lean_object* v_step_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_3675_, v_acc_3676_, v_step_3677_, v_a_3678_);
lean_dec_ref(v_a_3678_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_3681_, lean_object* v_stream_3682_, lean_object* v_acc_3683_, lean_object* v_step_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v___f_3687_; lean_object* v___f_3688_; lean_object* v___f_3689_; lean_object* v___f_3690_; lean_object* v___x_3691_; lean_object* v___f_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___f_3687_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_3688_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_3689_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_3685_);
v___f_3690_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_3690_, 0, v_step_3684_);
lean_closure_set(v___f_3690_, 1, v_a_3685_);
lean_closure_set(v___f_3690_, 2, v_stream_3682_);
lean_closure_set(v___f_3690_, 3, v___f_3687_);
lean_closure_set(v___f_3690_, 4, v___f_3688_);
lean_closure_set(v___f_3690_, 5, v___f_3689_);
v___x_3691_ = lean_unsigned_to_nat(0u);
v___f_3692_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3692_, 0, v___f_3690_);
lean_closure_set(v___f_3692_, 1, v___x_3691_);
lean_closure_set(v___f_3692_, 2, v_acc_3683_);
v___x_3693_ = 0;
v___x_3694_ = lean_io_promise_new();
v___x_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
v___x_3697_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3691_, v___x_3693_, v___x_3696_, v___f_3692_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_3698_, lean_object* v_stream_3699_, lean_object* v_acc_3700_, lean_object* v_step_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_3698_, v_stream_3699_, v_acc_3700_, v_step_3701_, v_a_3702_);
lean_dec_ref(v_a_3702_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v_stream_3707_, lean_object* v___f_3708_, lean_object* v___f_3709_, lean_object* v_x_3710_){
_start:
{
if (lean_obj_tag(v_x_3710_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3720_; 
lean_dec_ref(v___f_3709_);
lean_dec_ref(v___f_3708_);
lean_dec_ref(v_stream_3707_);
v_a_3712_ = lean_ctor_get(v_x_3710_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_x_3710_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3714_ = v_x_3710_;
v_isShared_3715_ = v_isSharedCheck_3720_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v_x_3710_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3720_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
return v___x_3718_;
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v_a_3721_ = lean_ctor_get(v_x_3710_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v_x_3710_, 1);
v___x_3722_ = l_Std_Http_Body_Stream_recvSelector(v_stream_3707_);
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set(v___x_3723_, 1, v___f_3708_);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v_a_3721_);
lean_ctor_set(v___x_3724_, 1, v___f_3709_);
v___x_3725_ = lean_unsigned_to_nat(2u);
v___x_3726_ = lean_mk_empty_array_with_capacity(v___x_3725_);
v___x_3727_ = lean_array_push(v___x_3726_, v___x_3723_);
v___x_3728_ = lean_array_push(v___x_3727_, v___x_3724_);
v___x_3729_ = l_Std_Async_Selectable_one___redArg(v___x_3728_);
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v_stream_3730_, lean_object* v___f_3731_, lean_object* v___f_3732_, lean_object* v_x_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v_stream_3730_, v___f_3731_, v___f_3732_, v_x_3733_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v___f_3736_, lean_object* v___f_3737_, lean_object* v___f_3738_, lean_object* v_stream_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v___f_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___f_3742_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3742_, 0, v_stream_3739_);
lean_closure_set(v___f_3742_, 1, v___f_3736_);
lean_closure_set(v___f_3742_, 2, v___f_3737_);
v___x_3743_ = lean_unsigned_to_nat(0u);
v___x_3744_ = 0;
lean_inc_ref(v___y_3740_);
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___y_3740_);
v___x_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
v___x_3747_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3743_, v___x_3744_, v___x_3746_, v___f_3738_);
v___x_3748_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3743_, v___x_3744_, v___x_3747_, v___f_3742_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v___f_3749_, lean_object* v___f_3750_, lean_object* v___f_3751_, lean_object* v_stream_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v___f_3749_, v___f_3750_, v___f_3751_, v_stream_3752_, v___y_3753_);
lean_dec_ref(v___y_3753_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_pieces_3761_, lean_object* v_size_3762_, lean_object* v_toPure_3763_, lean_object* v_____r_3764_){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces(v_pieces_3761_, v_size_3762_);
v___x_3766_ = lean_apply_2(v_toPure_3763_, lean_box(0), v___x_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0___boxed(lean_object* v_pieces_3767_, lean_object* v_size_3768_, lean_object* v_toPure_3769_, lean_object* v_____r_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(v_pieces_3767_, v_size_3768_, v_toPure_3769_, v_____r_3770_);
lean_dec(v_size_3768_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v___f_3772_, lean_object* v_____r_3773_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_apply_1(v___f_3772_, v_____r_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2(lean_object* v_inst_3778_, lean_object* v_toBind_3779_, lean_object* v___f_3780_, lean_object* v___f_3781_, uint8_t v_____do__lift_3782_){
_start:
{
if (v_____do__lift_3782_ == 0)
{
lean_object* v_throw_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_dec(v___f_3781_);
v_throw_3783_ = lean_ctor_get(v_inst_3778_, 0);
lean_inc(v_throw_3783_);
lean_dec_ref(v_inst_3778_);
v___x_3784_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__1));
v___x_3785_ = lean_apply_2(v_throw_3783_, lean_box(0), v___x_3784_);
v___x_3786_ = lean_apply_4(v_toBind_3779_, lean_box(0), lean_box(0), v___x_3785_, v___f_3780_);
return v___x_3786_;
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_dec(v___f_3780_);
lean_dec(v_toBind_3779_);
lean_dec_ref(v_inst_3778_);
v___x_3787_ = lean_box(0);
v___x_3788_ = lean_apply_1(v___f_3781_, v___x_3787_);
return v___x_3788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___boxed(lean_object* v_inst_3789_, lean_object* v_toBind_3790_, lean_object* v___f_3791_, lean_object* v___f_3792_, lean_object* v_____do__lift_3793_){
_start:
{
uint8_t v_____do__lift_336__boxed_3794_; lean_object* v_res_3795_; 
v_____do__lift_336__boxed_3794_ = lean_unbox(v_____do__lift_3793_);
v_res_3795_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2(v_inst_3789_, v_toBind_3790_, v___f_3791_, v___f_3792_, v_____do__lift_336__boxed_3794_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5(lean_object* v_inst_3798_, uint64_t v_val_3799_, lean_object* v_toBind_3800_, lean_object* v___f_3801_, lean_object* v_____r_3802_){
_start:
{
lean_object* v_throw_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_throw_3803_ = lean_ctor_get(v_inst_3798_, 0);
lean_inc(v_throw_3803_);
lean_dec_ref(v_inst_3798_);
v___x_3804_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___closed__0));
v___x_3805_ = lean_uint64_to_nat(v_val_3799_);
v___x_3806_ = l_Nat_reprFast(v___x_3805_);
v___x_3807_ = lean_string_append(v___x_3804_, v___x_3806_);
lean_dec_ref(v___x_3806_);
v___x_3808_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___closed__1));
v___x_3809_ = lean_string_append(v___x_3807_, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
v___x_3811_ = lean_apply_2(v_throw_3803_, lean_box(0), v___x_3810_);
v___x_3812_ = lean_apply_4(v_toBind_3800_, lean_box(0), lean_box(0), v___x_3811_, v___f_3801_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___boxed(lean_object* v_inst_3813_, lean_object* v_val_3814_, lean_object* v_toBind_3815_, lean_object* v___f_3816_, lean_object* v_____r_3817_){
_start:
{
uint64_t v_val_363__boxed_3818_; lean_object* v_res_3819_; 
v_val_363__boxed_3818_ = lean_unbox_uint64(v_val_3814_);
lean_dec_ref(v_val_3814_);
v_res_3819_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5(v_inst_3813_, v_val_363__boxed_3818_, v_toBind_3815_, v___f_3816_, v_____r_3817_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__4(lean_object* v_stream_3820_, lean_object* v_inst_3821_, lean_object* v_toBind_3822_, lean_object* v___f_3823_, lean_object* v_size_3824_, lean_object* v_pieces_3825_, lean_object* v_inst_3826_, lean_object* v_inst_3827_, lean_object* v_inst_3828_, lean_object* v_maximumSize_3829_, lean_object* v_____do__lift_3830_){
_start:
{
if (lean_obj_tag(v_____do__lift_3830_) == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_dec(v_maximumSize_3829_);
lean_dec(v_inst_3828_);
lean_dec_ref(v_inst_3827_);
lean_dec_ref(v_inst_3826_);
lean_dec(v_pieces_3825_);
v___x_3831_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_isClosed___boxed), 2, 1);
lean_closure_set(v___x_3831_, 0, v_stream_3820_);
v___x_3832_ = lean_apply_2(v_inst_3821_, lean_box(0), v___x_3831_);
v___x_3833_ = lean_apply_4(v_toBind_3822_, lean_box(0), lean_box(0), v___x_3832_, v___f_3823_);
return v___x_3833_;
}
else
{
lean_object* v_val_3834_; lean_object* v_data_3835_; lean_object* v___x_3836_; lean_object* v_size_3837_; lean_object* v___f_3838_; 
lean_dec(v___f_3823_);
v_val_3834_ = lean_ctor_get(v_____do__lift_3830_, 0);
lean_inc(v_val_3834_);
lean_dec_ref_known(v_____do__lift_3830_, 1);
v_data_3835_ = lean_ctor_get(v_val_3834_, 0);
lean_inc_ref_n(v_data_3835_, 2);
lean_dec(v_val_3834_);
v___x_3836_ = lean_byte_array_size(v_data_3835_);
v_size_3837_ = lean_nat_add(v_size_3824_, v___x_3836_);
lean_inc(v_size_3837_);
lean_inc(v_maximumSize_3829_);
lean_inc_ref(v_stream_3820_);
lean_inc(v_inst_3828_);
lean_inc(v_inst_3821_);
lean_inc_ref(v_inst_3827_);
lean_inc_ref(v_inst_3826_);
lean_inc(v_pieces_3825_);
v___f_3838_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3), 10, 9);
lean_closure_set(v___f_3838_, 0, v_data_3835_);
lean_closure_set(v___f_3838_, 1, v_pieces_3825_);
lean_closure_set(v___f_3838_, 2, v_inst_3826_);
lean_closure_set(v___f_3838_, 3, v_inst_3827_);
lean_closure_set(v___f_3838_, 4, v_inst_3821_);
lean_closure_set(v___f_3838_, 5, v_inst_3828_);
lean_closure_set(v___f_3838_, 6, v_stream_3820_);
lean_closure_set(v___f_3838_, 7, v_maximumSize_3829_);
lean_closure_set(v___f_3838_, 8, v_size_3837_);
if (lean_obj_tag(v_maximumSize_3829_) == 1)
{
lean_object* v_val_3839_; uint64_t v___x_3840_; uint64_t v___x_3841_; uint8_t v___x_3842_; 
v_val_3839_ = lean_ctor_get(v_maximumSize_3829_, 0);
v___x_3840_ = lean_uint64_of_nat(v_size_3837_);
v___x_3841_ = lean_unbox_uint64(v_val_3839_);
v___x_3842_ = lean_uint64_dec_lt(v___x_3841_, v___x_3840_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_dec_ref(v___f_3838_);
lean_dec(v_toBind_3822_);
v___x_3843_ = lean_box(0);
v___x_3844_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3(v_data_3835_, v_pieces_3825_, v_inst_3826_, v_inst_3827_, v_inst_3821_, v_inst_3828_, v_stream_3820_, v_maximumSize_3829_, v_size_3837_, v___x_3843_);
return v___x_3844_;
}
else
{
lean_object* v___f_3845_; lean_object* v___f_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_inc(v_val_3839_);
lean_dec_ref_known(v_maximumSize_3829_, 1);
lean_dec(v_size_3837_);
lean_dec_ref(v_data_3835_);
lean_dec(v_inst_3828_);
lean_dec_ref(v_inst_3826_);
lean_dec(v_pieces_3825_);
v___f_3845_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3845_, 0, v___f_3838_);
lean_inc(v_toBind_3822_);
v___f_3846_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__5___boxed), 5, 4);
lean_closure_set(v___f_3846_, 0, v_inst_3827_);
lean_closure_set(v___f_3846_, 1, v_val_3839_);
lean_closure_set(v___f_3846_, 2, v_toBind_3822_);
lean_closure_set(v___f_3846_, 3, v___f_3845_);
v___x_3847_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_close___boxed), 2, 1);
lean_closure_set(v___x_3847_, 0, v_stream_3820_);
v___x_3848_ = lean_apply_2(v_inst_3821_, lean_box(0), v___x_3847_);
v___x_3849_ = lean_apply_4(v_toBind_3822_, lean_box(0), lean_box(0), v___x_3848_, v___f_3846_);
return v___x_3849_;
}
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_dec_ref(v___f_3838_);
lean_dec(v_toBind_3822_);
v___x_3850_ = lean_box(0);
v___x_3851_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3(v_data_3835_, v_pieces_3825_, v_inst_3826_, v_inst_3827_, v_inst_3821_, v_inst_3828_, v_stream_3820_, v_maximumSize_3829_, v_size_3837_, v___x_3850_);
return v___x_3851_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__4___boxed(lean_object* v_stream_3852_, lean_object* v_inst_3853_, lean_object* v_toBind_3854_, lean_object* v___f_3855_, lean_object* v_size_3856_, lean_object* v_pieces_3857_, lean_object* v_inst_3858_, lean_object* v_inst_3859_, lean_object* v_inst_3860_, lean_object* v_maximumSize_3861_, lean_object* v_____do__lift_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__4(v_stream_3852_, v_inst_3853_, v_toBind_3854_, v___f_3855_, v_size_3856_, v_pieces_3857_, v_inst_3858_, v_inst_3859_, v_inst_3860_, v_maximumSize_3861_, v_____do__lift_3862_);
lean_dec(v_size_3856_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_3864_, lean_object* v_inst_3865_, lean_object* v_inst_3866_, lean_object* v_inst_3867_, lean_object* v_stream_3868_, lean_object* v_maximumSize_3869_, lean_object* v_pieces_3870_, lean_object* v_size_3871_){
_start:
{
lean_object* v_toApplicative_3872_; lean_object* v_toBind_3873_; lean_object* v_toPure_3874_; lean_object* v___x_3875_; lean_object* v___f_3876_; lean_object* v___f_3877_; lean_object* v___f_3878_; lean_object* v___f_3879_; lean_object* v___x_3880_; 
v_toApplicative_3872_ = lean_ctor_get(v_inst_3864_, 0);
v_toBind_3873_ = lean_ctor_get(v_inst_3864_, 1);
lean_inc_n(v_toBind_3873_, 3);
v_toPure_3874_ = lean_ctor_get(v_toApplicative_3872_, 1);
lean_inc(v_inst_3867_);
lean_inc_ref(v_stream_3868_);
v___x_3875_ = lean_apply_1(v_inst_3867_, v_stream_3868_);
lean_inc(v_toPure_3874_);
lean_inc(v_size_3871_);
lean_inc(v_pieces_3870_);
v___f_3876_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3876_, 0, v_pieces_3870_);
lean_closure_set(v___f_3876_, 1, v_size_3871_);
lean_closure_set(v___f_3876_, 2, v_toPure_3874_);
lean_inc_ref(v___f_3876_);
v___f_3877_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3877_, 0, v___f_3876_);
lean_inc_ref(v_inst_3865_);
v___f_3878_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_3878_, 0, v_inst_3865_);
lean_closure_set(v___f_3878_, 1, v_toBind_3873_);
lean_closure_set(v___f_3878_, 2, v___f_3877_);
lean_closure_set(v___f_3878_, 3, v___f_3876_);
v___f_3879_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_3879_, 0, v_stream_3868_);
lean_closure_set(v___f_3879_, 1, v_inst_3866_);
lean_closure_set(v___f_3879_, 2, v_toBind_3873_);
lean_closure_set(v___f_3879_, 3, v___f_3878_);
lean_closure_set(v___f_3879_, 4, v_size_3871_);
lean_closure_set(v___f_3879_, 5, v_pieces_3870_);
lean_closure_set(v___f_3879_, 6, v_inst_3864_);
lean_closure_set(v___f_3879_, 7, v_inst_3865_);
lean_closure_set(v___f_3879_, 8, v_inst_3867_);
lean_closure_set(v___f_3879_, 9, v_maximumSize_3869_);
v___x_3880_ = lean_apply_4(v_toBind_3873_, lean_box(0), lean_box(0), v___x_3875_, v___f_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3(lean_object* v_data_3881_, lean_object* v_pieces_3882_, lean_object* v_inst_3883_, lean_object* v_inst_3884_, lean_object* v_inst_3885_, lean_object* v_inst_3886_, lean_object* v_stream_3887_, lean_object* v_maximumSize_3888_, lean_object* v_size_3889_, lean_object* v_____r_3890_){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3891_, 0, v_data_3881_);
lean_ctor_set(v___x_3891_, 1, v_pieces_3882_);
v___x_3892_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3883_, v_inst_3884_, v_inst_3885_, v_inst_3886_, v_stream_3887_, v_maximumSize_3888_, v___x_3891_, v_size_3889_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_3893_, lean_object* v_inst_3894_, lean_object* v_inst_3895_, lean_object* v_inst_3896_, lean_object* v_inst_3897_, lean_object* v_stream_3898_, lean_object* v_maximumSize_3899_, lean_object* v_pieces_3900_, lean_object* v_size_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3894_, v_inst_3895_, v_inst_3896_, v_inst_3897_, v_stream_3898_, v_maximumSize_3899_, v_pieces_3900_, v_size_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_3903_, lean_object* v_inst_3904_, lean_object* v_toPure_3905_, lean_object* v_result_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = lean_apply_1(v_inst_3903_, v_result_3906_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3917_; 
lean_dec(v_toPure_3905_);
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3910_ = v___x_3907_;
v_isShared_3911_ = v_isSharedCheck_3917_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3917_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v_throw_3912_; lean_object* v___x_3914_; 
v_throw_3912_ = lean_ctor_get(v_inst_3904_, 0);
lean_inc(v_throw_3912_);
lean_dec_ref(v_inst_3904_);
if (v_isShared_3911_ == 0)
{
lean_ctor_set_tag(v___x_3910_, 18);
v___x_3914_ = v___x_3910_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3908_);
v___x_3914_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3915_; 
v___x_3915_ = lean_apply_2(v_throw_3912_, lean_box(0), v___x_3914_);
return v___x_3915_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3919_; 
lean_dec_ref(v_inst_3904_);
v_a_3918_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3919_ = lean_apply_2(v_toPure_3905_, lean_box(0), v_a_3918_);
return v___x_3919_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_3920_, lean_object* v_inst_3921_, lean_object* v_inst_3922_, lean_object* v_inst_3923_, lean_object* v_inst_3924_, lean_object* v_stream_3925_, lean_object* v_maximumSize_3926_){
_start:
{
lean_object* v_toApplicative_3927_; lean_object* v_toBind_3928_; lean_object* v_toPure_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___f_3933_; lean_object* v___x_3934_; 
v_toApplicative_3927_ = lean_ctor_get(v_inst_3921_, 0);
v_toBind_3928_ = lean_ctor_get(v_inst_3921_, 1);
lean_inc(v_toBind_3928_);
v_toPure_3929_ = lean_ctor_get(v_toApplicative_3927_, 1);
lean_inc(v_toPure_3929_);
v___x_3930_ = lean_box(0);
v___x_3931_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inst_3922_);
v___x_3932_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3921_, v_inst_3922_, v_inst_3923_, v_inst_3924_, v_stream_3925_, v_maximumSize_3926_, v___x_3930_, v___x_3931_);
v___f_3933_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3933_, 0, v_inst_3920_);
lean_closure_set(v___f_3933_, 1, v_inst_3922_);
lean_closure_set(v___f_3933_, 2, v_toPure_3929_);
v___x_3934_ = lean_apply_4(v_toBind_3928_, lean_box(0), lean_box(0), v___x_3932_, v___f_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_3935_, lean_object* v_m_3936_, lean_object* v_inst_3937_, lean_object* v_inst_3938_, lean_object* v_inst_3939_, lean_object* v_inst_3940_, lean_object* v_inst_3941_, lean_object* v_stream_3942_, lean_object* v_maximumSize_3943_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_3937_, v_inst_3938_, v_inst_3939_, v_inst_3940_, v_inst_3941_, v_stream_3942_, v_maximumSize_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0(lean_object* v_toPure_3945_, lean_object* v_____r_3946_){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = lean_box(0);
v___x_3948_ = lean_apply_2(v_toPure_3945_, lean_box(0), v___x_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(lean_object* v_toPure_3949_, uint64_t v_consumed_3950_, lean_object* v_drainLimit_3951_, lean_object* v_inst_3952_, lean_object* v_inst_3953_, lean_object* v_stream_3954_, lean_object* v_closeStream_3955_, lean_object* v_toBind_3956_, lean_object* v___f_3957_, lean_object* v_____do__lift_3958_){
_start:
{
if (lean_obj_tag(v_____do__lift_3958_) == 0)
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_dec(v___f_3957_);
lean_dec(v_toBind_3956_);
lean_dec(v_closeStream_3955_);
lean_dec_ref(v_stream_3954_);
lean_dec(v_inst_3953_);
lean_dec_ref(v_inst_3952_);
lean_dec(v_drainLimit_3951_);
v___x_3959_ = lean_box(0);
v___x_3960_ = lean_apply_2(v_toPure_3949_, lean_box(0), v___x_3959_);
return v___x_3960_;
}
else
{
lean_object* v_val_3961_; lean_object* v_data_3962_; lean_object* v___x_3963_; uint64_t v___x_3964_; uint64_t v_consumed_3965_; 
lean_dec(v_toPure_3949_);
v_val_3961_ = lean_ctor_get(v_____do__lift_3958_, 0);
v_data_3962_ = lean_ctor_get(v_val_3961_, 0);
v___x_3963_ = lean_byte_array_size(v_data_3962_);
v___x_3964_ = lean_uint64_of_nat(v___x_3963_);
v_consumed_3965_ = lean_uint64_add(v_consumed_3950_, v___x_3964_);
if (lean_obj_tag(v_drainLimit_3951_) == 1)
{
lean_object* v_val_3966_; uint64_t v___x_3967_; uint8_t v___x_3968_; 
v_val_3966_ = lean_ctor_get(v_drainLimit_3951_, 0);
v___x_3967_ = lean_unbox_uint64(v_val_3966_);
v___x_3968_ = lean_uint64_dec_lt(v___x_3967_, v_consumed_3965_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_dec(v___f_3957_);
lean_dec(v_toBind_3956_);
v___x_3969_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3952_, v_inst_3953_, v_stream_3954_, v_drainLimit_3951_, v_closeStream_3955_, v_consumed_3965_);
return v___x_3969_;
}
else
{
lean_object* v___x_3970_; 
lean_dec_ref_known(v_drainLimit_3951_, 1);
lean_dec_ref(v_stream_3954_);
lean_dec(v_inst_3953_);
lean_dec_ref(v_inst_3952_);
v___x_3970_ = lean_apply_4(v_toBind_3956_, lean_box(0), lean_box(0), v_closeStream_3955_, v___f_3957_);
return v___x_3970_;
}
}
else
{
lean_object* v___x_3971_; 
lean_dec(v___f_3957_);
lean_dec(v_toBind_3956_);
v___x_3971_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3952_, v_inst_3953_, v_stream_3954_, v_drainLimit_3951_, v_closeStream_3955_, v_consumed_3965_);
return v___x_3971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed(lean_object* v_toPure_3972_, lean_object* v_consumed_3973_, lean_object* v_drainLimit_3974_, lean_object* v_inst_3975_, lean_object* v_inst_3976_, lean_object* v_stream_3977_, lean_object* v_closeStream_3978_, lean_object* v_toBind_3979_, lean_object* v___f_3980_, lean_object* v_____do__lift_3981_){
_start:
{
uint64_t v_consumed_boxed_3982_; lean_object* v_res_3983_; 
v_consumed_boxed_3982_ = lean_unbox_uint64(v_consumed_3973_);
lean_dec_ref(v_consumed_3973_);
v_res_3983_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(v_toPure_3972_, v_consumed_boxed_3982_, v_drainLimit_3974_, v_inst_3975_, v_inst_3976_, v_stream_3977_, v_closeStream_3978_, v_toBind_3979_, v___f_3980_, v_____do__lift_3981_);
lean_dec(v_____do__lift_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(lean_object* v_inst_3984_, lean_object* v_inst_3985_, lean_object* v_stream_3986_, lean_object* v_drainLimit_3987_, lean_object* v_closeStream_3988_, uint64_t v_consumed_3989_){
_start:
{
lean_object* v_toApplicative_3990_; lean_object* v_toBind_3991_; lean_object* v_toPure_3992_; lean_object* v___x_3993_; lean_object* v___f_3994_; lean_object* v___x_3995_; lean_object* v___f_3996_; lean_object* v___x_3997_; 
v_toApplicative_3990_ = lean_ctor_get(v_inst_3984_, 0);
v_toBind_3991_ = lean_ctor_get(v_inst_3984_, 1);
lean_inc_n(v_toBind_3991_, 2);
v_toPure_3992_ = lean_ctor_get(v_toApplicative_3990_, 1);
lean_inc_n(v_toPure_3992_, 2);
lean_inc(v_inst_3985_);
lean_inc_ref(v_stream_3986_);
v___x_3993_ = lean_apply_1(v_inst_3985_, v_stream_3986_);
v___f_3994_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3994_, 0, v_toPure_3992_);
v___x_3995_ = lean_box_uint64(v_consumed_3989_);
v___f_3996_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3996_, 0, v_toPure_3992_);
lean_closure_set(v___f_3996_, 1, v___x_3995_);
lean_closure_set(v___f_3996_, 2, v_drainLimit_3987_);
lean_closure_set(v___f_3996_, 3, v_inst_3984_);
lean_closure_set(v___f_3996_, 4, v_inst_3985_);
lean_closure_set(v___f_3996_, 5, v_stream_3986_);
lean_closure_set(v___f_3996_, 6, v_closeStream_3988_);
lean_closure_set(v___f_3996_, 7, v_toBind_3991_);
lean_closure_set(v___f_3996_, 8, v___f_3994_);
v___x_3997_ = lean_apply_4(v_toBind_3991_, lean_box(0), lean_box(0), v___x_3993_, v___f_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___boxed(lean_object* v_inst_3998_, lean_object* v_inst_3999_, lean_object* v_stream_4000_, lean_object* v_drainLimit_4001_, lean_object* v_closeStream_4002_, lean_object* v_consumed_4003_){
_start:
{
uint64_t v_consumed_boxed_4004_; lean_object* v_res_4005_; 
v_consumed_boxed_4004_ = lean_unbox_uint64(v_consumed_4003_);
lean_dec_ref(v_consumed_4003_);
v_res_4005_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3998_, v_inst_3999_, v_stream_4000_, v_drainLimit_4001_, v_closeStream_4002_, v_consumed_boxed_4004_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_object* v_m_4006_, lean_object* v_inst_4007_, lean_object* v_inst_4008_, lean_object* v_stream_4009_, lean_object* v_drainLimit_4010_, lean_object* v_closeStream_4011_, uint64_t v_consumed_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_4007_, v_inst_4008_, v_stream_4009_, v_drainLimit_4010_, v_closeStream_4011_, v_consumed_4012_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___boxed(lean_object* v_m_4014_, lean_object* v_inst_4015_, lean_object* v_inst_4016_, lean_object* v_stream_4017_, lean_object* v_drainLimit_4018_, lean_object* v_closeStream_4019_, lean_object* v_consumed_4020_){
_start:
{
uint64_t v_consumed_boxed_4021_; lean_object* v_res_4022_; 
v_consumed_boxed_4021_ = lean_unbox_uint64(v_consumed_4020_);
lean_dec_ref(v_consumed_4020_);
v_res_4022_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(v_m_4014_, v_inst_4015_, v_inst_4016_, v_stream_4017_, v_drainLimit_4018_, v_closeStream_4019_, v_consumed_boxed_4021_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain___redArg(lean_object* v_inst_4023_, lean_object* v_inst_4024_, lean_object* v_stream_4025_, lean_object* v_drainLimit_4026_, lean_object* v_closeStream_4027_){
_start:
{
uint64_t v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = 0ULL;
v___x_4029_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_4023_, v_inst_4024_, v_stream_4025_, v_drainLimit_4026_, v_closeStream_4027_, v___x_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain(lean_object* v_m_4030_, lean_object* v_inst_4031_, lean_object* v_inst_4032_, lean_object* v_stream_4033_, lean_object* v_drainLimit_4034_, lean_object* v_closeStream_4035_){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = l_Std_Http_Body_Stream_drain___redArg(v_inst_4031_, v_inst_4032_, v_stream_4033_, v_drainLimit_4034_, v_closeStream_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(lean_object* v_chunk_4042_, uint8_t v_incomplete_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; uint8_t v_closed_4048_; 
v___x_4046_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_4044_);
v___x_4047_ = lean_st_ref_get(v___y_4044_);
v_closed_4048_ = lean_ctor_get_uint8(v___x_4047_, sizeof(void*)*6);
if (v_closed_4048_ == 0)
{
lean_object* v_pendingProducer_4049_; lean_object* v_pendingConsumer_4050_; lean_object* v_interestWaiter_4051_; lean_object* v_knownSize_4052_; lean_object* v_pendingIncomplete_4053_; lean_object* v_closeError_4054_; uint8_t v_closeAfterProducer_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4074_; 
v_pendingProducer_4049_ = lean_ctor_get(v___x_4047_, 0);
v_pendingConsumer_4050_ = lean_ctor_get(v___x_4047_, 1);
v_interestWaiter_4051_ = lean_ctor_get(v___x_4047_, 2);
v_knownSize_4052_ = lean_ctor_get(v___x_4047_, 3);
v_pendingIncomplete_4053_ = lean_ctor_get(v___x_4047_, 4);
v_closeError_4054_ = lean_ctor_get(v___x_4047_, 5);
v_closeAfterProducer_4055_ = lean_ctor_get_uint8(v___x_4047_, sizeof(void*)*6 + 1);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4057_ = v___x_4047_;
v_isShared_4058_ = v_isSharedCheck_4074_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_closeError_4054_);
lean_inc(v_pendingIncomplete_4053_);
lean_inc(v_knownSize_4052_);
lean_inc(v_interestWaiter_4051_);
lean_inc(v_pendingConsumer_4050_);
lean_inc(v_pendingProducer_4049_);
lean_dec(v___x_4047_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4074_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4059_; 
v___x_4059_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_push(v_pendingIncomplete_4053_, v_chunk_4042_);
if (v_incomplete_4043_ == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4062_; 
v___x_4060_ = lean_box(0);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 4, v___x_4060_);
v___x_4062_ = v___x_4057_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_pendingProducer_4049_);
lean_ctor_set(v_reuseFailAlloc_4067_, 1, v_pendingConsumer_4050_);
lean_ctor_set(v_reuseFailAlloc_4067_, 2, v_interestWaiter_4051_);
lean_ctor_set(v_reuseFailAlloc_4067_, 3, v_knownSize_4052_);
lean_ctor_set(v_reuseFailAlloc_4067_, 4, v___x_4060_);
lean_ctor_set(v_reuseFailAlloc_4067_, 5, v_closeError_4054_);
lean_ctor_set_uint8(v_reuseFailAlloc_4067_, sizeof(void*)*6, v_closed_4048_);
lean_ctor_set_uint8(v_reuseFailAlloc_4067_, sizeof(void*)*6 + 1, v_closeAfterProducer_4055_);
v___x_4062_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4063_ = lean_st_ref_swap(v___y_4044_, v___x_4062_);
lean_dec(v___x_4063_);
v___x_4064_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(v___x_4059_);
v___x_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
v___x_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
return v___x_4066_;
}
}
else
{
lean_object* v___x_4068_; lean_object* v___x_4070_; 
v___x_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4059_);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 4, v___x_4068_);
v___x_4070_ = v___x_4057_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_pendingProducer_4049_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v_pendingConsumer_4050_);
lean_ctor_set(v_reuseFailAlloc_4073_, 2, v_interestWaiter_4051_);
lean_ctor_set(v_reuseFailAlloc_4073_, 3, v_knownSize_4052_);
lean_ctor_set(v_reuseFailAlloc_4073_, 4, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4073_, 5, v_closeError_4054_);
lean_ctor_set_uint8(v_reuseFailAlloc_4073_, sizeof(void*)*6, v_closed_4048_);
lean_ctor_set_uint8(v_reuseFailAlloc_4073_, sizeof(void*)*6 + 1, v_closeAfterProducer_4055_);
v___x_4070_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_st_ref_swap(v___y_4044_, v___x_4070_);
lean_dec(v___x_4071_);
v___x_4072_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
return v___x_4072_;
}
}
}
}
else
{
lean_object* v___x_4075_; 
lean_dec(v___x_4047_);
lean_dec_ref(v_chunk_4042_);
v___x_4075_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_4075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_chunk_4076_, lean_object* v_incomplete_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
uint8_t v_incomplete_boxed_4080_; lean_object* v_res_4081_; 
v_incomplete_boxed_4080_ = lean_unbox(v_incomplete_4077_);
v_res_4081_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_chunk_4076_, v_incomplete_boxed_4080_, v___y_4078_);
lean_dec(v___y_4078_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_4082_, lean_object* v_chunk_4083_, uint8_t v_incomplete_4084_){
_start:
{
lean_object* v___x_4086_; lean_object* v___f_4087_; lean_object* v___x_4088_; 
v___x_4086_ = lean_box(v_incomplete_4084_);
v___f_4087_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4087_, 0, v_chunk_4083_);
lean_closure_set(v___f_4087_, 1, v___x_4086_);
v___x_4088_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_4082_, v___f_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_4089_, lean_object* v_chunk_4090_, lean_object* v_incomplete_4091_, lean_object* v_a_4092_){
_start:
{
uint8_t v_incomplete_boxed_4093_; lean_object* v_res_4094_; 
v_incomplete_boxed_4093_ = lean_unbox(v_incomplete_4091_);
v_res_4094_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_4089_, v_chunk_4090_, v_incomplete_boxed_4093_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_4101_){
_start:
{
if (lean_obj_tag(v_x_4101_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4111_; 
v_a_4103_ = lean_ctor_get(v_x_4101_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v_x_4101_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4105_ = v_x_4101_;
v_isShared_4106_ = v_isSharedCheck_4111_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v_x_4101_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4111_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
return v___x_4109_;
}
}
}
else
{
lean_object* v___x_4112_; 
lean_dec_ref_known(v_x_4101_, 1);
v___x_4112_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_4112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_4113_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___4116_){
_start:
{
lean_object* v___x_4118_; 
v___x_4118_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___4119_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_4126_, lean_object* v_x_4127_){
_start:
{
if (lean_obj_tag(v_x_4127_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4139_; 
lean_dec_ref(v___f_4126_);
v_a_4131_ = lean_ctor_get(v_x_4127_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v_x_4127_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4133_ = v_x_4127_;
v_isShared_4134_ = v_isSharedCheck_4139_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v_x_4127_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4139_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; 
v___x_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
return v___x_4137_;
}
}
}
else
{
lean_object* v_a_4140_; 
v_a_4140_ = lean_ctor_get(v_x_4127_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v_x_4127_, 1);
if (lean_obj_tag(v_a_4140_) == 1)
{
lean_object* v_val_4141_; uint8_t v___x_4142_; 
v_val_4141_ = lean_ctor_get(v_a_4140_, 0);
lean_inc(v_val_4141_);
lean_dec_ref_known(v_a_4140_, 1);
v___x_4142_ = lean_unbox(v_val_4141_);
lean_dec(v_val_4141_);
if (v___x_4142_ == 1)
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = lean_box(0);
v___x_4144_ = lean_apply_2(v___f_4126_, v___x_4143_, lean_box(0));
return v___x_4144_;
}
else
{
lean_dec_ref(v___f_4126_);
goto v___jp_4129_;
}
}
else
{
lean_dec(v_a_4140_);
lean_dec_ref(v___f_4126_);
goto v___jp_4129_;
}
}
v___jp_4129_:
{
lean_object* v___x_4130_; 
v___x_4130_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_4130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_4145_, lean_object* v_x_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_4145_, v_x_4146_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_4149_){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4150_, 0, v_a_4149_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_4151_, lean_object* v_x_4152_){
_start:
{
if (lean_obj_tag(v_x_4152_) == 0)
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4162_; 
v_a_4154_ = lean_ctor_get(v_x_4152_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_x_4152_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4156_ = v_x_4152_;
v_isShared_4157_ = v_isSharedCheck_4162_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v_x_4152_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4162_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
lean_object* v___x_4160_; 
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
return v___x_4160_;
}
}
}
else
{
lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4173_; 
v_isSharedCheck_4173_ = !lean_is_exclusive(v_x_4152_);
if (v_isSharedCheck_4173_ == 0)
{
lean_object* v_unused_4174_; 
v_unused_4174_ = lean_ctor_get(v_x_4152_, 0);
lean_dec(v_unused_4174_);
v___x_4164_ = v_x_4152_;
v_isShared_4165_ = v_isSharedCheck_4173_;
goto v_resetjp_4163_;
}
else
{
lean_dec(v_x_4152_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4173_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4166_ = lean_box(v___x_4151_);
v___x_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 0, v___x_4167_);
v___x_4169_ = v___x_4164_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
v___x_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
return v___x_4171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_4175_, lean_object* v_x_4176_, lean_object* v___y_4177_){
_start:
{
uint8_t v___x_5132__boxed_4178_; lean_object* v_res_4179_; 
v___x_5132__boxed_4178_ = lean_unbox(v___x_4175_);
v_res_4179_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5132__boxed_4178_, v_x_4176_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_4180_, lean_object* v_x_4181_){
_start:
{
if (lean_obj_tag(v_x_4181_) == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4191_; 
v_a_4183_ = lean_ctor_get(v_x_4181_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v_x_4181_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4185_ = v_x_4181_;
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v_x_4181_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4189_; 
v___x_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
return v___x_4189_;
}
}
}
else
{
lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4202_; 
v_isSharedCheck_4202_ = !lean_is_exclusive(v_x_4181_);
if (v_isSharedCheck_4202_ == 0)
{
lean_object* v_unused_4203_; 
v_unused_4203_ = lean_ctor_get(v_x_4181_, 0);
lean_dec(v_unused_4203_);
v___x_4193_ = v_x_4181_;
v_isShared_4194_ = v_isSharedCheck_4202_;
goto v_resetjp_4192_;
}
else
{
lean_dec(v_x_4181_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4202_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4198_; 
v___x_4195_ = lean_box(v_a_4180_);
v___x_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 0, v___x_4196_);
v___x_4198_ = v___x_4193_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
return v___x_4200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_4204_, lean_object* v_x_4205_, lean_object* v___y_4206_){
_start:
{
uint8_t v_a_5184__boxed_4207_; lean_object* v_res_4208_; 
v_a_5184__boxed_4207_ = lean_unbox(v_a_4204_);
v_res_4208_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5184__boxed_4207_, v_x_4205_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_4209_, lean_object* v_interestWaiter_4210_, uint8_t v_closed_4211_, lean_object* v_knownSize_4212_, lean_object* v_pendingIncomplete_4213_, lean_object* v_closeError_4214_, uint8_t v_closeAfterProducer_4215_, lean_object* v___y_4216_, lean_object* v_chunk_4217_, lean_object* v___f_4218_, lean_object* v_x_4219_){
_start:
{
if (lean_obj_tag(v_x_4219_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4229_; 
lean_dec_ref(v___f_4218_);
lean_dec(v_closeError_4214_);
lean_dec(v_pendingIncomplete_4213_);
lean_dec(v_knownSize_4212_);
lean_dec(v_interestWaiter_4210_);
lean_dec(v_pendingProducer_4209_);
v_a_4221_ = lean_ctor_get(v_x_4219_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v_x_4219_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4223_ = v_x_4219_;
v_isShared_4224_ = v_isSharedCheck_4229_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v_x_4219_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4229_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
return v___x_4227_;
}
}
}
else
{
lean_object* v_a_4230_; uint8_t v___x_4231_; 
v_a_4230_ = lean_ctor_get(v_x_4219_, 0);
lean_inc(v_a_4230_);
lean_dec_ref_known(v_x_4219_, 1);
v___x_4231_ = lean_unbox(v_a_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___f_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; lean_object* v___x_4239_; 
lean_dec_ref(v___f_4218_);
lean_inc(v_a_4230_);
v___f_4232_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4232_, 0, v_a_4230_);
v___x_4233_ = lean_box(0);
v___x_4234_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_4234_, 0, v_pendingProducer_4209_);
lean_ctor_set(v___x_4234_, 1, v___x_4233_);
lean_ctor_set(v___x_4234_, 2, v_interestWaiter_4210_);
lean_ctor_set(v___x_4234_, 3, v_knownSize_4212_);
lean_ctor_set(v___x_4234_, 4, v_pendingIncomplete_4213_);
lean_ctor_set(v___x_4234_, 5, v_closeError_4214_);
lean_ctor_set_uint8(v___x_4234_, sizeof(void*)*6, v_closed_4211_);
lean_ctor_set_uint8(v___x_4234_, sizeof(void*)*6 + 1, v_closeAfterProducer_4215_);
v___x_4235_ = lean_unsigned_to_nat(0u);
v___x_4236_ = lean_st_ref_swap(v___y_4216_, v___x_4234_);
lean_dec(v___x_4236_);
v___x_4237_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4238_ = lean_unbox(v_a_4230_);
lean_dec(v_a_4230_);
v___x_4239_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4235_, v___x_4238_, v___x_4237_, v___f_4232_);
return v___x_4239_;
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_dec(v_a_4230_);
v___x_4240_ = lean_box(0);
v___x_4241_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_4212_, v_chunk_4217_);
v___x_4242_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_4242_, 0, v_pendingProducer_4209_);
lean_ctor_set(v___x_4242_, 1, v___x_4240_);
lean_ctor_set(v___x_4242_, 2, v_interestWaiter_4210_);
lean_ctor_set(v___x_4242_, 3, v___x_4241_);
lean_ctor_set(v___x_4242_, 4, v_pendingIncomplete_4213_);
lean_ctor_set(v___x_4242_, 5, v_closeError_4214_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*6, v_closed_4211_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*6 + 1, v_closeAfterProducer_4215_);
v___x_4243_ = lean_unsigned_to_nat(0u);
v___x_4244_ = lean_st_ref_swap(v___y_4216_, v___x_4242_);
lean_dec(v___x_4244_);
v___x_4245_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4246_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4243_, v_closed_4211_, v___x_4245_, v___f_4218_);
return v___x_4246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_4247_, lean_object* v_interestWaiter_4248_, lean_object* v_closed_4249_, lean_object* v_knownSize_4250_, lean_object* v_pendingIncomplete_4251_, lean_object* v_closeError_4252_, lean_object* v_closeAfterProducer_4253_, lean_object* v___y_4254_, lean_object* v_chunk_4255_, lean_object* v___f_4256_, lean_object* v_x_4257_, lean_object* v___y_4258_){
_start:
{
uint8_t v_closed_boxed_4259_; uint8_t v_closeAfterProducer_boxed_4260_; lean_object* v_res_4261_; 
v_closed_boxed_4259_ = lean_unbox(v_closed_4249_);
v_closeAfterProducer_boxed_4260_ = lean_unbox(v_closeAfterProducer_4253_);
v_res_4261_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_4247_, v_interestWaiter_4248_, v_closed_boxed_4259_, v_knownSize_4250_, v_pendingIncomplete_4251_, v_closeError_4252_, v_closeAfterProducer_boxed_4260_, v___y_4254_, v_chunk_4255_, v___f_4256_, v_x_4257_);
lean_dec_ref(v_chunk_4255_);
lean_dec(v___y_4254_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v___y_4280_, lean_object* v_chunk_4281_, lean_object* v_a_4282_, lean_object* v___f_4283_, lean_object* v_x_4284_){
_start:
{
if (lean_obj_tag(v_x_4284_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4294_; 
lean_dec_ref(v___f_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_chunk_4281_);
v_a_4286_ = lean_ctor_get(v_x_4284_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v_x_4284_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4288_ = v_x_4284_;
v_isShared_4289_ = v_isSharedCheck_4294_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v_x_4284_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4294_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4291_);
return v___x_4292_;
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4351_; 
v_a_4295_ = lean_ctor_get(v_x_4284_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v_x_4284_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4297_ = v_x_4284_;
v_isShared_4298_ = v_isSharedCheck_4351_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v_x_4284_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4351_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
uint8_t v_closed_4299_; 
v_closed_4299_ = lean_ctor_get_uint8(v_a_4295_, sizeof(void*)*6);
if (v_closed_4299_ == 0)
{
lean_object* v_pendingConsumer_4300_; 
v_pendingConsumer_4300_ = lean_ctor_get(v_a_4295_, 1);
lean_inc(v_pendingConsumer_4300_);
if (lean_obj_tag(v_pendingConsumer_4300_) == 1)
{
lean_object* v_pendingProducer_4301_; lean_object* v_interestWaiter_4302_; lean_object* v_knownSize_4303_; lean_object* v_pendingIncomplete_4304_; lean_object* v_closeError_4305_; uint8_t v_closeAfterProducer_4306_; lean_object* v_val_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v___f_4283_);
lean_dec(v_a_4282_);
v_pendingProducer_4301_ = lean_ctor_get(v_a_4295_, 0);
lean_inc(v_pendingProducer_4301_);
v_interestWaiter_4302_ = lean_ctor_get(v_a_4295_, 2);
lean_inc(v_interestWaiter_4302_);
v_knownSize_4303_ = lean_ctor_get(v_a_4295_, 3);
lean_inc(v_knownSize_4303_);
v_pendingIncomplete_4304_ = lean_ctor_get(v_a_4295_, 4);
lean_inc(v_pendingIncomplete_4304_);
v_closeError_4305_ = lean_ctor_get(v_a_4295_, 5);
lean_inc(v_closeError_4305_);
v_closeAfterProducer_4306_ = lean_ctor_get_uint8(v_a_4295_, sizeof(void*)*6 + 1);
lean_dec(v_a_4295_);
v_val_4307_ = lean_ctor_get(v_pendingConsumer_4300_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_pendingConsumer_4300_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4309_ = v_pendingConsumer_4300_;
v_isShared_4310_ = v_isSharedCheck_4327_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_val_4307_);
lean_dec(v_pendingConsumer_4300_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4327_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___f_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___f_4314_; lean_object* v___x_4316_; 
v___f_4311_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_4312_ = lean_box(v_closed_4299_);
v___x_4313_ = lean_box(v_closeAfterProducer_4306_);
lean_inc_ref(v_chunk_4281_);
lean_inc(v___y_4280_);
v___f_4314_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 12, 10);
lean_closure_set(v___f_4314_, 0, v_pendingProducer_4301_);
lean_closure_set(v___f_4314_, 1, v_interestWaiter_4302_);
lean_closure_set(v___f_4314_, 2, v___x_4312_);
lean_closure_set(v___f_4314_, 3, v_knownSize_4303_);
lean_closure_set(v___f_4314_, 4, v_pendingIncomplete_4304_);
lean_closure_set(v___f_4314_, 5, v_closeError_4305_);
lean_closure_set(v___f_4314_, 6, v___x_4313_);
lean_closure_set(v___f_4314_, 7, v___y_4280_);
lean_closure_set(v___f_4314_, 8, v_chunk_4281_);
lean_closure_set(v___f_4314_, 9, v___f_4311_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 0, v_chunk_4281_);
v___x_4316_ = v___x_4309_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_chunk_4281_);
v___x_4316_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
lean_object* v___x_4318_; 
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4316_);
v___x_4318_ = v___x_4297_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
lean_object* v___x_4319_; uint8_t v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4319_ = lean_unsigned_to_nat(0u);
v___x_4320_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_4307_, v___x_4318_);
lean_dec(v_val_4307_);
v___x_4321_ = lean_box(v___x_4320_);
v___x_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
v___x_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
v___x_4324_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4319_, v_closed_4299_, v___x_4323_, v___f_4314_);
return v___x_4324_;
}
}
}
}
else
{
lean_object* v_pendingProducer_4328_; 
lean_del_object(v___x_4297_);
v_pendingProducer_4328_ = lean_ctor_get(v_a_4295_, 0);
if (lean_obj_tag(v_pendingProducer_4328_) == 0)
{
lean_object* v_interestWaiter_4329_; lean_object* v_knownSize_4330_; lean_object* v_pendingIncomplete_4331_; lean_object* v_closeError_4332_; uint8_t v_closeAfterProducer_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4346_; 
v_interestWaiter_4329_ = lean_ctor_get(v_a_4295_, 2);
v_knownSize_4330_ = lean_ctor_get(v_a_4295_, 3);
v_pendingIncomplete_4331_ = lean_ctor_get(v_a_4295_, 4);
v_closeError_4332_ = lean_ctor_get(v_a_4295_, 5);
v_closeAfterProducer_4333_ = lean_ctor_get_uint8(v_a_4295_, sizeof(void*)*6 + 1);
v_isSharedCheck_4346_ = !lean_is_exclusive(v_a_4295_);
if (v_isSharedCheck_4346_ == 0)
{
lean_object* v_unused_4347_; lean_object* v_unused_4348_; 
v_unused_4347_ = lean_ctor_get(v_a_4295_, 1);
lean_dec(v_unused_4347_);
v_unused_4348_ = lean_ctor_get(v_a_4295_, 0);
lean_dec(v_unused_4348_);
v___x_4335_ = v_a_4295_;
v_isShared_4336_ = v_isSharedCheck_4346_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_closeError_4332_);
lean_inc(v_pendingIncomplete_4331_);
lean_inc(v_knownSize_4330_);
lean_inc(v_interestWaiter_4329_);
lean_dec(v_a_4295_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4346_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4340_; 
v___x_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4337_, 0, v_chunk_4281_);
lean_ctor_set(v___x_4337_, 1, v_a_4282_);
v___x_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v___x_4338_);
v___x_4340_ = v___x_4335_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4338_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_pendingConsumer_4300_);
lean_ctor_set(v_reuseFailAlloc_4345_, 2, v_interestWaiter_4329_);
lean_ctor_set(v_reuseFailAlloc_4345_, 3, v_knownSize_4330_);
lean_ctor_set(v_reuseFailAlloc_4345_, 4, v_pendingIncomplete_4331_);
lean_ctor_set(v_reuseFailAlloc_4345_, 5, v_closeError_4332_);
lean_ctor_set_uint8(v_reuseFailAlloc_4345_, sizeof(void*)*6, v_closed_4299_);
lean_ctor_set_uint8(v_reuseFailAlloc_4345_, sizeof(void*)*6 + 1, v_closeAfterProducer_4333_);
v___x_4340_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4341_ = lean_unsigned_to_nat(0u);
v___x_4342_ = lean_st_ref_swap(v___y_4280_, v___x_4340_);
lean_dec(v___x_4342_);
v___x_4343_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4344_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4341_, v_closed_4299_, v___x_4343_, v___f_4283_);
return v___x_4344_;
}
}
}
else
{
lean_object* v___x_4349_; 
lean_dec(v_pendingConsumer_4300_);
lean_dec(v_a_4295_);
lean_dec_ref(v___f_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_chunk_4281_);
v___x_4349_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_4349_;
}
}
}
else
{
lean_object* v___x_4350_; 
lean_del_object(v___x_4297_);
lean_dec(v_a_4295_);
lean_dec_ref(v___f_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_chunk_4281_);
v___x_4350_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_4350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v___y_4352_, lean_object* v_chunk_4353_, lean_object* v_a_4354_, lean_object* v___f_4355_, lean_object* v_x_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v___y_4352_, v_chunk_4353_, v_a_4354_, v___f_4355_, v_x_4356_);
lean_dec(v___y_4352_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_4359_, lean_object* v___f_4360_, lean_object* v_x_4361_){
_start:
{
if (lean_obj_tag(v_x_4361_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4371_; 
lean_dec_ref(v___f_4360_);
v_a_4363_ = lean_ctor_get(v_x_4361_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v_x_4361_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4365_ = v_x_4361_;
v_isShared_4366_ = v_isSharedCheck_4371_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v_x_4361_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4371_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
lean_object* v___x_4369_; 
v___x_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4368_);
return v___x_4369_;
}
}
}
else
{
lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4383_; 
v_isSharedCheck_4383_ = !lean_is_exclusive(v_x_4361_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v_x_4361_, 0);
lean_dec(v_unused_4384_);
v___x_4373_ = v_x_4361_;
v_isShared_4374_ = v_isSharedCheck_4383_;
goto v_resetjp_4372_;
}
else
{
lean_dec(v_x_4361_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4383_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4375_; uint8_t v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4379_; 
v___x_4375_ = lean_unsigned_to_nat(0u);
v___x_4376_ = 0;
v___x_4377_ = lean_st_ref_get(v___y_4359_);
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 0, v___x_4377_);
v___x_4379_ = v___x_4373_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4377_);
v___x_4379_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
v___x_4381_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4375_, v___x_4376_, v___x_4380_, v___f_4360_);
return v___x_4381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_4385_, lean_object* v___f_4386_, lean_object* v_x_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_4385_, v___f_4386_, v_x_4387_);
lean_dec(v___y_4385_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_4390_, lean_object* v_a_4391_, lean_object* v___f_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v___f_4395_; lean_object* v___f_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
lean_inc_n(v___y_4393_, 2);
v___f_4395_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4395_, 0, v___y_4393_);
lean_closure_set(v___f_4395_, 1, v_chunk_4390_);
lean_closure_set(v___f_4395_, 2, v_a_4391_);
lean_closure_set(v___f_4395_, 3, v___f_4392_);
v___f_4396_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_4396_, 0, v___y_4393_);
lean_closure_set(v___f_4396_, 1, v___f_4395_);
v___x_4397_ = lean_unsigned_to_nat(0u);
v___x_4398_ = 0;
v___x_4399_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4393_);
v___x_4400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4397_, v___x_4398_, v___x_4399_, v___f_4396_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_4401_, lean_object* v_a_4402_, lean_object* v___f_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_4401_, v_a_4402_, v___f_4403_, v___y_4404_);
lean_dec(v___y_4404_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_4412_, lean_object* v___f_4413_, lean_object* v___f_4414_, lean_object* v_stream_4415_, lean_object* v_chunk_4416_, lean_object* v___f_4417_, lean_object* v_x_4418_){
_start:
{
if (lean_obj_tag(v_x_4418_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4428_; 
lean_dec_ref(v___f_4417_);
lean_dec_ref(v_chunk_4416_);
lean_dec_ref(v_stream_4415_);
lean_dec_ref(v___f_4414_);
lean_dec_ref(v___f_4413_);
v_a_4420_ = lean_ctor_get(v_x_4418_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_x_4418_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4422_ = v_x_4418_;
v_isShared_4423_ = v_isSharedCheck_4428_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v_x_4418_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4428_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
lean_object* v___x_4426_; 
v___x_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4425_);
return v___x_4426_;
}
}
}
else
{
lean_object* v_a_4429_; 
v_a_4429_ = lean_ctor_get(v_x_4418_, 0);
lean_inc(v_a_4429_);
lean_dec_ref_known(v_x_4418_, 1);
if (lean_obj_tag(v_a_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4438_; 
lean_dec_ref(v___f_4417_);
lean_dec_ref(v_chunk_4416_);
lean_dec_ref(v_stream_4415_);
lean_dec_ref(v___f_4414_);
lean_dec_ref(v___f_4413_);
v_a_4430_ = lean_ctor_get(v_a_4429_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v_a_4429_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4432_ = v_a_4429_;
v_isShared_4433_ = v_isSharedCheck_4438_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v_a_4429_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4438_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
lean_object* v___x_4436_; 
v___x_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
return v___x_4436_;
}
}
}
else
{
lean_object* v_a_4439_; 
v_a_4439_ = lean_ctor_get(v_a_4429_, 0);
lean_inc(v_a_4439_);
lean_dec_ref_known(v_a_4429_, 1);
if (lean_obj_tag(v_a_4439_) == 0)
{
lean_object* v___x_4440_; lean_object* v___x_4441_; uint8_t v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
lean_dec_ref(v___f_4417_);
lean_dec_ref(v_chunk_4416_);
lean_dec_ref(v_stream_4415_);
v___x_4440_ = lean_io_promise_result_opt(v_a_4412_);
v___x_4441_ = lean_unsigned_to_nat(0u);
v___x_4442_ = 0;
v___x_4443_ = lean_task_map(v___f_4413_, v___x_4440_, v___x_4441_, v___x_4442_);
v___x_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
v___x_4445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4441_, v___x_4442_, v___x_4444_, v___f_4414_);
return v___x_4445_;
}
else
{
lean_object* v_val_4446_; uint8_t v___x_4447_; 
lean_dec_ref(v___f_4414_);
lean_dec_ref(v___f_4413_);
v_val_4446_ = lean_ctor_get(v_a_4439_, 0);
lean_inc(v_val_4446_);
lean_dec_ref_known(v_a_4439_, 1);
v___x_4447_ = lean_unbox(v_val_4446_);
lean_dec(v_val_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; 
lean_dec_ref(v___f_4417_);
v___x_4448_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_4415_, v_chunk_4416_);
return v___x_4448_;
}
else
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_dec_ref(v_chunk_4416_);
lean_dec_ref(v_stream_4415_);
v___x_4449_ = lean_box(0);
v___x_4450_ = lean_apply_2(v___f_4417_, v___x_4449_, lean_box(0));
return v___x_4450_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_4451_, lean_object* v___f_4452_, lean_object* v___f_4453_, lean_object* v_stream_4454_, lean_object* v_chunk_4455_, lean_object* v___f_4456_, lean_object* v_x_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_4451_, v___f_4452_, v___f_4453_, v_stream_4454_, v_chunk_4455_, v___f_4456_, v_x_4457_);
lean_dec(v_a_4451_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_4460_, lean_object* v___f_4461_, lean_object* v___f_4462_, lean_object* v___f_4463_, lean_object* v_stream_4464_, lean_object* v___f_4465_, lean_object* v_x_4466_){
_start:
{
if (lean_obj_tag(v_x_4466_) == 0)
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4476_; 
lean_dec_ref(v___f_4465_);
lean_dec_ref(v_stream_4464_);
lean_dec_ref(v___f_4463_);
lean_dec_ref(v___f_4462_);
lean_dec_ref(v___f_4461_);
lean_dec_ref(v_chunk_4460_);
v_a_4468_ = lean_ctor_get(v_x_4466_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_x_4466_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4470_ = v_x_4466_;
v_isShared_4471_ = v_isSharedCheck_4476_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v_x_4466_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4476_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
lean_object* v___x_4474_; 
v___x_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4473_);
return v___x_4474_;
}
}
}
else
{
lean_object* v_a_4477_; lean_object* v___f_4478_; lean_object* v___f_4479_; lean_object* v___x_4480_; uint8_t v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v_a_4477_ = lean_ctor_get(v_x_4466_, 0);
lean_inc_n(v_a_4477_, 2);
lean_dec_ref_known(v_x_4466_, 1);
lean_inc_ref(v_chunk_4460_);
v___f_4478_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4478_, 0, v_chunk_4460_);
lean_closure_set(v___f_4478_, 1, v_a_4477_);
lean_closure_set(v___f_4478_, 2, v___f_4461_);
lean_inc_ref(v_stream_4464_);
v___f_4479_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_4479_, 0, v_a_4477_);
lean_closure_set(v___f_4479_, 1, v___f_4462_);
lean_closure_set(v___f_4479_, 2, v___f_4463_);
lean_closure_set(v___f_4479_, 3, v_stream_4464_);
lean_closure_set(v___f_4479_, 4, v_chunk_4460_);
lean_closure_set(v___f_4479_, 5, v___f_4465_);
v___x_4480_ = lean_unsigned_to_nat(0u);
v___x_4481_ = 0;
v___x_4482_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_4464_, v___f_4478_);
v___x_4483_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4480_, v___x_4481_, v___x_4482_, v___f_4479_);
return v___x_4483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_4484_, lean_object* v___f_4485_, lean_object* v___f_4486_, lean_object* v___f_4487_, lean_object* v_stream_4488_, lean_object* v___f_4489_, lean_object* v_x_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_4484_, v___f_4485_, v___f_4486_, v___f_4487_, v_stream_4488_, v___f_4489_, v_x_4490_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_4493_, lean_object* v_chunk_4494_){
_start:
{
lean_object* v___f_4496_; lean_object* v___f_4497_; lean_object* v___f_4498_; lean_object* v___f_4499_; lean_object* v___f_4500_; lean_object* v___x_4501_; uint8_t v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___f_4496_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_4497_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_4498_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_4499_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_4500_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_4500_, 0, v_chunk_4494_);
lean_closure_set(v___f_4500_, 1, v___f_4496_);
lean_closure_set(v___f_4500_, 2, v___f_4499_);
lean_closure_set(v___f_4500_, 3, v___f_4498_);
lean_closure_set(v___f_4500_, 4, v_stream_4493_);
lean_closure_set(v___f_4500_, 5, v___f_4497_);
v___x_4501_ = lean_unsigned_to_nat(0u);
v___x_4502_ = 0;
v___x_4503_ = lean_io_promise_new();
v___x_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
v___x_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
v___x_4506_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4501_, v___x_4502_, v___x_4505_, v___f_4500_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_4507_, lean_object* v_chunk_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_4507_, v_chunk_4508_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_4511_, lean_object* v_x_4512_){
_start:
{
if (lean_obj_tag(v_x_4512_) == 0)
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4522_; 
lean_dec_ref(v_stream_4511_);
v_a_4514_ = lean_ctor_get(v_x_4512_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v_x_4512_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4516_ = v_x_4512_;
v_isShared_4517_ = v_isSharedCheck_4522_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v_x_4512_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4522_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
lean_object* v___x_4520_; 
v___x_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
return v___x_4520_;
}
}
}
else
{
lean_object* v_a_4523_; 
v_a_4523_ = lean_ctor_get(v_x_4512_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v_x_4512_, 1);
if (lean_obj_tag(v_a_4523_) == 0)
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4532_; 
lean_dec_ref(v_stream_4511_);
v_a_4524_ = lean_ctor_get(v_a_4523_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v_a_4523_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4526_ = v_a_4523_;
v_isShared_4527_ = v_isSharedCheck_4532_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v_a_4523_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4532_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4524_);
v___x_4529_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
lean_object* v___x_4530_; 
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
return v___x_4530_;
}
}
}
else
{
lean_object* v_a_4533_; 
v_a_4533_ = lean_ctor_get(v_a_4523_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v_a_4523_, 1);
if (lean_obj_tag(v_a_4533_) == 0)
{
lean_object* v___x_4534_; 
lean_dec_ref(v_stream_4511_);
v___x_4534_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4534_;
}
else
{
lean_object* v_val_4535_; lean_object* v_data_4536_; lean_object* v_extensions_4537_; uint8_t v___x_4538_; 
v_val_4535_ = lean_ctor_get(v_a_4533_, 0);
lean_inc(v_val_4535_);
lean_dec_ref_known(v_a_4533_, 1);
v_data_4536_ = lean_ctor_get(v_val_4535_, 0);
v_extensions_4537_ = lean_ctor_get(v_val_4535_, 1);
v___x_4538_ = l_ByteArray_isEmpty(v_data_4536_);
if (v___x_4538_ == 0)
{
lean_object* v___x_4539_; 
v___x_4539_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_4511_, v_val_4535_);
return v___x_4539_;
}
else
{
lean_object* v___x_4540_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4540_ = lean_array_get_size(v_extensions_4537_);
v___x_4541_ = lean_unsigned_to_nat(0u);
v___x_4542_ = lean_nat_dec_eq(v___x_4540_, v___x_4541_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; 
v___x_4543_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_4511_, v_val_4535_);
return v___x_4543_;
}
else
{
lean_object* v___x_4544_; 
lean_dec(v_val_4535_);
lean_dec_ref(v_stream_4511_);
v___x_4544_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4544_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object* v_stream_4545_, lean_object* v_x_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_4545_, v_x_4546_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object* v_stream_4549_, lean_object* v_chunk_4550_, uint8_t v_incomplete_4551_){
_start:
{
lean_object* v___f_4553_; lean_object* v___x_4554_; uint8_t v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
lean_inc_ref(v_stream_4549_);
v___f_4553_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4553_, 0, v_stream_4549_);
v___x_4554_ = lean_unsigned_to_nat(0u);
v___x_4555_ = 0;
v___x_4556_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_4549_, v_chunk_4550_, v_incomplete_4551_);
v___x_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
v___x_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
v___x_4559_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4554_, v___x_4555_, v___x_4558_, v___f_4553_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object* v_stream_4560_, lean_object* v_chunk_4561_, lean_object* v_incomplete_4562_, lean_object* v_a_4563_){
_start:
{
uint8_t v_incomplete_boxed_4564_; lean_object* v_res_4565_; 
v_incomplete_boxed_4564_ = lean_unbox(v_incomplete_4562_);
v_res_4565_ = l_Std_Http_Body_Stream_send(v_stream_4560_, v_chunk_4561_, v_incomplete_boxed_4564_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__0(lean_object* v_x_4570_){
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
lean_object* v___x_4581_; 
lean_dec_ref_known(v_x_4570_, 1);
v___x_4581_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___lam__0___closed__1));
return v___x_4581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__0___boxed(lean_object* v_x_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Std_Http_Body_Stream_offer___lam__0(v_x_4582_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__1(lean_object* v_____r_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v___x_4588_; 
v___x_4588_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___lam__0___closed__1));
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__1___boxed(lean_object* v_____r_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Std_Http_Body_Stream_offer___lam__1(v_____r_4589_, v___y_4590_);
lean_dec(v___y_4590_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__3(lean_object* v_x_4593_){
_start:
{
if (lean_obj_tag(v_x_4593_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4603_; 
v_a_4595_ = lean_ctor_get(v_x_4593_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v_x_4593_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4597_ = v_x_4593_;
v_isShared_4598_ = v_isSharedCheck_4603_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v_x_4593_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4603_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
lean_object* v___x_4601_; 
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
return v___x_4601_;
}
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4620_; 
v_a_4604_ = lean_ctor_get(v_x_4593_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v_x_4593_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4606_ = v_x_4593_;
v_isShared_4607_ = v_isSharedCheck_4620_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v_x_4593_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4620_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
if (lean_obj_tag(v_a_4604_) == 1)
{
lean_object* v_val_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4618_; 
v_val_4608_ = lean_ctor_get(v_a_4604_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v_a_4604_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4610_ = v_a_4604_;
v_isShared_4611_ = v_isSharedCheck_4618_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_val_4608_);
lean_dec(v_a_4604_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4618_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4607_ == 0)
{
lean_ctor_set_tag(v___x_4606_, 0);
lean_ctor_set(v___x_4606_, 0, v_val_4608_);
v___x_4613_ = v___x_4606_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_val_4608_);
v___x_4613_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
lean_object* v___x_4615_; 
if (v_isShared_4611_ == 0)
{
lean_ctor_set_tag(v___x_4610_, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4613_);
v___x_4615_ = v___x_4610_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4613_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
}
else
{
lean_object* v___x_4619_; 
lean_del_object(v___x_4606_);
lean_dec(v_a_4604_);
v___x_4619_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__3___boxed(lean_object* v_x_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_Std_Http_Body_Stream_offer___lam__3(v_x_4621_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__2(lean_object* v___f_4624_, lean_object* v___y_4625_, lean_object* v_x_4626_){
_start:
{
if (lean_obj_tag(v_x_4626_) == 0)
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4636_; 
lean_dec_ref(v___f_4624_);
v_a_4628_ = lean_ctor_get(v_x_4626_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v_x_4626_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4630_ = v_x_4626_;
v_isShared_4631_ = v_isSharedCheck_4636_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v_x_4626_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4636_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
lean_object* v___x_4634_; 
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
return v___x_4634_;
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4638_; 
v_a_4637_ = lean_ctor_get(v_x_4626_, 0);
lean_inc(v_a_4637_);
lean_dec_ref_known(v_x_4626_, 1);
lean_inc(v___y_4625_);
v___x_4638_ = lean_apply_3(v___f_4624_, v_a_4637_, v___y_4625_, lean_box(0));
return v___x_4638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__2___boxed(lean_object* v___f_4639_, lean_object* v___y_4640_, lean_object* v_x_4641_, lean_object* v___y_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l_Std_Http_Body_Stream_offer___lam__2(v___f_4639_, v___y_4640_, v_x_4641_);
lean_dec(v___y_4640_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__5(lean_object* v_toSend_4650_, lean_object* v_a_4651_, uint8_t v_closeAfter_4652_, lean_object* v___y_4653_, uint8_t v___y_4654_, lean_object* v___f_4655_, lean_object* v_x_4656_){
_start:
{
if (lean_obj_tag(v_x_4656_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4666_; 
lean_dec_ref(v___f_4655_);
lean_dec(v_a_4651_);
lean_dec_ref(v_toSend_4650_);
v_a_4658_ = lean_ctor_get(v_x_4656_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v_x_4656_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4660_ = v_x_4656_;
v_isShared_4661_ = v_isSharedCheck_4666_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v_x_4656_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4666_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
lean_object* v___x_4664_; 
v___x_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4663_);
return v___x_4664_;
}
}
}
else
{
lean_object* v_a_4667_; lean_object* v_pendingProducer_4668_; 
v_a_4667_ = lean_ctor_get(v_x_4656_, 0);
lean_inc(v_a_4667_);
lean_dec_ref_known(v_x_4656_, 1);
v_pendingProducer_4668_ = lean_ctor_get(v_a_4667_, 0);
if (lean_obj_tag(v_pendingProducer_4668_) == 0)
{
lean_object* v_pendingConsumer_4669_; lean_object* v_interestWaiter_4670_; uint8_t v_closed_4671_; lean_object* v_knownSize_4672_; lean_object* v_pendingIncomplete_4673_; lean_object* v_closeError_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4687_; 
v_pendingConsumer_4669_ = lean_ctor_get(v_a_4667_, 1);
v_interestWaiter_4670_ = lean_ctor_get(v_a_4667_, 2);
v_closed_4671_ = lean_ctor_get_uint8(v_a_4667_, sizeof(void*)*6);
v_knownSize_4672_ = lean_ctor_get(v_a_4667_, 3);
v_pendingIncomplete_4673_ = lean_ctor_get(v_a_4667_, 4);
v_closeError_4674_ = lean_ctor_get(v_a_4667_, 5);
v_isSharedCheck_4687_ = !lean_is_exclusive(v_a_4667_);
if (v_isSharedCheck_4687_ == 0)
{
lean_object* v_unused_4688_; 
v_unused_4688_ = lean_ctor_get(v_a_4667_, 0);
lean_dec(v_unused_4688_);
v___x_4676_ = v_a_4667_;
v_isShared_4677_ = v_isSharedCheck_4687_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_closeError_4674_);
lean_inc(v_pendingIncomplete_4673_);
lean_inc(v_knownSize_4672_);
lean_inc(v_interestWaiter_4670_);
lean_inc(v_pendingConsumer_4669_);
lean_dec(v_a_4667_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4687_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4681_; 
v___x_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4678_, 0, v_toSend_4650_);
lean_ctor_set(v___x_4678_, 1, v_a_4651_);
v___x_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 0, v___x_4679_);
v___x_4681_ = v___x_4676_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4679_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v_pendingConsumer_4669_);
lean_ctor_set(v_reuseFailAlloc_4686_, 2, v_interestWaiter_4670_);
lean_ctor_set(v_reuseFailAlloc_4686_, 3, v_knownSize_4672_);
lean_ctor_set(v_reuseFailAlloc_4686_, 4, v_pendingIncomplete_4673_);
lean_ctor_set(v_reuseFailAlloc_4686_, 5, v_closeError_4674_);
lean_ctor_set_uint8(v_reuseFailAlloc_4686_, sizeof(void*)*6, v_closed_4671_);
v___x_4681_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
lean_ctor_set_uint8(v___x_4681_, sizeof(void*)*6 + 1, v_closeAfter_4652_);
v___x_4682_ = lean_unsigned_to_nat(0u);
v___x_4683_ = lean_st_ref_swap(v___y_4653_, v___x_4681_);
lean_dec(v___x_4683_);
v___x_4684_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4685_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4682_, v___y_4654_, v___x_4684_, v___f_4655_);
return v___x_4685_;
}
}
}
else
{
lean_object* v___x_4689_; 
lean_dec(v_a_4667_);
lean_dec_ref(v___f_4655_);
lean_dec(v_a_4651_);
lean_dec_ref(v_toSend_4650_);
v___x_4689_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___lam__5___closed__2));
return v___x_4689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__5___boxed(lean_object* v_toSend_4690_, lean_object* v_a_4691_, lean_object* v_closeAfter_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___f_4695_, lean_object* v_x_4696_, lean_object* v___y_4697_){
_start:
{
uint8_t v_closeAfter_boxed_4698_; uint8_t v___y_8107__boxed_4699_; lean_object* v_res_4700_; 
v_closeAfter_boxed_4698_ = lean_unbox(v_closeAfter_4692_);
v___y_8107__boxed_4699_ = lean_unbox(v___y_4694_);
v_res_4700_ = l_Std_Http_Body_Stream_offer___lam__5(v_toSend_4690_, v_a_4691_, v_closeAfter_boxed_4698_, v___y_4693_, v___y_8107__boxed_4699_, v___f_4695_, v_x_4696_);
lean_dec(v___y_4693_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__4(lean_object* v_toSend_4701_, lean_object* v_a_4702_, uint8_t v_closeAfter_4703_, uint8_t v___y_4704_, lean_object* v___f_4705_, lean_object* v_____r_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___f_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4709_ = lean_box(v_closeAfter_4703_);
v___x_4710_ = lean_box(v___y_4704_);
lean_inc(v___y_4707_);
v___f_4711_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__5___boxed), 8, 6);
lean_closure_set(v___f_4711_, 0, v_toSend_4701_);
lean_closure_set(v___f_4711_, 1, v_a_4702_);
lean_closure_set(v___f_4711_, 2, v___x_4709_);
lean_closure_set(v___f_4711_, 3, v___y_4707_);
lean_closure_set(v___f_4711_, 4, v___x_4710_);
lean_closure_set(v___f_4711_, 5, v___f_4705_);
v___x_4712_ = lean_unsigned_to_nat(0u);
v___x_4713_ = lean_st_ref_get(v___y_4707_);
v___x_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4713_);
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
v___x_4716_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4712_, v___y_4704_, v___x_4715_, v___f_4711_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__4___boxed(lean_object* v_toSend_4717_, lean_object* v_a_4718_, lean_object* v_closeAfter_4719_, lean_object* v___y_4720_, lean_object* v___f_4721_, lean_object* v_____r_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
uint8_t v_closeAfter_boxed_4725_; uint8_t v___y_8181__boxed_4726_; lean_object* v_res_4727_; 
v_closeAfter_boxed_4725_ = lean_unbox(v_closeAfter_4719_);
v___y_8181__boxed_4726_ = lean_unbox(v___y_4720_);
v_res_4727_ = l_Std_Http_Body_Stream_offer___lam__4(v_toSend_4717_, v_a_4718_, v_closeAfter_boxed_4725_, v___y_8181__boxed_4726_, v___f_4721_, v_____r_4722_, v___y_4723_);
lean_dec(v___y_4723_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__6(uint8_t v_closeAfter_4728_, lean_object* v___f_4729_, lean_object* v___y_4730_, uint8_t v___y_4731_, lean_object* v___f_4732_, lean_object* v_x_4733_){
_start:
{
if (lean_obj_tag(v_x_4733_) == 0)
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4743_; 
lean_dec_ref(v___f_4732_);
lean_dec_ref(v___f_4729_);
v_a_4735_ = lean_ctor_get(v_x_4733_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_x_4733_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4737_ = v_x_4733_;
v_isShared_4738_ = v_isSharedCheck_4743_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v_x_4733_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4743_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4741_; 
v___x_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
return v___x_4741_;
}
}
}
else
{
lean_dec_ref_known(v_x_4733_, 1);
if (v_closeAfter_4728_ == 0)
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
lean_dec_ref(v___f_4732_);
v___x_4744_ = lean_box(0);
lean_inc(v___y_4730_);
v___x_4745_ = lean_apply_3(v___f_4729_, v___x_4744_, v___y_4730_, lean_box(0));
return v___x_4745_;
}
else
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
lean_dec_ref(v___f_4729_);
v___x_4746_ = lean_unsigned_to_nat(0u);
v___x_4747_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___y_4730_);
v___x_4748_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4746_, v___y_4731_, v___x_4747_, v___f_4732_);
return v___x_4748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__6___boxed(lean_object* v_closeAfter_4749_, lean_object* v___f_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___f_4753_, lean_object* v_x_4754_, lean_object* v___y_4755_){
_start:
{
uint8_t v_closeAfter_boxed_4756_; uint8_t v___y_8216__boxed_4757_; lean_object* v_res_4758_; 
v_closeAfter_boxed_4756_ = lean_unbox(v_closeAfter_4749_);
v___y_8216__boxed_4757_ = lean_unbox(v___y_4752_);
v_res_4758_ = l_Std_Http_Body_Stream_offer___lam__6(v_closeAfter_boxed_4756_, v___f_4750_, v___y_4751_, v___y_8216__boxed_4757_, v___f_4753_, v_x_4754_);
lean_dec(v___y_4751_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__7(lean_object* v___f_4759_, lean_object* v___y_4760_, lean_object* v_toSend_4761_, uint8_t v___y_4762_, lean_object* v___f_4763_, lean_object* v_x_4764_){
_start:
{
if (lean_obj_tag(v_x_4764_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4774_; 
lean_dec_ref(v___f_4763_);
lean_dec_ref(v___f_4759_);
v_a_4766_ = lean_ctor_get(v_x_4764_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v_x_4764_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4768_ = v_x_4764_;
v_isShared_4769_ = v_isSharedCheck_4774_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v_x_4764_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4774_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4772_; 
v___x_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
return v___x_4772_;
}
}
}
else
{
lean_object* v_a_4775_; uint8_t v___x_4776_; 
v_a_4775_ = lean_ctor_get(v_x_4764_, 0);
lean_inc(v_a_4775_);
lean_dec_ref_known(v_x_4764_, 1);
v___x_4776_ = lean_unbox(v_a_4775_);
lean_dec(v_a_4775_);
if (v___x_4776_ == 0)
{
lean_object* v___x_4777_; lean_object* v___x_4778_; 
lean_dec_ref(v___f_4763_);
v___x_4777_ = lean_box(0);
lean_inc(v___y_4760_);
v___x_4778_ = lean_apply_3(v___f_4759_, v___x_4777_, v___y_4760_, lean_box(0));
return v___x_4778_;
}
else
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v_pendingProducer_4781_; lean_object* v_pendingConsumer_4782_; lean_object* v_interestWaiter_4783_; uint8_t v_closed_4784_; lean_object* v_knownSize_4785_; lean_object* v_pendingIncomplete_4786_; lean_object* v_closeError_4787_; uint8_t v_closeAfterProducer_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4799_; 
lean_dec_ref(v___f_4759_);
v___x_4779_ = lean_unsigned_to_nat(0u);
v___x_4780_ = lean_st_ref_take(v___y_4760_);
v_pendingProducer_4781_ = lean_ctor_get(v___x_4780_, 0);
v_pendingConsumer_4782_ = lean_ctor_get(v___x_4780_, 1);
v_interestWaiter_4783_ = lean_ctor_get(v___x_4780_, 2);
v_closed_4784_ = lean_ctor_get_uint8(v___x_4780_, sizeof(void*)*6);
v_knownSize_4785_ = lean_ctor_get(v___x_4780_, 3);
v_pendingIncomplete_4786_ = lean_ctor_get(v___x_4780_, 4);
v_closeError_4787_ = lean_ctor_get(v___x_4780_, 5);
v_closeAfterProducer_4788_ = lean_ctor_get_uint8(v___x_4780_, sizeof(void*)*6 + 1);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4790_ = v___x_4780_;
v_isShared_4791_ = v_isSharedCheck_4799_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_closeError_4787_);
lean_inc(v_pendingIncomplete_4786_);
lean_inc(v_knownSize_4785_);
lean_inc(v_interestWaiter_4783_);
lean_inc(v_pendingConsumer_4782_);
lean_inc(v_pendingProducer_4781_);
lean_dec(v___x_4780_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4799_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4792_; lean_object* v___x_4794_; 
v___x_4792_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_4785_, v_toSend_4761_);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 3, v___x_4792_);
v___x_4794_ = v___x_4790_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_pendingProducer_4781_);
lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_pendingConsumer_4782_);
lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_interestWaiter_4783_);
lean_ctor_set(v_reuseFailAlloc_4798_, 3, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4798_, 4, v_pendingIncomplete_4786_);
lean_ctor_set(v_reuseFailAlloc_4798_, 5, v_closeError_4787_);
lean_ctor_set_uint8(v_reuseFailAlloc_4798_, sizeof(void*)*6, v_closed_4784_);
lean_ctor_set_uint8(v_reuseFailAlloc_4798_, sizeof(void*)*6 + 1, v_closeAfterProducer_4788_);
v___x_4794_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4795_ = lean_st_ref_put(v___y_4760_, v___x_4794_);
v___x_4796_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4797_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4779_, v___y_4762_, v___x_4796_, v___f_4763_);
return v___x_4797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__7___boxed(lean_object* v___f_4800_, lean_object* v___y_4801_, lean_object* v_toSend_4802_, lean_object* v___y_4803_, lean_object* v___f_4804_, lean_object* v_x_4805_, lean_object* v___y_4806_){
_start:
{
uint8_t v___y_8266__boxed_4807_; lean_object* v_res_4808_; 
v___y_8266__boxed_4807_ = lean_unbox(v___y_4803_);
v_res_4808_ = l_Std_Http_Body_Stream_offer___lam__7(v___f_4800_, v___y_4801_, v_toSend_4802_, v___y_8266__boxed_4807_, v___f_4804_, v_x_4805_);
lean_dec_ref(v_toSend_4802_);
lean_dec(v___y_4801_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__8(lean_object* v_toSend_4809_, lean_object* v_val_4810_, uint8_t v___y_4811_, lean_object* v___f_4812_, lean_object* v_x_4813_){
_start:
{
if (lean_obj_tag(v_x_4813_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4823_; 
lean_dec_ref(v___f_4812_);
lean_dec_ref(v_toSend_4809_);
v_a_4815_ = lean_ctor_get(v_x_4813_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v_x_4813_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4817_ = v_x_4813_;
v_isShared_4818_ = v_isSharedCheck_4823_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v_x_4813_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4823_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4820_; 
if (v_isShared_4818_ == 0)
{
v___x_4820_ = v___x_4817_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4815_);
v___x_4820_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
lean_object* v___x_4821_; 
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
return v___x_4821_;
}
}
}
else
{
lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4837_; 
v_isSharedCheck_4837_ = !lean_is_exclusive(v_x_4813_);
if (v_isSharedCheck_4837_ == 0)
{
lean_object* v_unused_4838_; 
v_unused_4838_ = lean_ctor_get(v_x_4813_, 0);
lean_dec(v_unused_4838_);
v___x_4825_ = v_x_4813_;
v_isShared_4826_ = v_isSharedCheck_4837_;
goto v_resetjp_4824_;
}
else
{
lean_dec(v_x_4813_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4837_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4827_, 0, v_toSend_4809_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 0, v___x_4827_);
v___x_4829_ = v___x_4825_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4827_);
v___x_4829_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4830_; uint8_t v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_4810_, v___x_4829_);
v___x_4832_ = lean_box(v___x_4831_);
v___x_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4832_);
v___x_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
v___x_4835_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4830_, v___y_4811_, v___x_4834_, v___f_4812_);
return v___x_4835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__8___boxed(lean_object* v_toSend_4839_, lean_object* v_val_4840_, lean_object* v___y_4841_, lean_object* v___f_4842_, lean_object* v_x_4843_, lean_object* v___y_4844_){
_start:
{
uint8_t v___y_8337__boxed_4845_; lean_object* v_res_4846_; 
v___y_8337__boxed_4845_ = lean_unbox(v___y_4841_);
v_res_4846_ = l_Std_Http_Body_Stream_offer___lam__8(v_toSend_4839_, v_val_4840_, v___y_8337__boxed_4845_, v___f_4842_, v_x_4843_);
lean_dec_ref(v_val_4840_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__9(lean_object* v_toSend_4853_, lean_object* v_a_4854_, uint8_t v_closeAfter_4855_, lean_object* v___f_4856_, lean_object* v___f_4857_, lean_object* v___y_4858_, lean_object* v___f_4859_, lean_object* v___f_4860_, lean_object* v___f_4861_, lean_object* v_x_4862_){
_start:
{
if (lean_obj_tag(v_x_4862_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4872_; 
lean_dec_ref(v___f_4861_);
lean_dec_ref(v___f_4860_);
lean_dec_ref(v___f_4859_);
lean_dec_ref(v___f_4857_);
lean_dec_ref(v___f_4856_);
lean_dec(v_a_4854_);
lean_dec_ref(v_toSend_4853_);
v_a_4864_ = lean_ctor_get(v_x_4862_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v_x_4862_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4866_ = v_x_4862_;
v_isShared_4867_ = v_isSharedCheck_4872_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v_x_4862_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4872_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4869_; 
if (v_isShared_4867_ == 0)
{
v___x_4869_ = v___x_4866_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4864_);
v___x_4869_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
lean_object* v___x_4870_; 
v___x_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
return v___x_4870_;
}
}
}
else
{
lean_object* v_a_4873_; lean_object* v_pendingProducer_4874_; lean_object* v_pendingConsumer_4875_; lean_object* v_interestWaiter_4876_; uint8_t v_closed_4877_; lean_object* v_knownSize_4878_; lean_object* v_pendingIncomplete_4879_; lean_object* v_closeError_4880_; uint8_t v_closeAfterProducer_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4919_; 
v_a_4873_ = lean_ctor_get(v_x_4862_, 0);
lean_inc(v_a_4873_);
lean_dec_ref_known(v_x_4862_, 1);
v_pendingProducer_4874_ = lean_ctor_get(v_a_4873_, 0);
v_pendingConsumer_4875_ = lean_ctor_get(v_a_4873_, 1);
v_interestWaiter_4876_ = lean_ctor_get(v_a_4873_, 2);
v_closed_4877_ = lean_ctor_get_uint8(v_a_4873_, sizeof(void*)*6);
v_knownSize_4878_ = lean_ctor_get(v_a_4873_, 3);
v_pendingIncomplete_4879_ = lean_ctor_get(v_a_4873_, 4);
v_closeError_4880_ = lean_ctor_get(v_a_4873_, 5);
v_closeAfterProducer_4881_ = lean_ctor_get_uint8(v_a_4873_, sizeof(void*)*6 + 1);
v_isSharedCheck_4919_ = !lean_is_exclusive(v_a_4873_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4883_ = v_a_4873_;
v_isShared_4884_ = v_isSharedCheck_4919_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_closeError_4880_);
lean_inc(v_pendingIncomplete_4879_);
lean_inc(v_knownSize_4878_);
lean_inc(v_interestWaiter_4876_);
lean_inc(v_pendingConsumer_4875_);
lean_inc(v_pendingProducer_4874_);
lean_dec(v_a_4873_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4919_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
uint8_t v___y_4886_; 
if (v_closed_4877_ == 0)
{
lean_object* v_data_4908_; lean_object* v_extensions_4909_; uint8_t v___x_4910_; 
v_data_4908_ = lean_ctor_get(v_toSend_4853_, 0);
v_extensions_4909_ = lean_ctor_get(v_toSend_4853_, 1);
v___x_4910_ = l_ByteArray_isEmpty(v_data_4908_);
if (v___x_4910_ == 0)
{
lean_dec_ref(v___f_4861_);
lean_dec_ref(v___f_4860_);
v___y_4886_ = v___x_4910_;
goto v___jp_4885_;
}
else
{
lean_object* v___x_4911_; lean_object* v___x_4912_; uint8_t v___x_4913_; 
v___x_4911_ = lean_array_get_size(v_extensions_4909_);
v___x_4912_ = lean_unsigned_to_nat(0u);
v___x_4913_ = lean_nat_dec_eq(v___x_4911_, v___x_4912_);
if (v___x_4913_ == 0)
{
lean_dec_ref(v___f_4861_);
lean_dec_ref(v___f_4860_);
v___y_4886_ = v___x_4913_;
goto v___jp_4885_;
}
else
{
lean_del_object(v___x_4883_);
lean_dec(v_closeError_4880_);
lean_dec(v_pendingIncomplete_4879_);
lean_dec(v_knownSize_4878_);
lean_dec(v_interestWaiter_4876_);
lean_dec(v_pendingConsumer_4875_);
lean_dec(v_pendingProducer_4874_);
lean_dec_ref(v___f_4859_);
lean_dec_ref(v___f_4857_);
lean_dec_ref(v___f_4856_);
lean_dec(v_a_4854_);
lean_dec_ref(v_toSend_4853_);
if (v_closeAfter_4855_ == 0)
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
lean_dec_ref(v___f_4861_);
v___x_4914_ = lean_box(0);
lean_inc(v___y_4858_);
v___x_4915_ = lean_apply_3(v___f_4860_, v___x_4914_, v___y_4858_, lean_box(0));
return v___x_4915_;
}
else
{
lean_object* v___x_4916_; lean_object* v___x_4917_; 
lean_dec_ref(v___f_4860_);
v___x_4916_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___y_4858_);
v___x_4917_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4912_, v_closed_4877_, v___x_4916_, v___f_4861_);
return v___x_4917_;
}
}
}
}
else
{
lean_object* v___x_4918_; 
lean_del_object(v___x_4883_);
lean_dec(v_closeError_4880_);
lean_dec(v_pendingIncomplete_4879_);
lean_dec(v_knownSize_4878_);
lean_dec(v_interestWaiter_4876_);
lean_dec(v_pendingConsumer_4875_);
lean_dec(v_pendingProducer_4874_);
lean_dec_ref(v___f_4861_);
lean_dec_ref(v___f_4860_);
lean_dec_ref(v___f_4859_);
lean_dec_ref(v___f_4857_);
lean_dec_ref(v___f_4856_);
lean_dec(v_a_4854_);
lean_dec_ref(v_toSend_4853_);
v___x_4918_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___lam__9___closed__2));
return v___x_4918_;
}
v___jp_4885_:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___f_4889_; 
v___x_4887_ = lean_box(v_closeAfter_4855_);
v___x_4888_ = lean_box(v___y_4886_);
lean_inc_ref(v___f_4856_);
lean_inc(v_a_4854_);
lean_inc_ref(v_toSend_4853_);
v___f_4889_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__4___boxed), 8, 5);
lean_closure_set(v___f_4889_, 0, v_toSend_4853_);
lean_closure_set(v___f_4889_, 1, v_a_4854_);
lean_closure_set(v___f_4889_, 2, v___x_4887_);
lean_closure_set(v___f_4889_, 3, v___x_4888_);
lean_closure_set(v___f_4889_, 4, v___f_4856_);
if (lean_obj_tag(v_pendingConsumer_4875_) == 1)
{
lean_object* v_val_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___f_4893_; lean_object* v___x_4894_; lean_object* v___f_4895_; lean_object* v___x_4896_; lean_object* v___f_4897_; lean_object* v___x_4898_; lean_object* v___x_4900_; 
lean_dec_ref(v___f_4856_);
lean_dec(v_a_4854_);
v_val_4890_ = lean_ctor_get(v_pendingConsumer_4875_, 0);
lean_inc(v_val_4890_);
lean_dec_ref_known(v_pendingConsumer_4875_, 1);
v___x_4891_ = lean_box(v_closeAfter_4855_);
v___x_4892_ = lean_box(v___y_4886_);
lean_inc_n(v___y_4858_, 2);
v___f_4893_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__6___boxed), 7, 5);
lean_closure_set(v___f_4893_, 0, v___x_4891_);
lean_closure_set(v___f_4893_, 1, v___f_4857_);
lean_closure_set(v___f_4893_, 2, v___y_4858_);
lean_closure_set(v___f_4893_, 3, v___x_4892_);
lean_closure_set(v___f_4893_, 4, v___f_4859_);
v___x_4894_ = lean_box(v___y_4886_);
lean_inc_ref(v_toSend_4853_);
v___f_4895_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__7___boxed), 7, 5);
lean_closure_set(v___f_4895_, 0, v___f_4889_);
lean_closure_set(v___f_4895_, 1, v___y_4858_);
lean_closure_set(v___f_4895_, 2, v_toSend_4853_);
lean_closure_set(v___f_4895_, 3, v___x_4894_);
lean_closure_set(v___f_4895_, 4, v___f_4893_);
v___x_4896_ = lean_box(v___y_4886_);
v___f_4897_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4897_, 0, v_toSend_4853_);
lean_closure_set(v___f_4897_, 1, v_val_4890_);
lean_closure_set(v___f_4897_, 2, v___x_4896_);
lean_closure_set(v___f_4897_, 3, v___f_4895_);
v___x_4898_ = lean_box(0);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 1, v___x_4898_);
v___x_4900_ = v___x_4883_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_pendingProducer_4874_);
lean_ctor_set(v_reuseFailAlloc_4905_, 1, v___x_4898_);
lean_ctor_set(v_reuseFailAlloc_4905_, 2, v_interestWaiter_4876_);
lean_ctor_set(v_reuseFailAlloc_4905_, 3, v_knownSize_4878_);
lean_ctor_set(v_reuseFailAlloc_4905_, 4, v_pendingIncomplete_4879_);
lean_ctor_set(v_reuseFailAlloc_4905_, 5, v_closeError_4880_);
lean_ctor_set_uint8(v_reuseFailAlloc_4905_, sizeof(void*)*6, v_closed_4877_);
lean_ctor_set_uint8(v_reuseFailAlloc_4905_, sizeof(void*)*6 + 1, v_closeAfterProducer_4881_);
v___x_4900_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4901_ = lean_unsigned_to_nat(0u);
v___x_4902_ = lean_st_ref_swap(v___y_4858_, v___x_4900_);
lean_dec(v___x_4902_);
v___x_4903_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4904_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4901_, v___y_4886_, v___x_4903_, v___f_4897_);
return v___x_4904_;
}
}
else
{
lean_object* v___x_4906_; lean_object* v___x_4907_; 
lean_dec_ref(v___f_4889_);
lean_del_object(v___x_4883_);
lean_dec(v_closeError_4880_);
lean_dec(v_pendingIncomplete_4879_);
lean_dec(v_knownSize_4878_);
lean_dec(v_interestWaiter_4876_);
lean_dec(v_pendingConsumer_4875_);
lean_dec(v_pendingProducer_4874_);
lean_dec_ref(v___f_4859_);
lean_dec_ref(v___f_4857_);
v___x_4906_ = lean_box(0);
v___x_4907_ = l_Std_Http_Body_Stream_offer___lam__4(v_toSend_4853_, v_a_4854_, v_closeAfter_4855_, v___y_4886_, v___f_4856_, v___x_4906_, v___y_4858_);
return v___x_4907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__9___boxed(lean_object* v_toSend_4920_, lean_object* v_a_4921_, lean_object* v_closeAfter_4922_, lean_object* v___f_4923_, lean_object* v___f_4924_, lean_object* v___y_4925_, lean_object* v___f_4926_, lean_object* v___f_4927_, lean_object* v___f_4928_, lean_object* v_x_4929_, lean_object* v___y_4930_){
_start:
{
uint8_t v_closeAfter_boxed_4931_; lean_object* v_res_4932_; 
v_closeAfter_boxed_4931_ = lean_unbox(v_closeAfter_4922_);
v_res_4932_ = l_Std_Http_Body_Stream_offer___lam__9(v_toSend_4920_, v_a_4921_, v_closeAfter_boxed_4931_, v___f_4923_, v___f_4924_, v___y_4925_, v___f_4926_, v___f_4927_, v___f_4928_, v_x_4929_);
lean_dec(v___y_4925_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__10(lean_object* v___y_4933_, lean_object* v___f_4934_, lean_object* v_x_4935_){
_start:
{
if (lean_obj_tag(v_x_4935_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4945_; 
lean_dec_ref(v___f_4934_);
v_a_4937_ = lean_ctor_get(v_x_4935_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v_x_4935_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4939_ = v_x_4935_;
v_isShared_4940_ = v_isSharedCheck_4945_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v_x_4935_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4945_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4942_; 
if (v_isShared_4940_ == 0)
{
v___x_4942_ = v___x_4939_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4937_);
v___x_4942_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
lean_object* v___x_4943_; 
v___x_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4942_);
return v___x_4943_;
}
}
}
else
{
lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4957_; 
v_isSharedCheck_4957_ = !lean_is_exclusive(v_x_4935_);
if (v_isSharedCheck_4957_ == 0)
{
lean_object* v_unused_4958_; 
v_unused_4958_ = lean_ctor_get(v_x_4935_, 0);
lean_dec(v_unused_4958_);
v___x_4947_ = v_x_4935_;
v_isShared_4948_ = v_isSharedCheck_4957_;
goto v_resetjp_4946_;
}
else
{
lean_dec(v_x_4935_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4957_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4949_; uint8_t v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4953_; 
v___x_4949_ = lean_unsigned_to_nat(0u);
v___x_4950_ = 0;
v___x_4951_ = lean_st_ref_get(v___y_4933_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 0, v___x_4951_);
v___x_4953_ = v___x_4947_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v___x_4951_);
v___x_4953_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4953_);
v___x_4955_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4949_, v___x_4950_, v___x_4954_, v___f_4934_);
return v___x_4955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__10___boxed(lean_object* v___y_4959_, lean_object* v___f_4960_, lean_object* v_x_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Std_Http_Body_Stream_offer___lam__10(v___y_4959_, v___f_4960_, v_x_4961_);
lean_dec(v___y_4959_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__11(lean_object* v___f_4964_, lean_object* v___f_4965_, lean_object* v_toSend_4966_, lean_object* v_a_4967_, uint8_t v_closeAfter_4968_, lean_object* v___f_4969_, lean_object* v___y_4970_){
_start:
{
lean_object* v___f_4972_; lean_object* v___f_4973_; lean_object* v___x_4974_; lean_object* v___f_4975_; lean_object* v___f_4976_; lean_object* v___x_4977_; uint8_t v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
lean_inc_n(v___y_4970_, 4);
lean_inc_ref(v___f_4964_);
v___f_4972_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4972_, 0, v___f_4964_);
lean_closure_set(v___f_4972_, 1, v___y_4970_);
lean_inc_ref(v___f_4965_);
v___f_4973_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4973_, 0, v___f_4965_);
lean_closure_set(v___f_4973_, 1, v___y_4970_);
v___x_4974_ = lean_box(v_closeAfter_4968_);
v___f_4975_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__9___boxed), 11, 9);
lean_closure_set(v___f_4975_, 0, v_toSend_4966_);
lean_closure_set(v___f_4975_, 1, v_a_4967_);
lean_closure_set(v___f_4975_, 2, v___x_4974_);
lean_closure_set(v___f_4975_, 3, v___f_4969_);
lean_closure_set(v___f_4975_, 4, v___f_4965_);
lean_closure_set(v___f_4975_, 5, v___y_4970_);
lean_closure_set(v___f_4975_, 6, v___f_4973_);
lean_closure_set(v___f_4975_, 7, v___f_4964_);
lean_closure_set(v___f_4975_, 8, v___f_4972_);
v___f_4976_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__10___boxed), 4, 2);
lean_closure_set(v___f_4976_, 0, v___y_4970_);
lean_closure_set(v___f_4976_, 1, v___f_4975_);
v___x_4977_ = lean_unsigned_to_nat(0u);
v___x_4978_ = 0;
v___x_4979_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4970_);
v___x_4980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4977_, v___x_4978_, v___x_4979_, v___f_4976_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__11___boxed(lean_object* v___f_4981_, lean_object* v___f_4982_, lean_object* v_toSend_4983_, lean_object* v_a_4984_, lean_object* v_closeAfter_4985_, lean_object* v___f_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_){
_start:
{
uint8_t v_closeAfter_boxed_4989_; lean_object* v_res_4990_; 
v_closeAfter_boxed_4989_ = lean_unbox(v_closeAfter_4985_);
v_res_4990_ = l_Std_Http_Body_Stream_offer___lam__11(v___f_4981_, v___f_4982_, v_toSend_4983_, v_a_4984_, v_closeAfter_boxed_4989_, v___f_4986_, v___y_4987_);
lean_dec(v___y_4987_);
return v_res_4990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__12(lean_object* v___f_4991_, lean_object* v___f_4992_, lean_object* v_toSend_4993_, uint8_t v_closeAfter_4994_, lean_object* v___f_4995_, lean_object* v_stream_4996_, lean_object* v___f_4997_, lean_object* v_x_4998_){
_start:
{
if (lean_obj_tag(v_x_4998_) == 0)
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5008_; 
lean_dec_ref(v___f_4997_);
lean_dec_ref(v_stream_4996_);
lean_dec_ref(v___f_4995_);
lean_dec_ref(v_toSend_4993_);
lean_dec_ref(v___f_4992_);
lean_dec_ref(v___f_4991_);
v_a_5000_ = lean_ctor_get(v_x_4998_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v_x_4998_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5002_ = v_x_4998_;
v_isShared_5003_ = v_isSharedCheck_5008_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v_x_4998_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5008_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5000_);
v___x_5005_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
lean_object* v___x_5006_; 
v___x_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
return v___x_5006_;
}
}
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5010_; lean_object* v___f_5011_; lean_object* v___x_5012_; uint8_t v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v_a_5009_ = lean_ctor_get(v_x_4998_, 0);
lean_inc(v_a_5009_);
lean_dec_ref_known(v_x_4998_, 1);
v___x_5010_ = lean_box(v_closeAfter_4994_);
v___f_5011_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__11___boxed), 8, 6);
lean_closure_set(v___f_5011_, 0, v___f_4991_);
lean_closure_set(v___f_5011_, 1, v___f_4992_);
lean_closure_set(v___f_5011_, 2, v_toSend_4993_);
lean_closure_set(v___f_5011_, 3, v_a_5009_);
lean_closure_set(v___f_5011_, 4, v___x_5010_);
lean_closure_set(v___f_5011_, 5, v___f_4995_);
v___x_5012_ = lean_unsigned_to_nat(0u);
v___x_5013_ = 0;
v___x_5014_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_4996_, v___f_5011_);
v___x_5015_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5012_, v___x_5013_, v___x_5014_, v___f_4997_);
return v___x_5015_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__12___boxed(lean_object* v___f_5016_, lean_object* v___f_5017_, lean_object* v_toSend_5018_, lean_object* v_closeAfter_5019_, lean_object* v___f_5020_, lean_object* v_stream_5021_, lean_object* v___f_5022_, lean_object* v_x_5023_, lean_object* v___y_5024_){
_start:
{
uint8_t v_closeAfter_boxed_5025_; lean_object* v_res_5026_; 
v_closeAfter_boxed_5025_ = lean_unbox(v_closeAfter_5019_);
v_res_5026_ = l_Std_Http_Body_Stream_offer___lam__12(v___f_5016_, v___f_5017_, v_toSend_5018_, v_closeAfter_boxed_5025_, v___f_5020_, v_stream_5021_, v___f_5022_, v_x_5023_);
return v_res_5026_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__13(lean_object* v___f_5027_, lean_object* v___f_5028_, uint8_t v_closeAfter_5029_, lean_object* v___f_5030_, lean_object* v_stream_5031_, lean_object* v___f_5032_, lean_object* v_toSend_5033_){
_start:
{
lean_object* v___x_5035_; lean_object* v___f_5036_; lean_object* v___x_5037_; uint8_t v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5035_ = lean_box(v_closeAfter_5029_);
v___f_5036_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__12___boxed), 9, 7);
lean_closure_set(v___f_5036_, 0, v___f_5027_);
lean_closure_set(v___f_5036_, 1, v___f_5028_);
lean_closure_set(v___f_5036_, 2, v_toSend_5033_);
lean_closure_set(v___f_5036_, 3, v___x_5035_);
lean_closure_set(v___f_5036_, 4, v___f_5030_);
lean_closure_set(v___f_5036_, 5, v_stream_5031_);
lean_closure_set(v___f_5036_, 6, v___f_5032_);
v___x_5037_ = lean_unsigned_to_nat(0u);
v___x_5038_ = 0;
v___x_5039_ = lean_io_promise_new();
v___x_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5039_);
v___x_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5041_, 0, v___x_5040_);
v___x_5042_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5037_, v___x_5038_, v___x_5041_, v___f_5036_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__13___boxed(lean_object* v___f_5043_, lean_object* v___f_5044_, lean_object* v_closeAfter_5045_, lean_object* v___f_5046_, lean_object* v_stream_5047_, lean_object* v___f_5048_, lean_object* v_toSend_5049_, lean_object* v___y_5050_){
_start:
{
uint8_t v_closeAfter_boxed_5051_; lean_object* v_res_5052_; 
v_closeAfter_boxed_5051_ = lean_unbox(v_closeAfter_5045_);
v_res_5052_ = l_Std_Http_Body_Stream_offer___lam__13(v___f_5043_, v___f_5044_, v_closeAfter_boxed_5051_, v___f_5046_, v_stream_5047_, v___f_5048_, v_toSend_5049_);
return v_res_5052_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__14(lean_object* v___f_5053_, lean_object* v_x_5054_){
_start:
{
if (lean_obj_tag(v_x_5054_) == 0)
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5064_; 
lean_dec_ref(v___f_5053_);
v_a_5056_ = lean_ctor_get(v_x_5054_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v_x_5054_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5058_ = v_x_5054_;
v_isShared_5059_ = v_isSharedCheck_5064_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v_x_5054_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5064_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5056_);
v___x_5061_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
lean_object* v___x_5062_; 
v___x_5062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5061_);
return v___x_5062_;
}
}
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5066_; 
v_a_5065_ = lean_ctor_get(v_x_5054_, 0);
lean_inc(v_a_5065_);
lean_dec_ref_known(v_x_5054_, 1);
v___x_5066_ = lean_apply_2(v___f_5053_, v_a_5065_, lean_box(0));
return v___x_5066_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__14___boxed(lean_object* v___f_5067_, lean_object* v_x_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l_Std_Http_Body_Stream_offer___lam__14(v___f_5067_, v_x_5068_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__16(lean_object* v___f_5071_, lean_object* v___f_5072_, lean_object* v_x_5073_){
_start:
{
if (lean_obj_tag(v_x_5073_) == 0)
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5083_; 
lean_dec_ref(v___f_5072_);
lean_dec_ref(v___f_5071_);
v_a_5075_ = lean_ctor_get(v_x_5073_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v_x_5073_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5077_ = v_x_5073_;
v_isShared_5078_ = v_isSharedCheck_5083_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v_x_5073_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5083_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
lean_object* v___x_5081_; 
v___x_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5080_);
return v___x_5081_;
}
}
}
else
{
lean_object* v_a_5084_; 
v_a_5084_ = lean_ctor_get(v_x_5073_, 0);
lean_inc(v_a_5084_);
lean_dec_ref_known(v_x_5073_, 1);
if (lean_obj_tag(v_a_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5096_; 
lean_dec_ref(v___f_5072_);
v_a_5085_ = lean_ctor_get(v_a_5084_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v_a_5084_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5087_ = v_a_5084_;
v_isShared_5088_ = v_isSharedCheck_5096_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v_a_5084_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5096_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5089_; uint8_t v___x_5090_; lean_object* v___x_5092_; 
v___x_5089_ = lean_unsigned_to_nat(0u);
v___x_5090_ = 0;
if (v_isShared_5088_ == 0)
{
v___x_5092_ = v___x_5087_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5085_);
v___x_5092_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5093_, 0, v___x_5092_);
v___x_5094_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5089_, v___x_5090_, v___x_5093_, v___f_5071_);
return v___x_5094_;
}
}
}
else
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5116_; 
lean_dec_ref(v___f_5071_);
v_a_5097_ = lean_ctor_get(v_a_5084_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v_a_5084_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5099_ = v_a_5084_;
v_isShared_5100_ = v_isSharedCheck_5116_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v_a_5084_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5116_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
if (lean_obj_tag(v_a_5097_) == 0)
{
lean_object* v___x_5101_; 
lean_del_object(v___x_5099_);
lean_dec_ref(v___f_5072_);
v___x_5101_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_5101_;
}
else
{
lean_object* v_val_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5115_; 
v_val_5102_ = lean_ctor_get(v_a_5097_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v_a_5097_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5104_ = v_a_5097_;
v_isShared_5105_ = v_isSharedCheck_5115_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_val_5102_);
lean_dec(v_a_5097_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5115_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5106_; uint8_t v___x_5107_; lean_object* v___x_5109_; 
v___x_5106_ = lean_unsigned_to_nat(0u);
v___x_5107_ = 0;
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 0, v_val_5102_);
v___x_5109_ = v___x_5099_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_val_5102_);
v___x_5109_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
lean_object* v___x_5111_; 
if (v_isShared_5105_ == 0)
{
lean_ctor_set_tag(v___x_5104_, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5109_);
v___x_5111_ = v___x_5104_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5109_);
v___x_5111_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
lean_object* v___x_5112_; 
v___x_5112_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5106_, v___x_5107_, v___x_5111_, v___f_5072_);
return v___x_5112_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__16___boxed(lean_object* v___f_5117_, lean_object* v___f_5118_, lean_object* v_x_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_Std_Http_Body_Stream_offer___lam__16(v___f_5117_, v___f_5118_, v_x_5119_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer(lean_object* v_stream_5125_, lean_object* v_chunk_5126_, uint8_t v_incomplete_5127_, uint8_t v_closeAfter_5128_){
_start:
{
lean_object* v___f_5130_; lean_object* v___f_5131_; lean_object* v___f_5132_; lean_object* v___x_5133_; lean_object* v___f_5134_; lean_object* v___f_5135_; lean_object* v___f_5136_; uint8_t v___y_5138_; 
v___f_5130_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___closed__0));
v___f_5131_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___closed__1));
v___f_5132_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___closed__2));
v___x_5133_ = lean_box(v_closeAfter_5128_);
lean_inc_ref(v_stream_5125_);
v___f_5134_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__13___boxed), 8, 6);
lean_closure_set(v___f_5134_, 0, v___f_5131_);
lean_closure_set(v___f_5134_, 1, v___f_5131_);
lean_closure_set(v___f_5134_, 2, v___x_5133_);
lean_closure_set(v___f_5134_, 3, v___f_5130_);
lean_closure_set(v___f_5134_, 4, v_stream_5125_);
lean_closure_set(v___f_5134_, 5, v___f_5132_);
v___f_5135_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__14___boxed), 3, 1);
lean_closure_set(v___f_5135_, 0, v___f_5134_);
lean_inc_ref(v___f_5135_);
v___f_5136_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__16___boxed), 4, 2);
lean_closure_set(v___f_5136_, 0, v___f_5135_);
lean_closure_set(v___f_5136_, 1, v___f_5135_);
if (v_incomplete_5127_ == 0)
{
v___y_5138_ = v_incomplete_5127_;
goto v___jp_5137_;
}
else
{
if (v_closeAfter_5128_ == 0)
{
v___y_5138_ = v_incomplete_5127_;
goto v___jp_5137_;
}
else
{
uint8_t v___x_5145_; 
v___x_5145_ = 0;
v___y_5138_ = v___x_5145_;
goto v___jp_5137_;
}
}
v___jp_5137_:
{
lean_object* v___x_5139_; uint8_t v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5139_ = lean_unsigned_to_nat(0u);
v___x_5140_ = 0;
v___x_5141_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_5125_, v_chunk_5126_, v___y_5138_);
v___x_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5142_, 0, v___x_5141_);
v___x_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5142_);
v___x_5144_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5139_, v___x_5140_, v___x_5143_, v___f_5136_);
return v___x_5144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___boxed(lean_object* v_stream_5146_, lean_object* v_chunk_5147_, lean_object* v_incomplete_5148_, lean_object* v_closeAfter_5149_, lean_object* v_a_5150_){
_start:
{
uint8_t v_incomplete_boxed_5151_; uint8_t v_closeAfter_boxed_5152_; lean_object* v_res_5153_; 
v_incomplete_boxed_5151_ = lean_unbox(v_incomplete_5148_);
v_closeAfter_boxed_5152_ = lean_unbox(v_closeAfter_5149_);
v_res_5153_ = l_Std_Http_Body_Stream_offer(v_stream_5146_, v_chunk_5147_, v_incomplete_boxed_5151_, v_closeAfter_boxed_5152_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object* v_x_5154_){
_start:
{
uint8_t v___y_5157_; 
if (lean_obj_tag(v_x_5154_) == 0)
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5169_; 
v_a_5161_ = lean_ctor_get(v_x_5154_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v_x_5154_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5163_ = v_x_5154_;
v_isShared_5164_ = v_isSharedCheck_5169_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v_x_5154_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5169_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
lean_object* v___x_5167_; 
v___x_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5166_);
return v___x_5167_;
}
}
}
else
{
lean_object* v_a_5170_; lean_object* v_pendingConsumer_5171_; 
v_a_5170_ = lean_ctor_get(v_x_5154_, 0);
lean_inc(v_a_5170_);
lean_dec_ref_known(v_x_5154_, 1);
v_pendingConsumer_5171_ = lean_ctor_get(v_a_5170_, 1);
lean_inc(v_pendingConsumer_5171_);
lean_dec(v_a_5170_);
if (lean_obj_tag(v_pendingConsumer_5171_) == 0)
{
uint8_t v___x_5172_; 
v___x_5172_ = 0;
v___y_5157_ = v___x_5172_;
goto v___jp_5156_;
}
else
{
uint8_t v___x_5173_; 
lean_dec_ref_known(v_pendingConsumer_5171_, 1);
v___x_5173_ = 1;
v___y_5157_ = v___x_5173_;
goto v___jp_5156_;
}
}
v___jp_5156_:
{
lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; 
v___x_5158_ = lean_box(v___y_5157_);
v___x_5159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5158_);
v___x_5160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5160_, 0, v___x_5159_);
return v___x_5160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object* v_x_5174_, lean_object* v___y_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_5174_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object* v_a_5178_){
_start:
{
lean_object* v___f_5180_; lean_object* v___x_5181_; uint8_t v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___f_5180_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_5181_ = lean_unsigned_to_nat(0u);
v___x_5182_ = 0;
v___x_5183_ = lean_st_ref_get(v_a_5178_);
v___x_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5183_);
v___x_5185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5184_);
v___x_5186_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5181_, v___x_5182_, v___x_5185_, v___f_5180_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object* v_a_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_5187_);
lean_dec(v_a_5187_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object* v___y_5190_, lean_object* v_x_5191_){
_start:
{
if (lean_obj_tag(v_x_5191_) == 0)
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5201_; 
v_a_5193_ = lean_ctor_get(v_x_5191_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v_x_5191_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5195_ = v_x_5191_;
v_isShared_5196_ = v_isSharedCheck_5201_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v_x_5191_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5201_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
lean_object* v___x_5199_; 
v___x_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5198_);
return v___x_5199_;
}
}
}
else
{
lean_object* v___x_5202_; 
lean_dec_ref_known(v_x_5191_, 1);
v___x_5202_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_5190_);
return v___x_5202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object* v___y_5203_, lean_object* v_x_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_5203_, v_x_5204_);
lean_dec(v___y_5203_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object* v___y_5207_){
_start:
{
lean_object* v___f_5209_; lean_object* v___x_5210_; uint8_t v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
lean_inc(v___y_5207_);
v___f_5209_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5209_, 0, v___y_5207_);
v___x_5210_ = lean_unsigned_to_nat(0u);
v___x_5211_ = 0;
v___x_5212_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_5207_);
v___x_5213_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5210_, v___x_5211_, v___x_5212_, v___f_5209_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v_res_5216_; 
v_res_5216_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_5214_);
lean_dec(v___y_5214_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object* v_stream_5218_){
_start:
{
lean_object* v___f_5220_; lean_object* v___x_5221_; 
v___f_5220_ = ((lean_object*)(l_Std_Http_Body_Stream_hasInterest___closed__0));
v___x_5221_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_5218_, v___f_5220_);
return v___x_5221_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object* v_stream_5222_, lean_object* v_a_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l_Std_Http_Body_Stream_hasInterest(v_stream_5222_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object* v_lose_5225_, lean_object* v___y_5226_, uint8_t v___x_5227_, lean_object* v_promise_5228_, lean_object* v_x_5229_){
_start:
{
if (lean_obj_tag(v_x_5229_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5239_; 
lean_dec_ref(v_lose_5225_);
v_a_5231_ = lean_ctor_get(v_x_5229_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v_x_5229_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5233_ = v_x_5229_;
v_isShared_5234_ = v_isSharedCheck_5239_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v_x_5229_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5239_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5236_; 
if (v_isShared_5234_ == 0)
{
v___x_5236_ = v___x_5233_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v_a_5231_);
v___x_5236_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
lean_object* v___x_5237_; 
v___x_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5236_);
return v___x_5237_;
}
}
}
else
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5253_; 
v_a_5240_ = lean_ctor_get(v_x_5229_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_x_5229_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5242_ = v_x_5229_;
v_isShared_5243_ = v_isSharedCheck_5253_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v_x_5229_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5253_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
uint8_t v___x_5244_; 
v___x_5244_ = lean_unbox(v_a_5240_);
lean_dec(v_a_5240_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5245_; 
lean_del_object(v___x_5242_);
lean_inc(v___y_5226_);
v___x_5245_ = lean_apply_2(v_lose_5225_, v___y_5226_, lean_box(0));
return v___x_5245_;
}
else
{
lean_object* v___x_5246_; lean_object* v___x_5248_; 
lean_dec_ref(v_lose_5225_);
v___x_5246_ = lean_box(v___x_5227_);
if (v_isShared_5243_ == 0)
{
lean_ctor_set(v___x_5242_, 0, v___x_5246_);
v___x_5248_ = v___x_5242_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5246_);
v___x_5248_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; 
v___x_5249_ = lean_io_promise_resolve(v___x_5248_, v_promise_5228_);
v___x_5250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5249_);
v___x_5251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5250_);
return v___x_5251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object* v_lose_5254_, lean_object* v___y_5255_, lean_object* v___x_5256_, lean_object* v_promise_5257_, lean_object* v_x_5258_, lean_object* v___y_5259_){
_start:
{
uint8_t v___x_4079__boxed_5260_; lean_object* v_res_5261_; 
v___x_4079__boxed_5260_ = lean_unbox(v___x_5256_);
v_res_5261_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_5254_, v___y_5255_, v___x_4079__boxed_5260_, v_promise_5257_, v_x_5258_);
lean_dec(v_promise_5257_);
lean_dec(v___y_5255_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_5262_, lean_object* v_lose_5263_, lean_object* v___y_5264_){
_start:
{
lean_object* v_finished_5266_; lean_object* v_promise_5267_; uint8_t v___x_5268_; lean_object* v___x_5269_; lean_object* v___f_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; uint8_t v___y_5274_; uint8_t v___x_5282_; 
v_finished_5266_ = lean_ctor_get(v_w_5262_, 0);
lean_inc(v_finished_5266_);
v_promise_5267_ = lean_ctor_get(v_w_5262_, 1);
lean_inc(v_promise_5267_);
lean_dec_ref(v_w_5262_);
v___x_5268_ = 0;
v___x_5269_ = lean_box(v___x_5268_);
lean_inc(v___y_5264_);
v___f_5270_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5270_, 0, v_lose_5263_);
lean_closure_set(v___f_5270_, 1, v___y_5264_);
lean_closure_set(v___f_5270_, 2, v___x_5269_);
lean_closure_set(v___f_5270_, 3, v_promise_5267_);
v___x_5271_ = lean_unsigned_to_nat(0u);
v___x_5272_ = lean_st_ref_take(v_finished_5266_);
v___x_5282_ = lean_unbox(v___x_5272_);
lean_dec(v___x_5272_);
if (v___x_5282_ == 0)
{
uint8_t v___x_5283_; 
v___x_5283_ = 1;
v___y_5274_ = v___x_5283_;
goto v___jp_5273_;
}
else
{
v___y_5274_ = v___x_5268_;
goto v___jp_5273_;
}
v___jp_5273_:
{
uint8_t v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v___x_5275_ = 1;
v___x_5276_ = lean_box(v___x_5275_);
v___x_5277_ = lean_st_ref_put(v_finished_5266_, v___x_5276_);
lean_dec(v_finished_5266_);
v___x_5278_ = lean_box(v___y_5274_);
v___x_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
v___x_5280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5279_);
v___x_5281_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5271_, v___x_5268_, v___x_5280_, v___f_5270_);
return v___x_5281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object* v_w_5284_, lean_object* v_lose_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_5284_, v_lose_5285_, v___y_5286_);
lean_dec(v___y_5286_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object* v_w_5289_, lean_object* v_lose_5290_, lean_object* v___y_5291_){
_start:
{
lean_object* v_finished_5293_; lean_object* v_promise_5294_; uint8_t v___x_5295_; lean_object* v___x_5296_; lean_object* v___f_5297_; lean_object* v___x_5298_; uint8_t v___x_5299_; lean_object* v___x_5300_; uint8_t v___y_5302_; uint8_t v___x_5309_; 
v_finished_5293_ = lean_ctor_get(v_w_5289_, 0);
lean_inc(v_finished_5293_);
v_promise_5294_ = lean_ctor_get(v_w_5289_, 1);
lean_inc(v_promise_5294_);
lean_dec_ref(v_w_5289_);
v___x_5295_ = 1;
v___x_5296_ = lean_box(v___x_5295_);
lean_inc(v___y_5291_);
v___f_5297_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5297_, 0, v_lose_5290_);
lean_closure_set(v___f_5297_, 1, v___y_5291_);
lean_closure_set(v___f_5297_, 2, v___x_5296_);
lean_closure_set(v___f_5297_, 3, v_promise_5294_);
v___x_5298_ = lean_unsigned_to_nat(0u);
v___x_5299_ = 0;
v___x_5300_ = lean_st_ref_take(v_finished_5293_);
v___x_5309_ = lean_unbox(v___x_5300_);
lean_dec(v___x_5300_);
if (v___x_5309_ == 0)
{
v___y_5302_ = v___x_5295_;
goto v___jp_5301_;
}
else
{
v___y_5302_ = v___x_5299_;
goto v___jp_5301_;
}
v___jp_5301_:
{
lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; 
v___x_5303_ = lean_box(v___x_5295_);
v___x_5304_ = lean_st_ref_put(v_finished_5293_, v___x_5303_);
lean_dec(v_finished_5293_);
v___x_5305_ = lean_box(v___y_5302_);
v___x_5306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5305_);
v___x_5307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5307_, 0, v___x_5306_);
v___x_5308_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5298_, v___x_5299_, v___x_5307_, v___f_5297_);
return v___x_5308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_5310_, lean_object* v_lose_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_){
_start:
{
lean_object* v_res_5314_; 
v_res_5314_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_5310_, v_lose_5311_, v___y_5312_);
lean_dec(v___y_5312_);
return v_res_5314_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_5331_){
_start:
{
if (lean_obj_tag(v_x_5331_) == 0)
{
lean_object* v_a_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5341_; 
v_a_5333_ = lean_ctor_get(v_x_5331_, 0);
v_isSharedCheck_5341_ = !lean_is_exclusive(v_x_5331_);
if (v_isSharedCheck_5341_ == 0)
{
v___x_5335_ = v_x_5331_;
v_isShared_5336_ = v_isSharedCheck_5341_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_a_5333_);
lean_dec(v_x_5331_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5341_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5338_; 
if (v_isShared_5336_ == 0)
{
v___x_5338_ = v___x_5335_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_a_5333_);
v___x_5338_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
lean_object* v___x_5339_; 
v___x_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5339_, 0, v___x_5338_);
return v___x_5339_;
}
}
}
else
{
lean_object* v_a_5342_; lean_object* v_pendingConsumer_5343_; 
v_a_5342_ = lean_ctor_get(v_x_5331_, 0);
lean_inc(v_a_5342_);
lean_dec_ref_known(v_x_5331_, 1);
v_pendingConsumer_5343_ = lean_ctor_get(v_a_5342_, 1);
if (lean_obj_tag(v_pendingConsumer_5343_) == 0)
{
uint8_t v_closed_5344_; 
v_closed_5344_ = lean_ctor_get_uint8(v_a_5342_, sizeof(void*)*6);
lean_dec(v_a_5342_);
if (v_closed_5344_ == 0)
{
lean_object* v___x_5345_; 
v___x_5345_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_5345_;
}
else
{
lean_object* v___x_5346_; 
v___x_5346_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_5346_;
}
}
else
{
lean_object* v___x_5347_; 
lean_dec(v_a_5342_);
v___x_5347_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_5347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_5348_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_5358_, lean_object* v___y_5359_, lean_object* v_x_5360_){
_start:
{
if (lean_obj_tag(v_x_5360_) == 0)
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5370_; 
lean_dec_ref(v_waiter_5358_);
v_a_5362_ = lean_ctor_get(v_x_5360_, 0);
v_isSharedCheck_5370_ = !lean_is_exclusive(v_x_5360_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5364_ = v_x_5360_;
v_isShared_5365_ = v_isSharedCheck_5370_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v_x_5360_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5370_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_a_5362_);
v___x_5367_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
lean_object* v___x_5368_; 
v___x_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5367_);
return v___x_5368_;
}
}
}
else
{
lean_object* v_a_5371_; lean_object* v_pendingConsumer_5372_; 
v_a_5371_ = lean_ctor_get(v_x_5360_, 0);
lean_inc(v_a_5371_);
lean_dec_ref_known(v_x_5360_, 1);
v_pendingConsumer_5372_ = lean_ctor_get(v_a_5371_, 1);
lean_inc(v_pendingConsumer_5372_);
if (lean_obj_tag(v_pendingConsumer_5372_) == 0)
{
uint8_t v_closed_5373_; 
v_closed_5373_ = lean_ctor_get_uint8(v_a_5371_, sizeof(void*)*6);
if (v_closed_5373_ == 0)
{
lean_object* v_interestWaiter_5374_; 
v_interestWaiter_5374_ = lean_ctor_get(v_a_5371_, 2);
if (lean_obj_tag(v_interestWaiter_5374_) == 0)
{
lean_object* v_pendingProducer_5375_; lean_object* v_knownSize_5376_; lean_object* v_pendingIncomplete_5377_; lean_object* v_closeError_5378_; uint8_t v_closeAfterProducer_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5389_; 
v_pendingProducer_5375_ = lean_ctor_get(v_a_5371_, 0);
v_knownSize_5376_ = lean_ctor_get(v_a_5371_, 3);
v_pendingIncomplete_5377_ = lean_ctor_get(v_a_5371_, 4);
v_closeError_5378_ = lean_ctor_get(v_a_5371_, 5);
v_closeAfterProducer_5379_ = lean_ctor_get_uint8(v_a_5371_, sizeof(void*)*6 + 1);
v_isSharedCheck_5389_ = !lean_is_exclusive(v_a_5371_);
if (v_isSharedCheck_5389_ == 0)
{
lean_object* v_unused_5390_; lean_object* v_unused_5391_; 
v_unused_5390_ = lean_ctor_get(v_a_5371_, 2);
lean_dec(v_unused_5390_);
v_unused_5391_ = lean_ctor_get(v_a_5371_, 1);
lean_dec(v_unused_5391_);
v___x_5381_ = v_a_5371_;
v_isShared_5382_ = v_isSharedCheck_5389_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_closeError_5378_);
lean_inc(v_pendingIncomplete_5377_);
lean_inc(v_knownSize_5376_);
lean_inc(v_pendingProducer_5375_);
lean_dec(v_a_5371_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5389_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v___x_5383_; lean_object* v___x_5385_; 
v___x_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5383_, 0, v_waiter_5358_);
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 2, v___x_5383_);
v___x_5385_ = v___x_5381_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_pendingProducer_5375_);
lean_ctor_set(v_reuseFailAlloc_5388_, 1, v_pendingConsumer_5372_);
lean_ctor_set(v_reuseFailAlloc_5388_, 2, v___x_5383_);
lean_ctor_set(v_reuseFailAlloc_5388_, 3, v_knownSize_5376_);
lean_ctor_set(v_reuseFailAlloc_5388_, 4, v_pendingIncomplete_5377_);
lean_ctor_set(v_reuseFailAlloc_5388_, 5, v_closeError_5378_);
lean_ctor_set_uint8(v_reuseFailAlloc_5388_, sizeof(void*)*6, v_closed_5373_);
lean_ctor_set_uint8(v_reuseFailAlloc_5388_, sizeof(void*)*6 + 1, v_closeAfterProducer_5379_);
v___x_5385_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
lean_object* v___x_5386_; lean_object* v___x_5387_; 
v___x_5386_ = lean_st_ref_swap(v___y_5359_, v___x_5385_);
lean_dec(v___x_5386_);
v___x_5387_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_5387_;
}
}
}
else
{
lean_object* v___x_5392_; 
lean_dec(v_a_5371_);
lean_dec_ref(v_waiter_5358_);
v___x_5392_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_5392_;
}
}
else
{
lean_object* v___f_5393_; lean_object* v___x_5394_; 
lean_dec(v_a_5371_);
v___f_5393_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_5394_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_5358_, v___f_5393_, v___y_5359_);
return v___x_5394_;
}
}
else
{
lean_object* v___f_5395_; lean_object* v___x_5396_; 
lean_dec_ref_known(v_pendingConsumer_5372_, 1);
lean_dec(v_a_5371_);
v___f_5395_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_5396_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_5358_, v___f_5395_, v___y_5359_);
return v___x_5396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_5397_, lean_object* v___y_5398_, lean_object* v_x_5399_, lean_object* v___y_5400_){
_start:
{
lean_object* v_res_5401_; 
v_res_5401_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_5397_, v___y_5398_, v_x_5399_);
lean_dec(v___y_5398_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_5402_, lean_object* v___f_5403_, lean_object* v_x_5404_){
_start:
{
if (lean_obj_tag(v_x_5404_) == 0)
{
lean_object* v___x_5406_; 
lean_dec_ref(v___f_5403_);
v___x_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5406_, 0, v_x_5404_);
return v___x_5406_;
}
else
{
lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5418_; 
v_isSharedCheck_5418_ = !lean_is_exclusive(v_x_5404_);
if (v_isSharedCheck_5418_ == 0)
{
lean_object* v_unused_5419_; 
v_unused_5419_ = lean_ctor_get(v_x_5404_, 0);
lean_dec(v_unused_5419_);
v___x_5408_ = v_x_5404_;
v_isShared_5409_ = v_isSharedCheck_5418_;
goto v_resetjp_5407_;
}
else
{
lean_dec(v_x_5404_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5418_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5410_; uint8_t v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5414_; 
v___x_5410_ = lean_unsigned_to_nat(0u);
v___x_5411_ = 0;
v___x_5412_ = lean_st_ref_get(v___y_5402_);
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 0, v___x_5412_);
v___x_5414_ = v___x_5408_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v___x_5412_);
v___x_5414_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
lean_object* v___x_5415_; lean_object* v___x_5416_; 
v___x_5415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5415_, 0, v___x_5414_);
v___x_5416_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5410_, v___x_5411_, v___x_5415_, v___f_5403_);
return v___x_5416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_5420_, lean_object* v___f_5421_, lean_object* v_x_5422_, lean_object* v___y_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_5420_, v___f_5421_, v_x_5422_);
lean_dec(v___y_5420_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_5425_, lean_object* v___y_5426_){
_start:
{
lean_object* v___f_5428_; lean_object* v___f_5429_; lean_object* v___x_5430_; uint8_t v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
lean_inc_n(v___y_5426_, 2);
v___f_5428_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_5428_, 0, v_waiter_5425_);
lean_closure_set(v___f_5428_, 1, v___y_5426_);
v___f_5429_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5429_, 0, v___y_5426_);
lean_closure_set(v___f_5429_, 1, v___f_5428_);
v___x_5430_ = lean_unsigned_to_nat(0u);
v___x_5431_ = 0;
v___x_5432_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_5426_);
v___x_5433_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5430_, v___x_5431_, v___x_5432_, v___f_5429_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_5434_, v___y_5435_);
lean_dec(v___y_5435_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_5438_, lean_object* v_waiter_5439_){
_start:
{
lean_object* v___f_5441_; lean_object* v___x_5442_; 
v___f_5441_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5441_, 0, v_waiter_5439_);
v___x_5442_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_5438_, v___f_5441_);
return v___x_5442_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_5443_, lean_object* v_waiter_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_5443_, v_waiter_5444_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_5447_, lean_object* v___f_5448_, lean_object* v_x_5449_){
_start:
{
if (lean_obj_tag(v_x_5449_) == 0)
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5459_; 
lean_dec_ref(v___f_5448_);
v_a_5451_ = lean_ctor_get(v_x_5449_, 0);
v_isSharedCheck_5459_ = !lean_is_exclusive(v_x_5449_);
if (v_isSharedCheck_5459_ == 0)
{
v___x_5453_ = v_x_5449_;
v_isShared_5454_ = v_isSharedCheck_5459_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v_x_5449_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5459_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5456_; 
if (v_isShared_5454_ == 0)
{
v___x_5456_ = v___x_5453_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_a_5451_);
v___x_5456_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
lean_object* v___x_5457_; 
v___x_5457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5456_);
return v___x_5457_;
}
}
}
else
{
lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5471_; 
v_isSharedCheck_5471_ = !lean_is_exclusive(v_x_5449_);
if (v_isSharedCheck_5471_ == 0)
{
lean_object* v_unused_5472_; 
v_unused_5472_ = lean_ctor_get(v_x_5449_, 0);
lean_dec(v_unused_5472_);
v___x_5461_ = v_x_5449_;
v_isShared_5462_ = v_isSharedCheck_5471_;
goto v_resetjp_5460_;
}
else
{
lean_dec(v_x_5449_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5471_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5463_; uint8_t v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5467_; 
v___x_5463_ = lean_unsigned_to_nat(0u);
v___x_5464_ = 0;
v___x_5465_ = lean_st_ref_get(v___y_5447_);
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 0, v___x_5465_);
v___x_5467_ = v___x_5461_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v___x_5465_);
v___x_5467_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5468_, 0, v___x_5467_);
v___x_5469_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5463_, v___x_5464_, v___x_5468_, v___f_5448_);
return v___x_5469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_5473_, lean_object* v___f_5474_, lean_object* v_x_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v_res_5477_; 
v_res_5477_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_5473_, v___f_5474_, v_x_5475_);
lean_dec(v___y_5473_);
return v_res_5477_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_5478_, lean_object* v___y_5479_){
_start:
{
lean_object* v___f_5481_; lean_object* v___x_5482_; uint8_t v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; 
lean_inc(v___y_5479_);
v___f_5481_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_5481_, 0, v___y_5479_);
lean_closure_set(v___f_5481_, 1, v___f_5478_);
v___x_5482_ = lean_unsigned_to_nat(0u);
v___x_5483_ = 0;
v___x_5484_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_5479_);
v___x_5485_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5482_, v___x_5483_, v___x_5484_, v___f_5481_);
return v___x_5485_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_){
_start:
{
lean_object* v_res_5489_; 
v_res_5489_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_5486_, v___y_5487_);
lean_dec(v___y_5487_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_5493_){
_start:
{
lean_object* v___f_5494_; lean_object* v___f_5495_; lean_object* v___f_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
v___f_5494_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_5493_, 2);
v___f_5495_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_5495_, 0, v_stream_5493_);
v___f_5496_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_5497_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_5497_, 0, lean_box(0));
lean_closure_set(v___x_5497_, 1, lean_box(0));
lean_closure_set(v___x_5497_, 2, v_stream_5493_);
lean_closure_set(v___x_5497_, 3, v___f_5496_);
v___x_5498_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_5498_, 0, lean_box(0));
lean_closure_set(v___x_5498_, 1, lean_box(0));
lean_closure_set(v___x_5498_, 2, v_stream_5493_);
lean_closure_set(v___x_5498_, 3, v___f_5494_);
v___x_5499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5499_, 0, v___x_5497_);
lean_ctor_set(v___x_5499_, 1, v___f_5495_);
lean_ctor_set(v___x_5499_, 2, v___x_5498_);
return v___x_5499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v_x_5500_, lean_object* v_x_5501_){
_start:
{
if (lean_obj_tag(v_x_5501_) == 0)
{
lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5511_; 
lean_dec_ref(v_x_5500_);
v_a_5503_ = lean_ctor_get(v_x_5501_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v_x_5501_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5505_ = v_x_5501_;
v_isShared_5506_ = v_isSharedCheck_5511_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_dec(v_x_5501_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5511_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5503_);
v___x_5508_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
lean_object* v___x_5509_; 
v___x_5509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5509_, 0, v___x_5508_);
return v___x_5509_;
}
}
}
else
{
lean_object* v___x_5512_; 
lean_dec_ref_known(v_x_5501_, 1);
v___x_5512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5512_, 0, v_x_5500_);
return v___x_5512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0___boxed(lean_object* v_x_5513_, lean_object* v_x_5514_, lean_object* v___y_5515_){
_start:
{
lean_object* v_res_5516_; 
v_res_5516_ = l_Std_Http_Body_stream___lam__0(v_x_5513_, v_x_5514_);
return v_res_5516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_a_5517_, lean_object* v_x_5518_){
_start:
{
if (lean_obj_tag(v_x_5518_) == 0)
{
lean_object* v_a_5520_; lean_object* v___x_5521_; 
v_a_5520_ = lean_ctor_get(v_x_5518_, 0);
lean_inc(v_a_5520_);
lean_dec_ref_known(v_x_5518_, 1);
v___x_5521_ = l_Std_Http_Body_Stream_closeWithError(v_a_5517_, v_a_5520_);
return v___x_5521_;
}
else
{
lean_object* v___x_5522_; 
lean_dec_ref(v_a_5517_);
v___x_5522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5522_, 0, v_x_5518_);
return v___x_5522_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_a_5523_, lean_object* v_x_5524_, lean_object* v___y_5525_){
_start:
{
lean_object* v_res_5526_; 
v_res_5526_ = l_Std_Http_Body_stream___lam__1(v_a_5523_, v_x_5524_);
return v_res_5526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v_a_5527_, lean_object* v_x_5528_){
_start:
{
if (lean_obj_tag(v_x_5528_) == 0)
{
lean_object* v___x_5530_; 
lean_dec_ref(v_a_5527_);
v___x_5530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5530_, 0, v_x_5528_);
return v___x_5530_;
}
else
{
lean_object* v___x_5531_; 
lean_dec_ref_known(v_x_5528_, 1);
v___x_5531_ = l_Std_Http_Body_Stream_close(v_a_5527_);
return v___x_5531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v_a_5532_, lean_object* v_x_5533_, lean_object* v___y_5534_){
_start:
{
lean_object* v_res_5535_; 
v_res_5535_ = l_Std_Http_Body_stream___lam__2(v_a_5532_, v_x_5533_);
return v_res_5535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_gen_5536_, lean_object* v_a_5537_, lean_object* v___x_5538_, uint8_t v___x_5539_, lean_object* v___f_5540_, lean_object* v___f_5541_){
_start:
{
lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; 
v___x_5543_ = lean_apply_2(v_gen_5536_, v_a_5537_, lean_box(0));
lean_inc(v___x_5538_);
v___x_5544_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5538_, v___x_5539_, v___x_5543_, v___f_5540_);
v___x_5545_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5538_, v___x_5539_, v___x_5544_, v___f_5541_);
return v___x_5545_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_gen_5546_, lean_object* v_a_5547_, lean_object* v___x_5548_, lean_object* v___x_5549_, lean_object* v___f_5550_, lean_object* v___f_5551_, lean_object* v___y_5552_){
_start:
{
uint8_t v___x_1068__boxed_5553_; lean_object* v_res_5554_; 
v___x_1068__boxed_5553_ = lean_unbox(v___x_5549_);
v_res_5554_ = l_Std_Http_Body_stream___lam__3(v_gen_5546_, v_a_5547_, v___x_5548_, v___x_1068__boxed_5553_, v___f_5550_, v___f_5551_);
return v_res_5554_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_5555_, lean_object* v_a_5556_, lean_object* v___f_5557_, lean_object* v___f_5558_, lean_object* v___f_5559_, lean_object* v_x_5560_){
_start:
{
if (lean_obj_tag(v_x_5560_) == 0)
{
lean_object* v_a_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5570_; 
lean_dec_ref(v___f_5559_);
lean_dec_ref(v___f_5558_);
lean_dec_ref(v___f_5557_);
lean_dec_ref(v_a_5556_);
lean_dec_ref(v_gen_5555_);
v_a_5562_ = lean_ctor_get(v_x_5560_, 0);
v_isSharedCheck_5570_ = !lean_is_exclusive(v_x_5560_);
if (v_isSharedCheck_5570_ == 0)
{
v___x_5564_ = v_x_5560_;
v_isShared_5565_ = v_isSharedCheck_5570_;
goto v_resetjp_5563_;
}
else
{
lean_inc(v_a_5562_);
lean_dec(v_x_5560_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5570_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5567_; 
if (v_isShared_5565_ == 0)
{
v___x_5567_ = v___x_5564_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_a_5562_);
v___x_5567_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
lean_object* v___x_5568_; 
v___x_5568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5567_);
return v___x_5568_;
}
}
}
else
{
lean_object* v___x_5571_; uint8_t v___x_5572_; lean_object* v___x_5573_; lean_object* v___f_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; 
lean_dec_ref_known(v_x_5560_, 1);
v___x_5571_ = lean_unsigned_to_nat(0u);
v___x_5572_ = 0;
v___x_5573_ = lean_box(v___x_5572_);
v___f_5574_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 7, 6);
lean_closure_set(v___f_5574_, 0, v_gen_5555_);
lean_closure_set(v___f_5574_, 1, v_a_5556_);
lean_closure_set(v___f_5574_, 2, v___x_5571_);
lean_closure_set(v___f_5574_, 3, v___x_5573_);
lean_closure_set(v___f_5574_, 4, v___f_5557_);
lean_closure_set(v___f_5574_, 5, v___f_5558_);
v___x_5575_ = lean_io_as_task(v___f_5574_, v___x_5571_);
lean_dec_ref(v___x_5575_);
v___x_5576_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_5577_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5571_, v___x_5572_, v___x_5576_, v___f_5559_);
return v___x_5577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_5578_, lean_object* v_a_5579_, lean_object* v___f_5580_, lean_object* v___f_5581_, lean_object* v___f_5582_, lean_object* v_x_5583_, lean_object* v___y_5584_){
_start:
{
lean_object* v_res_5585_; 
v_res_5585_ = l_Std_Http_Body_stream___lam__4(v_gen_5578_, v_a_5579_, v___f_5580_, v___f_5581_, v___f_5582_, v_x_5583_);
return v_res_5585_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5(lean_object* v___x_5586_, lean_object* v___y_5587_){
_start:
{
lean_object* v___x_5589_; lean_object* v_pendingProducer_5590_; lean_object* v_pendingConsumer_5591_; lean_object* v_interestWaiter_5592_; uint8_t v_closed_5593_; lean_object* v_pendingIncomplete_5594_; lean_object* v_closeError_5595_; uint8_t v_closeAfterProducer_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5605_; 
v___x_5589_ = lean_st_ref_take(v___y_5587_);
v_pendingProducer_5590_ = lean_ctor_get(v___x_5589_, 0);
v_pendingConsumer_5591_ = lean_ctor_get(v___x_5589_, 1);
v_interestWaiter_5592_ = lean_ctor_get(v___x_5589_, 2);
v_closed_5593_ = lean_ctor_get_uint8(v___x_5589_, sizeof(void*)*6);
v_pendingIncomplete_5594_ = lean_ctor_get(v___x_5589_, 4);
v_closeError_5595_ = lean_ctor_get(v___x_5589_, 5);
v_closeAfterProducer_5596_ = lean_ctor_get_uint8(v___x_5589_, sizeof(void*)*6 + 1);
v_isSharedCheck_5605_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5605_ == 0)
{
lean_object* v_unused_5606_; 
v_unused_5606_ = lean_ctor_get(v___x_5589_, 3);
lean_dec(v_unused_5606_);
v___x_5598_ = v___x_5589_;
v_isShared_5599_ = v_isSharedCheck_5605_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_closeError_5595_);
lean_inc(v_pendingIncomplete_5594_);
lean_inc(v_interestWaiter_5592_);
lean_inc(v_pendingConsumer_5591_);
lean_inc(v_pendingProducer_5590_);
lean_dec(v___x_5589_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5605_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v___x_5601_; 
if (v_isShared_5599_ == 0)
{
lean_ctor_set(v___x_5598_, 3, v___x_5586_);
v___x_5601_ = v___x_5598_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_pendingProducer_5590_);
lean_ctor_set(v_reuseFailAlloc_5604_, 1, v_pendingConsumer_5591_);
lean_ctor_set(v_reuseFailAlloc_5604_, 2, v_interestWaiter_5592_);
lean_ctor_set(v_reuseFailAlloc_5604_, 3, v___x_5586_);
lean_ctor_set(v_reuseFailAlloc_5604_, 4, v_pendingIncomplete_5594_);
lean_ctor_set(v_reuseFailAlloc_5604_, 5, v_closeError_5595_);
lean_ctor_set_uint8(v_reuseFailAlloc_5604_, sizeof(void*)*6, v_closed_5593_);
lean_ctor_set_uint8(v_reuseFailAlloc_5604_, sizeof(void*)*6 + 1, v_closeAfterProducer_5596_);
v___x_5601_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
lean_object* v___x_5602_; lean_object* v___x_5603_; 
v___x_5602_ = lean_st_ref_put(v___y_5587_, v___x_5601_);
v___x_5603_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_5603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object* v___x_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l_Std_Http_Body_stream___lam__5(v___x_5607_, v___y_5608_);
lean_dec(v___y_5608_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6(lean_object* v_gen_5615_, lean_object* v_x_5616_){
_start:
{
if (lean_obj_tag(v_x_5616_) == 0)
{
lean_object* v___x_5618_; 
lean_dec_ref(v_gen_5615_);
v___x_5618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5618_, 0, v_x_5616_);
return v___x_5618_;
}
else
{
lean_object* v_a_5619_; lean_object* v___f_5620_; lean_object* v___f_5621_; lean_object* v___f_5622_; lean_object* v___f_5623_; lean_object* v___f_5624_; lean_object* v___x_5625_; uint8_t v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; 
v_a_5619_ = lean_ctor_get(v_x_5616_, 0);
lean_inc_n(v_a_5619_, 4);
v___f_5620_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5620_, 0, v_x_5616_);
v___f_5621_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_5621_, 0, v_a_5619_);
v___f_5622_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5622_, 0, v_a_5619_);
v___f_5623_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 7, 5);
lean_closure_set(v___f_5623_, 0, v_gen_5615_);
lean_closure_set(v___f_5623_, 1, v_a_5619_);
lean_closure_set(v___f_5623_, 2, v___f_5622_);
lean_closure_set(v___f_5623_, 3, v___f_5621_);
lean_closure_set(v___f_5623_, 4, v___f_5620_);
v___f_5624_ = ((lean_object*)(l_Std_Http_Body_stream___lam__6___closed__1));
v___x_5625_ = lean_unsigned_to_nat(0u);
v___x_5626_ = 0;
v___x_5627_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_5619_, v___f_5624_);
v___x_5628_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5625_, v___x_5626_, v___x_5627_, v___f_5623_);
return v___x_5628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object* v_gen_5629_, lean_object* v_x_5630_, lean_object* v___y_5631_){
_start:
{
lean_object* v_res_5632_; 
v_res_5632_ = l_Std_Http_Body_stream___lam__6(v_gen_5629_, v_x_5630_);
return v_res_5632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object* v_gen_5633_){
_start:
{
lean_object* v___f_5635_; lean_object* v___x_5636_; uint8_t v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; 
v___f_5635_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__6___boxed), 3, 1);
lean_closure_set(v___f_5635_, 0, v_gen_5633_);
v___x_5636_ = lean_unsigned_to_nat(0u);
v___x_5637_ = 0;
v___x_5638_ = l_Std_Http_Body_mkStream();
v___x_5639_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5636_, v___x_5637_, v___x_5638_, v___f_5635_);
return v___x_5639_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_5640_, lean_object* v_a_5641_){
_start:
{
lean_object* v_res_5642_; 
v_res_5642_ = l_Std_Http_Body_stream(v_gen_5640_);
return v_res_5642_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v___x_5643_, lean_object* v_content_5644_, lean_object* v_s_5645_, lean_object* v_x_5646_){
_start:
{
if (lean_obj_tag(v_x_5646_) == 0)
{
lean_object* v___x_5648_; 
lean_dec_ref(v_s_5645_);
lean_dec_ref(v_content_5644_);
v___x_5648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5648_, 0, v_x_5646_);
return v___x_5648_;
}
else
{
lean_object* v___x_5649_; uint8_t v___x_5650_; 
lean_dec_ref_known(v_x_5646_, 1);
v___x_5649_ = lean_unsigned_to_nat(0u);
v___x_5650_ = lean_nat_dec_lt(v___x_5649_, v___x_5643_);
if (v___x_5650_ == 0)
{
lean_object* v___x_5651_; 
lean_dec_ref(v_s_5645_);
lean_dec_ref(v_content_5644_);
v___x_5651_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_5651_;
}
else
{
lean_object* v___x_5652_; uint8_t v___x_5653_; lean_object* v___x_5654_; 
v___x_5652_ = l_Std_Http_Chunk_ofByteArray(v_content_5644_);
v___x_5653_ = 0;
v___x_5654_ = l_Std_Http_Body_Stream_send(v_s_5645_, v___x_5652_, v___x_5653_);
return v___x_5654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v___x_5655_, lean_object* v_content_5656_, lean_object* v_s_5657_, lean_object* v_x_5658_, lean_object* v___y_5659_){
_start:
{
lean_object* v_res_5660_; 
v_res_5660_ = l_Std_Http_Body_fromBytes___lam__0(v___x_5655_, v_content_5656_, v_s_5657_, v_x_5658_);
lean_dec(v___x_5655_);
return v_res_5660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object* v_content_5661_, lean_object* v_s_5662_){
_start:
{
lean_object* v___x_5664_; lean_object* v___f_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___f_5668_; lean_object* v___x_5669_; uint8_t v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; 
v___x_5664_ = lean_byte_array_size(v_content_5661_);
lean_inc_ref(v_s_5662_);
v___f_5665_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 5, 3);
lean_closure_set(v___f_5665_, 0, v___x_5664_);
lean_closure_set(v___f_5665_, 1, v_content_5661_);
lean_closure_set(v___f_5665_, 2, v_s_5662_);
v___x_5666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5664_);
v___x_5667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5666_);
v___f_5668_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__5___boxed), 3, 1);
lean_closure_set(v___f_5668_, 0, v___x_5667_);
v___x_5669_ = lean_unsigned_to_nat(0u);
v___x_5670_ = 0;
v___x_5671_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_5662_, v___f_5668_);
v___x_5672_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5669_, v___x_5670_, v___x_5671_, v___f_5665_);
return v___x_5672_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object* v_content_5673_, lean_object* v_s_5674_, lean_object* v___y_5675_){
_start:
{
lean_object* v_res_5676_; 
v_res_5676_ = l_Std_Http_Body_fromBytes___lam__2(v_content_5673_, v_s_5674_);
return v_res_5676_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_5677_){
_start:
{
lean_object* v___f_5679_; lean_object* v___x_5680_; 
v___f_5679_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5679_, 0, v_content_5677_);
v___x_5680_ = l_Std_Http_Body_stream(v___f_5679_);
return v___x_5680_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_5681_, lean_object* v_a_5682_){
_start:
{
lean_object* v_res_5683_; 
v_res_5683_ = l_Std_Http_Body_fromBytes(v_content_5681_);
return v_res_5683_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1(lean_object* v_a_5684_, lean_object* v___f_5685_, lean_object* v_x_5686_){
_start:
{
if (lean_obj_tag(v_x_5686_) == 0)
{
lean_object* v_a_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5696_; 
lean_dec_ref(v___f_5685_);
lean_dec_ref(v_a_5684_);
v_a_5688_ = lean_ctor_get(v_x_5686_, 0);
v_isSharedCheck_5696_ = !lean_is_exclusive(v_x_5686_);
if (v_isSharedCheck_5696_ == 0)
{
v___x_5690_ = v_x_5686_;
v_isShared_5691_ = v_isSharedCheck_5696_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_a_5688_);
lean_dec(v_x_5686_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5696_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v___x_5693_; 
if (v_isShared_5691_ == 0)
{
v___x_5693_ = v___x_5690_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_a_5688_);
v___x_5693_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
lean_object* v___x_5694_; 
v___x_5694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5693_);
return v___x_5694_;
}
}
}
else
{
lean_object* v___x_5697_; uint8_t v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; 
lean_dec_ref_known(v_x_5686_, 1);
v___x_5697_ = lean_unsigned_to_nat(0u);
v___x_5698_ = 0;
v___x_5699_ = l_Std_Http_Body_Stream_close(v_a_5684_);
v___x_5700_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5697_, v___x_5698_, v___x_5699_, v___f_5685_);
return v___x_5700_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1___boxed(lean_object* v_a_5701_, lean_object* v___f_5702_, lean_object* v_x_5703_, lean_object* v___y_5704_){
_start:
{
lean_object* v_res_5705_; 
v_res_5705_ = l_Std_Http_Body_empty___lam__1(v_a_5701_, v___f_5702_, v_x_5703_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_x_5712_){
_start:
{
if (lean_obj_tag(v_x_5712_) == 0)
{
lean_object* v___x_5714_; 
v___x_5714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5714_, 0, v_x_5712_);
return v___x_5714_;
}
else
{
lean_object* v_a_5715_; lean_object* v___f_5716_; lean_object* v___f_5717_; lean_object* v___x_5718_; lean_object* v___f_5719_; uint8_t v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; 
v_a_5715_ = lean_ctor_get(v_x_5712_, 0);
lean_inc_n(v_a_5715_, 2);
v___f_5716_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5716_, 0, v_x_5712_);
v___f_5717_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5717_, 0, v_a_5715_);
lean_closure_set(v___f_5717_, 1, v___f_5716_);
v___x_5718_ = lean_unsigned_to_nat(0u);
v___f_5719_ = ((lean_object*)(l_Std_Http_Body_empty___lam__2___closed__2));
v___x_5720_ = 0;
v___x_5721_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_5715_, v___f_5719_);
v___x_5722_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5718_, v___x_5720_, v___x_5721_, v___f_5717_);
return v___x_5722_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_x_5723_, lean_object* v___y_5724_){
_start:
{
lean_object* v_res_5725_; 
v_res_5725_ = l_Std_Http_Body_empty___lam__2(v_x_5723_);
return v_res_5725_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___f_5728_; lean_object* v___x_5729_; uint8_t v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; 
v___f_5728_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_5729_ = lean_unsigned_to_nat(0u);
v___x_5730_ = 0;
v___x_5731_ = l_Std_Http_Body_mkStream();
v___x_5732_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5729_, v___x_5730_, v___x_5731_, v___f_5728_);
return v___x_5732_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_5733_){
_start:
{
lean_object* v_res_5734_; 
v_res_5734_ = l_Std_Http_Body_empty();
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_5757_, lean_object* v_f_5758_){
_start:
{
lean_object* v_line_5759_; lean_object* v_body_5760_; lean_object* v_extensions_5761_; lean_object* v___x_5763_; uint8_t v_isShared_5764_; uint8_t v_isSharedCheck_5769_; 
v_line_5759_ = lean_ctor_get(v_f_5758_, 0);
v_body_5760_ = lean_ctor_get(v_f_5758_, 1);
v_extensions_5761_ = lean_ctor_get(v_f_5758_, 2);
v_isSharedCheck_5769_ = !lean_is_exclusive(v_f_5758_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5763_ = v_f_5758_;
v_isShared_5764_ = v_isSharedCheck_5769_;
goto v_resetjp_5762_;
}
else
{
lean_inc(v_extensions_5761_);
lean_inc(v_body_5760_);
lean_inc(v_line_5759_);
lean_dec(v_f_5758_);
v___x_5763_ = lean_box(0);
v_isShared_5764_ = v_isSharedCheck_5769_;
goto v_resetjp_5762_;
}
v_resetjp_5762_:
{
lean_object* v___x_5765_; lean_object* v___x_5767_; 
v___x_5765_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_5757_, v_body_5760_);
if (v_isShared_5764_ == 0)
{
lean_ctor_set(v___x_5763_, 1, v___x_5765_);
v___x_5767_ = v___x_5763_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_line_5759_);
lean_ctor_set(v_reuseFailAlloc_5768_, 1, v___x_5765_);
lean_ctor_set(v_reuseFailAlloc_5768_, 2, v_extensions_5761_);
v___x_5767_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
return v___x_5767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_5773_, lean_object* v_x_5774_){
_start:
{
if (lean_obj_tag(v_x_5774_) == 0)
{
lean_object* v_a_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5784_; 
lean_dec_ref(v___x_5773_);
v_a_5776_ = lean_ctor_get(v_x_5774_, 0);
v_isSharedCheck_5784_ = !lean_is_exclusive(v_x_5774_);
if (v_isSharedCheck_5784_ == 0)
{
v___x_5778_ = v_x_5774_;
v_isShared_5779_ = v_isSharedCheck_5784_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_a_5776_);
lean_dec(v_x_5774_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5784_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v___x_5781_; 
if (v_isShared_5779_ == 0)
{
v___x_5781_ = v___x_5778_;
goto v_reusejp_5780_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_a_5776_);
v___x_5781_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5780_;
}
v_reusejp_5780_:
{
lean_object* v___x_5782_; 
v___x_5782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5781_);
return v___x_5782_;
}
}
}
else
{
lean_object* v_a_5785_; lean_object* v___x_5787_; uint8_t v_isShared_5788_; uint8_t v_isSharedCheck_5804_; 
v_a_5785_ = lean_ctor_get(v_x_5774_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v_x_5774_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5787_ = v_x_5774_;
v_isShared_5788_ = v_isSharedCheck_5804_;
goto v_resetjp_5786_;
}
else
{
lean_inc(v_a_5785_);
lean_dec(v_x_5774_);
v___x_5787_ = lean_box(0);
v_isShared_5788_ = v_isSharedCheck_5804_;
goto v_resetjp_5786_;
}
v_resetjp_5786_:
{
lean_object* v_line_5789_; lean_object* v_body_5790_; lean_object* v_extensions_5791_; lean_object* v___x_5793_; uint8_t v_isShared_5794_; uint8_t v_isSharedCheck_5803_; 
v_line_5789_ = lean_ctor_get(v_a_5785_, 0);
v_body_5790_ = lean_ctor_get(v_a_5785_, 1);
v_extensions_5791_ = lean_ctor_get(v_a_5785_, 2);
v_isSharedCheck_5803_ = !lean_is_exclusive(v_a_5785_);
if (v_isSharedCheck_5803_ == 0)
{
v___x_5793_ = v_a_5785_;
v_isShared_5794_ = v_isSharedCheck_5803_;
goto v_resetjp_5792_;
}
else
{
lean_inc(v_extensions_5791_);
lean_inc(v_body_5790_);
lean_inc(v_line_5789_);
lean_dec(v_a_5785_);
v___x_5793_ = lean_box(0);
v_isShared_5794_ = v_isSharedCheck_5803_;
goto v_resetjp_5792_;
}
v_resetjp_5792_:
{
lean_object* v___x_5795_; lean_object* v___x_5797_; 
v___x_5795_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_5773_, v_body_5790_);
if (v_isShared_5794_ == 0)
{
lean_ctor_set(v___x_5793_, 1, v___x_5795_);
v___x_5797_ = v___x_5793_;
goto v_reusejp_5796_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_line_5789_);
lean_ctor_set(v_reuseFailAlloc_5802_, 1, v___x_5795_);
lean_ctor_set(v_reuseFailAlloc_5802_, 2, v_extensions_5791_);
v___x_5797_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5796_;
}
v_reusejp_5796_:
{
lean_object* v___x_5799_; 
if (v_isShared_5788_ == 0)
{
lean_ctor_set(v___x_5787_, 0, v___x_5797_);
v___x_5799_ = v___x_5787_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v___x_5797_);
v___x_5799_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
lean_object* v___x_5800_; 
v___x_5800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5800_, 0, v___x_5799_);
return v___x_5800_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_5805_, lean_object* v_x_5806_, lean_object* v___y_5807_){
_start:
{
lean_object* v_res_5808_; 
v_res_5808_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_5805_, v_x_5806_);
return v_res_5808_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_5809_, lean_object* v_action_5810_, lean_object* v___y_5811_){
_start:
{
lean_object* v___x_5813_; uint8_t v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; 
v___x_5813_ = lean_unsigned_to_nat(0u);
v___x_5814_ = 0;
lean_inc_ref(v___y_5811_);
v___x_5815_ = lean_apply_2(v_action_5810_, v___y_5811_, lean_box(0));
v___x_5816_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5813_, v___x_5814_, v___x_5815_, v___f_5809_);
return v___x_5816_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_5817_, lean_object* v_action_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_){
_start:
{
lean_object* v_res_5821_; 
v_res_5821_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_5817_, v_action_5818_, v___y_5819_);
lean_dec_ref(v___y_5819_);
return v_res_5821_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_5827_, lean_object* v_action_5828_, lean_object* v___y_5829_){
_start:
{
lean_object* v___x_5831_; uint8_t v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5831_ = lean_unsigned_to_nat(0u);
v___x_5832_ = 0;
v___x_5833_ = lean_apply_1(v_action_5828_, lean_box(0));
v___x_5834_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5831_, v___x_5832_, v___x_5833_, v___f_5827_);
return v___x_5834_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_5835_, lean_object* v_action_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_){
_start:
{
lean_object* v_res_5839_; 
v_res_5839_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_5835_, v_action_5836_, v___y_5837_);
lean_dec_ref(v___y_5837_);
return v_res_5839_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_5843_, lean_object* v_x_5844_){
_start:
{
if (lean_obj_tag(v_x_5844_) == 0)
{
lean_object* v_a_5846_; lean_object* v___x_5848_; uint8_t v_isShared_5849_; uint8_t v_isSharedCheck_5854_; 
v_a_5846_ = lean_ctor_get(v_x_5844_, 0);
v_isSharedCheck_5854_ = !lean_is_exclusive(v_x_5844_);
if (v_isSharedCheck_5854_ == 0)
{
v___x_5848_ = v_x_5844_;
v_isShared_5849_ = v_isSharedCheck_5854_;
goto v_resetjp_5847_;
}
else
{
lean_inc(v_a_5846_);
lean_dec(v_x_5844_);
v___x_5848_ = lean_box(0);
v_isShared_5849_ = v_isSharedCheck_5854_;
goto v_resetjp_5847_;
}
v_resetjp_5847_:
{
lean_object* v___x_5851_; 
if (v_isShared_5849_ == 0)
{
v___x_5851_ = v___x_5848_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5853_; 
v_reuseFailAlloc_5853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5853_, 0, v_a_5846_);
v___x_5851_ = v_reuseFailAlloc_5853_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
lean_object* v___x_5852_; 
v___x_5852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5852_, 0, v___x_5851_);
return v___x_5852_;
}
}
}
else
{
lean_object* v_a_5855_; lean_object* v___x_5857_; uint8_t v_isShared_5858_; uint8_t v_isSharedCheck_5864_; 
v_a_5855_ = lean_ctor_get(v_x_5844_, 0);
v_isSharedCheck_5864_ = !lean_is_exclusive(v_x_5844_);
if (v_isSharedCheck_5864_ == 0)
{
v___x_5857_ = v_x_5844_;
v_isShared_5858_ = v_isSharedCheck_5864_;
goto v_resetjp_5856_;
}
else
{
lean_inc(v_a_5855_);
lean_dec(v_x_5844_);
v___x_5857_ = lean_box(0);
v_isShared_5858_ = v_isSharedCheck_5864_;
goto v_resetjp_5856_;
}
v_resetjp_5856_:
{
lean_object* v___x_5859_; lean_object* v___x_5861_; 
v___x_5859_ = l_Std_Http_Request_Builder_body___redArg(v_builder_5843_, v_a_5855_);
if (v_isShared_5858_ == 0)
{
lean_ctor_set(v___x_5857_, 0, v___x_5859_);
v___x_5861_ = v___x_5857_;
goto v_reusejp_5860_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v___x_5859_);
v___x_5861_ = v_reuseFailAlloc_5863_;
goto v_reusejp_5860_;
}
v_reusejp_5860_:
{
lean_object* v___x_5862_; 
v___x_5862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5862_, 0, v___x_5861_);
return v___x_5862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_5865_, lean_object* v_x_5866_, lean_object* v___y_5867_){
_start:
{
lean_object* v_res_5868_; 
v_res_5868_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_5865_, v_x_5866_);
lean_dec_ref(v_builder_5865_);
return v_res_5868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_5869_, lean_object* v_gen_5870_){
_start:
{
lean_object* v___f_5872_; lean_object* v___x_5873_; uint8_t v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; 
v___f_5872_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5872_, 0, v_builder_5869_);
v___x_5873_ = lean_unsigned_to_nat(0u);
v___x_5874_ = 0;
v___x_5875_ = l_Std_Http_Body_stream(v_gen_5870_);
v___x_5876_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5873_, v___x_5874_, v___x_5875_, v___f_5872_);
return v___x_5876_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_5877_, lean_object* v_gen_5878_, lean_object* v_a_5879_){
_start:
{
lean_object* v_res_5880_; 
v_res_5880_ = l_Std_Http_Request_Builder_stream(v_builder_5877_, v_gen_5878_);
return v_res_5880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_5881_, lean_object* v_x_5882_){
_start:
{
if (lean_obj_tag(v_x_5882_) == 0)
{
lean_object* v_a_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5892_; 
v_a_5884_ = lean_ctor_get(v_x_5882_, 0);
v_isSharedCheck_5892_ = !lean_is_exclusive(v_x_5882_);
if (v_isSharedCheck_5892_ == 0)
{
v___x_5886_ = v_x_5882_;
v_isShared_5887_ = v_isSharedCheck_5892_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_a_5884_);
lean_dec(v_x_5882_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5892_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5889_; 
if (v_isShared_5887_ == 0)
{
v___x_5889_ = v___x_5886_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5891_; 
v_reuseFailAlloc_5891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5891_, 0, v_a_5884_);
v___x_5889_ = v_reuseFailAlloc_5891_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
lean_object* v___x_5890_; 
v___x_5890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5890_, 0, v___x_5889_);
return v___x_5890_;
}
}
}
else
{
lean_object* v_a_5893_; lean_object* v___x_5895_; uint8_t v_isShared_5896_; uint8_t v_isSharedCheck_5902_; 
v_a_5893_ = lean_ctor_get(v_x_5882_, 0);
v_isSharedCheck_5902_ = !lean_is_exclusive(v_x_5882_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5895_ = v_x_5882_;
v_isShared_5896_ = v_isSharedCheck_5902_;
goto v_resetjp_5894_;
}
else
{
lean_inc(v_a_5893_);
lean_dec(v_x_5882_);
v___x_5895_ = lean_box(0);
v_isShared_5896_ = v_isSharedCheck_5902_;
goto v_resetjp_5894_;
}
v_resetjp_5894_:
{
lean_object* v___x_5897_; lean_object* v___x_5899_; 
v___x_5897_ = l_Std_Http_Response_Builder_body___redArg(v_builder_5881_, v_a_5893_);
if (v_isShared_5896_ == 0)
{
lean_ctor_set(v___x_5895_, 0, v___x_5897_);
v___x_5899_ = v___x_5895_;
goto v_reusejp_5898_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v___x_5897_);
v___x_5899_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5898_;
}
v_reusejp_5898_:
{
lean_object* v___x_5900_; 
v___x_5900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5899_);
return v___x_5900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_5903_, lean_object* v_x_5904_, lean_object* v___y_5905_){
_start:
{
lean_object* v_res_5906_; 
v_res_5906_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_5903_, v_x_5904_);
lean_dec_ref(v_builder_5903_);
return v_res_5906_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_5907_, lean_object* v_gen_5908_){
_start:
{
lean_object* v___f_5910_; lean_object* v___x_5911_; uint8_t v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___f_5910_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5910_, 0, v_builder_5907_);
v___x_5911_ = lean_unsigned_to_nat(0u);
v___x_5912_ = 0;
v___x_5913_ = l_Std_Http_Body_stream(v_gen_5908_);
v___x_5914_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5911_, v___x_5912_, v___x_5913_, v___f_5910_);
return v___x_5914_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_5915_, lean_object* v_gen_5916_, lean_object* v_a_5917_){
_start:
{
lean_object* v_res_5918_; 
v_res_5918_ = l_Std_Http_Response_Builder_stream(v_builder_5915_, v_gen_5916_);
return v_res_5918_;
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

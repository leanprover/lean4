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
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_IO_Promise_new___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody(lean_object*, lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody___redArg(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_clean_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_clean_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_Promise_new___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_close___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_close___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "the read was cancelled before the body ended"};
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__2 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__2_value;
static const lean_ctor_object l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__2_value)}};
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__3 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value;
static const lean_closure_object l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value),((lean_object*)&l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0_value),((lean_object*)&l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2_value)} };
static const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1 = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync = (const lean_object*)&l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "body exceeded maximum size of "};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " bytes"};
static const lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorIdx___impl(lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_tag_nat(v_x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorIdx___impl___boxed(lean_object* v_x_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorIdx___impl(v_x_214_);
lean_dec(v_x_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim___redArg(lean_object* v_t_216_, lean_object* v_k_217_){
_start:
{
if (lean_obj_tag(v_t_216_) == 0)
{
return v_k_217_;
}
else
{
lean_object* v_err_218_; lean_object* v___x_219_; 
v_err_218_ = lean_ctor_get(v_t_216_, 0);
lean_inc(v_err_218_);
lean_dec_ref_known(v_t_216_, 1);
v___x_219_ = lean_apply_1(v_k_217_, v_err_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim(lean_object* v_motive_220_, lean_object* v_ctorIdx_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_k_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim___redArg(v_t_222_, v_k_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim___boxed(lean_object* v_motive_226_, lean_object* v_ctorIdx_227_, lean_object* v_t_228_, lean_object* v_h_229_, lean_object* v_k_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim(v_motive_226_, v_ctorIdx_227_, v_t_228_, v_h_229_, v_k_230_);
lean_dec(v_ctorIdx_227_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_clean_elim___redArg(lean_object* v_t_232_, lean_object* v_clean_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim___redArg(v_t_232_, v_clean_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_clean_elim(lean_object* v_motive_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_clean_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim___redArg(v_t_236_, v_clean_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_failed_elim___redArg(lean_object* v_t_240_, lean_object* v_failed_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim___redArg(v_t_240_, v_failed_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_failed_elim(lean_object* v_motive_243_, lean_object* v_t_244_, lean_object* v_h_245_, lean_object* v_failed_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Ending_ctorElim___redArg(v_t_244_, v_failed_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0(lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
v_a_261_ = lean_ctor_get(v_x_259_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_269_ == 0)
{
v___x_263_ = v_x_259_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v_x_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_268_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
v_a_270_ = lean_ctor_get(v_x_259_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_278_ == 0)
{
v___x_272_ = v_x_259_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v_x_259_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_277_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___lam__0___boxed(lean_object* v_x_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_Http_Body_mkStream___lam__0(v_x_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream(){
_start:
{
lean_object* v___f_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___f_287_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__0));
v___x_288_ = 0;
v___x_289_ = ((lean_object*)(l_Std_Http_Body_mkStream___closed__1));
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = l_Std_Mutex_new___redArg(v___x_289_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
v___x_294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_290_, v___x_288_, v___x_293_, v___f_287_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_mkStream___boxed(lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Http_Body_mkStream();
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(lean_object* v_knownSize_297_, lean_object* v_chunk_298_){
_start:
{
if (lean_obj_tag(v_knownSize_297_) == 1)
{
lean_object* v_val_299_; 
v_val_299_ = lean_ctor_get(v_knownSize_297_, 0);
lean_inc(v_val_299_);
if (lean_obj_tag(v_val_299_) == 1)
{
lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_317_; 
v_isSharedCheck_317_ = !lean_is_exclusive(v_knownSize_297_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_knownSize_297_, 0);
lean_dec(v_unused_318_);
v___x_301_ = v_knownSize_297_;
v_isShared_302_ = v_isSharedCheck_317_;
goto v_resetjp_300_;
}
else
{
lean_dec(v_knownSize_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_317_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_n_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_316_; 
v_n_303_ = lean_ctor_get(v_val_299_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v_val_299_);
if (v_isSharedCheck_316_ == 0)
{
v___x_305_ = v_val_299_;
v_isShared_306_ = v_isSharedCheck_316_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_n_303_);
lean_dec(v_val_299_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_316_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_data_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v_data_307_ = lean_ctor_get(v_chunk_298_, 0);
v___x_308_ = lean_byte_array_size(v_data_307_);
v___x_309_ = lean_nat_sub(v_n_303_, v___x_308_);
lean_dec(v_n_303_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_309_);
v___x_311_ = v___x_305_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_311_);
v___x_313_ = v___x_301_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_dec(v_val_299_);
return v_knownSize_297_;
}
}
else
{
return v_knownSize_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(lean_object* v_knownSize_319_, lean_object* v_chunk_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_319_, v_chunk_320_);
lean_dec_ref(v_chunk_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(lean_object* v_pendingProducer_322_, lean_object* v_pendingConsumer_323_, lean_object* v_ended_324_, lean_object* v_knownSize_325_, lean_object* v_pendingIncomplete_326_, uint8_t v_closeAfterProducer_327_, lean_object* v_inst_328_, lean_object* v_interestWaiter_329_, lean_object* v___y_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_331_, 0, v_pendingProducer_322_);
lean_ctor_set(v___x_331_, 1, v_pendingConsumer_323_);
lean_ctor_set(v___x_331_, 2, v_interestWaiter_329_);
lean_ctor_set(v___x_331_, 3, v_ended_324_);
lean_ctor_set(v___x_331_, 4, v_knownSize_325_);
lean_ctor_set(v___x_331_, 5, v_pendingIncomplete_326_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*6, v_closeAfterProducer_327_);
lean_inc(v___y_330_);
v___x_332_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_332_, 0, lean_box(0));
lean_closure_set(v___x_332_, 1, lean_box(0));
lean_closure_set(v___x_332_, 2, v___y_330_);
lean_closure_set(v___x_332_, 3, v___x_331_);
v___x_333_ = lean_apply_2(v_inst_328_, lean_box(0), v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(lean_object* v_pendingProducer_334_, lean_object* v_pendingConsumer_335_, lean_object* v_ended_336_, lean_object* v_knownSize_337_, lean_object* v_pendingIncomplete_338_, lean_object* v_closeAfterProducer_339_, lean_object* v_inst_340_, lean_object* v_interestWaiter_341_, lean_object* v___y_342_){
_start:
{
uint8_t v_closeAfterProducer_boxed_343_; lean_object* v_res_344_; 
v_closeAfterProducer_boxed_343_ = lean_unbox(v_closeAfterProducer_339_);
v_res_344_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(v_pendingProducer_334_, v_pendingConsumer_335_, v_ended_336_, v_knownSize_337_, v_pendingIncomplete_338_, v_closeAfterProducer_boxed_343_, v_inst_340_, v_interestWaiter_341_, v___y_342_);
lean_dec(v___y_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(lean_object* v___f_345_, lean_object* v___y_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_348_; 
lean_inc(v___y_346_);
v___x_348_ = lean_apply_2(v___f_345_, v_a_347_, v___y_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(lean_object* v___f_349_, lean_object* v___y_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(v___f_349_, v___y_350_, v_a_351_);
lean_dec(v___y_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(lean_object* v_toApplicative_353_, lean_object* v_interestWaiter_354_, lean_object* v_toBind_355_, lean_object* v___f_356_, lean_object* v___f_357_, uint8_t v_a_358_){
_start:
{
if (v_a_358_ == 0)
{
lean_object* v_toPure_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___f_357_);
v_toPure_359_ = lean_ctor_get(v_toApplicative_353_, 1);
lean_inc(v_toPure_359_);
lean_dec_ref(v_toApplicative_353_);
v___x_360_ = lean_apply_2(v_toPure_359_, lean_box(0), v_interestWaiter_354_);
v___x_361_ = lean_apply_4(v_toBind_355_, lean_box(0), lean_box(0), v___x_360_, v___f_356_);
return v___x_361_;
}
else
{
lean_object* v_toPure_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v___f_356_);
lean_dec(v_interestWaiter_354_);
v_toPure_362_ = lean_ctor_get(v_toApplicative_353_, 1);
lean_inc(v_toPure_362_);
lean_dec_ref(v_toApplicative_353_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_apply_2(v_toPure_362_, lean_box(0), v___x_363_);
v___x_365_ = lean_apply_4(v_toBind_355_, lean_box(0), lean_box(0), v___x_364_, v___f_357_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(lean_object* v_toApplicative_366_, lean_object* v_interestWaiter_367_, lean_object* v_toBind_368_, lean_object* v___f_369_, lean_object* v___f_370_, lean_object* v_a_371_){
_start:
{
uint8_t v_a_boxed_372_; lean_object* v_res_373_; 
v_a_boxed_372_ = lean_unbox(v_a_371_);
v_res_373_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(v_toApplicative_366_, v_interestWaiter_367_, v_toBind_368_, v___f_369_, v___f_370_, v_a_boxed_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(lean_object* v_pendingProducer_374_, lean_object* v_ended_375_, lean_object* v_knownSize_376_, lean_object* v_pendingIncomplete_377_, uint8_t v_closeAfterProducer_378_, lean_object* v_inst_379_, lean_object* v_interestWaiter_380_, lean_object* v_toApplicative_381_, lean_object* v_toBind_382_, lean_object* v_pendingConsumer_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___f_386_; 
v___x_385_ = lean_box(v_closeAfterProducer_378_);
lean_inc(v_inst_379_);
v___f_386_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed), 9, 7);
lean_closure_set(v___f_386_, 0, v_pendingProducer_374_);
lean_closure_set(v___f_386_, 1, v_pendingConsumer_383_);
lean_closure_set(v___f_386_, 2, v_ended_375_);
lean_closure_set(v___f_386_, 3, v_knownSize_376_);
lean_closure_set(v___f_386_, 4, v_pendingIncomplete_377_);
lean_closure_set(v___f_386_, 5, v___x_385_);
lean_closure_set(v___f_386_, 6, v_inst_379_);
if (lean_obj_tag(v_interestWaiter_380_) == 0)
{
lean_object* v_toPure_387_; lean_object* v___f_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_inst_379_);
v_toPure_387_ = lean_ctor_get(v_toApplicative_381_, 1);
lean_inc(v_toPure_387_);
lean_dec_ref(v_toApplicative_381_);
lean_inc(v___y_384_);
v___f_388_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_388_, 0, v___f_386_);
lean_closure_set(v___f_388_, 1, v___y_384_);
v___x_389_ = lean_apply_2(v_toPure_387_, lean_box(0), v_interestWaiter_380_);
v___x_390_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v___x_389_, v___f_388_);
return v___x_390_;
}
else
{
lean_object* v_val_391_; lean_object* v_finished_392_; lean_object* v___f_393_; lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_val_391_ = lean_ctor_get(v_interestWaiter_380_, 0);
v_finished_392_ = lean_ctor_get(v_val_391_, 0);
lean_inc(v_finished_392_);
lean_inc(v___y_384_);
v___f_393_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_393_, 0, v___f_386_);
lean_closure_set(v___f_393_, 1, v___y_384_);
lean_inc_ref(v___f_393_);
lean_inc(v_toBind_382_);
v___f_394_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_394_, 0, v_toApplicative_381_);
lean_closure_set(v___f_394_, 1, v_interestWaiter_380_);
lean_closure_set(v___f_394_, 2, v_toBind_382_);
lean_closure_set(v___f_394_, 3, v___f_393_);
lean_closure_set(v___f_394_, 4, v___f_393_);
v___x_395_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_395_, 0, lean_box(0));
lean_closure_set(v___x_395_, 1, lean_box(0));
lean_closure_set(v___x_395_, 2, v_finished_392_);
v___x_396_ = lean_apply_2(v_inst_379_, lean_box(0), v___x_395_);
v___x_397_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v___x_396_, v___f_394_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(lean_object* v_pendingProducer_398_, lean_object* v_ended_399_, lean_object* v_knownSize_400_, lean_object* v_pendingIncomplete_401_, lean_object* v_closeAfterProducer_402_, lean_object* v_inst_403_, lean_object* v_interestWaiter_404_, lean_object* v_toApplicative_405_, lean_object* v_toBind_406_, lean_object* v_pendingConsumer_407_, lean_object* v___y_408_){
_start:
{
uint8_t v_closeAfterProducer_boxed_409_; lean_object* v_res_410_; 
v_closeAfterProducer_boxed_409_ = lean_unbox(v_closeAfterProducer_402_);
v_res_410_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(v_pendingProducer_398_, v_ended_399_, v_knownSize_400_, v_pendingIncomplete_401_, v_closeAfterProducer_boxed_409_, v_inst_403_, v_interestWaiter_404_, v_toApplicative_405_, v_toBind_406_, v_pendingConsumer_407_, v___y_408_);
lean_dec(v___y_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(lean_object* v___f_411_, lean_object* v___y_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; 
lean_inc(v___y_412_);
v___x_414_ = lean_apply_2(v___f_411_, v_a_413_, v___y_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(lean_object* v___f_415_, lean_object* v___y_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(v___f_415_, v___y_416_, v_a_417_);
lean_dec(v___y_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(lean_object* v___f_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_422_; 
lean_inc(v_a_420_);
v___x_422_ = lean_apply_2(v___f_419_, v_a_421_, v_a_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(lean_object* v___f_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(v___f_423_, v_a_424_, v_a_425_);
lean_dec(v_a_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(lean_object* v_toApplicative_427_, lean_object* v_pendingConsumer_428_, lean_object* v_toBind_429_, lean_object* v___f_430_, lean_object* v___f_431_, uint8_t v_a_432_){
_start:
{
if (v_a_432_ == 0)
{
lean_object* v_toPure_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v___f_431_);
v_toPure_433_ = lean_ctor_get(v_toApplicative_427_, 1);
lean_inc(v_toPure_433_);
lean_dec_ref(v_toApplicative_427_);
v___x_434_ = lean_apply_2(v_toPure_433_, lean_box(0), v_pendingConsumer_428_);
v___x_435_ = lean_apply_4(v_toBind_429_, lean_box(0), lean_box(0), v___x_434_, v___f_430_);
return v___x_435_;
}
else
{
lean_object* v_toPure_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v___f_430_);
lean_dec(v_pendingConsumer_428_);
v_toPure_436_ = lean_ctor_get(v_toApplicative_427_, 1);
lean_inc(v_toPure_436_);
lean_dec_ref(v_toApplicative_427_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_apply_2(v_toPure_436_, lean_box(0), v___x_437_);
v___x_439_ = lean_apply_4(v_toBind_429_, lean_box(0), lean_box(0), v___x_438_, v___f_431_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(lean_object* v_toApplicative_440_, lean_object* v_pendingConsumer_441_, lean_object* v_toBind_442_, lean_object* v___f_443_, lean_object* v___f_444_, lean_object* v_a_445_){
_start:
{
uint8_t v_a_boxed_446_; lean_object* v_res_447_; 
v_a_boxed_446_ = lean_unbox(v_a_445_);
v_res_447_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(v_toApplicative_440_, v_pendingConsumer_441_, v_toBind_442_, v___f_443_, v___f_444_, v_a_boxed_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(lean_object* v_inst_448_, lean_object* v_toApplicative_449_, lean_object* v_toBind_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_pendingProducer_453_; lean_object* v_pendingConsumer_454_; lean_object* v_interestWaiter_455_; lean_object* v_ended_456_; lean_object* v_knownSize_457_; lean_object* v_pendingIncomplete_458_; uint8_t v_closeAfterProducer_459_; lean_object* v___x_460_; lean_object* v___f_461_; lean_object* v___y_463_; 
v_pendingProducer_453_ = lean_ctor_get(v_a_452_, 0);
lean_inc(v_pendingProducer_453_);
v_pendingConsumer_454_ = lean_ctor_get(v_a_452_, 1);
lean_inc(v_pendingConsumer_454_);
v_interestWaiter_455_ = lean_ctor_get(v_a_452_, 2);
lean_inc(v_interestWaiter_455_);
v_ended_456_ = lean_ctor_get(v_a_452_, 3);
lean_inc(v_ended_456_);
v_knownSize_457_ = lean_ctor_get(v_a_452_, 4);
lean_inc(v_knownSize_457_);
v_pendingIncomplete_458_ = lean_ctor_get(v_a_452_, 5);
lean_inc(v_pendingIncomplete_458_);
v_closeAfterProducer_459_ = lean_ctor_get_uint8(v_a_452_, sizeof(void*)*6);
lean_dec_ref(v_a_452_);
v___x_460_ = lean_box(v_closeAfterProducer_459_);
lean_inc(v_toBind_450_);
lean_inc_ref(v_toApplicative_449_);
lean_inc(v_inst_448_);
v___f_461_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_461_, 0, v_pendingProducer_453_);
lean_closure_set(v___f_461_, 1, v_ended_456_);
lean_closure_set(v___f_461_, 2, v_knownSize_457_);
lean_closure_set(v___f_461_, 3, v_pendingIncomplete_458_);
lean_closure_set(v___f_461_, 4, v___x_460_);
lean_closure_set(v___f_461_, 5, v_inst_448_);
lean_closure_set(v___f_461_, 6, v_interestWaiter_455_);
lean_closure_set(v___f_461_, 7, v_toApplicative_449_);
lean_closure_set(v___f_461_, 8, v_toBind_450_);
if (lean_obj_tag(v_pendingConsumer_454_) == 1)
{
lean_object* v_val_468_; 
v_val_468_ = lean_ctor_get(v_pendingConsumer_454_, 0);
if (lean_obj_tag(v_val_468_) == 1)
{
lean_object* v_finished_469_; lean_object* v_finished_470_; lean_object* v___f_471_; lean_object* v___f_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_finished_469_ = lean_ctor_get(v_val_468_, 0);
v_finished_470_ = lean_ctor_get(v_finished_469_, 0);
lean_inc(v_finished_470_);
lean_inc(v_a_451_);
v___f_471_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_471_, 0, v___f_461_);
lean_closure_set(v___f_471_, 1, v_a_451_);
lean_inc_ref(v___f_471_);
lean_inc(v_toBind_450_);
v___f_472_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_472_, 0, v_toApplicative_449_);
lean_closure_set(v___f_472_, 1, v_pendingConsumer_454_);
lean_closure_set(v___f_472_, 2, v_toBind_450_);
lean_closure_set(v___f_472_, 3, v___f_471_);
lean_closure_set(v___f_472_, 4, v___f_471_);
v___x_473_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_473_, 0, lean_box(0));
lean_closure_set(v___x_473_, 1, lean_box(0));
lean_closure_set(v___x_473_, 2, v_finished_470_);
v___x_474_ = lean_apply_2(v_inst_448_, lean_box(0), v___x_473_);
v___x_475_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v___x_474_, v___f_472_);
return v___x_475_;
}
else
{
lean_dec(v_inst_448_);
v___y_463_ = v_a_451_;
goto v___jp_462_;
}
}
else
{
lean_dec(v_inst_448_);
v___y_463_ = v_a_451_;
goto v___jp_462_;
}
v___jp_462_:
{
lean_object* v_toPure_464_; lean_object* v___f_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_toPure_464_ = lean_ctor_get(v_toApplicative_449_, 1);
lean_inc(v_toPure_464_);
lean_dec_ref(v_toApplicative_449_);
lean_inc(v___y_463_);
v___f_465_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_465_, 0, v___f_461_);
lean_closure_set(v___f_465_, 1, v___y_463_);
v___x_466_ = lean_apply_2(v_toPure_464_, lean_box(0), v_pendingConsumer_454_);
v___x_467_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v___x_466_, v___f_465_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(lean_object* v_inst_476_, lean_object* v_toApplicative_477_, lean_object* v_toBind_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(v_inst_476_, v_toApplicative_477_, v_toBind_478_, v_a_479_, v_a_480_);
lean_dec(v_a_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_toApplicative_485_; lean_object* v_toBind_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_toApplicative_485_ = lean_ctor_get(v_inst_482_, 0);
lean_inc_ref(v_toApplicative_485_);
v_toBind_486_ = lean_ctor_get(v_inst_482_, 1);
lean_inc_n(v_toBind_486_, 2);
lean_dec_ref(v_inst_482_);
lean_inc_n(v_a_484_, 2);
lean_inc(v_inst_483_);
v___f_487_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_487_, 0, v_inst_483_);
lean_closure_set(v___f_487_, 1, v_toApplicative_485_);
lean_closure_set(v___f_487_, 2, v_toBind_486_);
lean_closure_set(v___f_487_, 3, v_a_484_);
v___x_488_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_488_, 0, lean_box(0));
lean_closure_set(v___x_488_, 1, lean_box(0));
lean_closure_set(v___x_488_, 2, v_a_484_);
v___x_489_ = lean_apply_2(v_inst_483_, lean_box(0), v___x_488_);
v___x_490_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v___x_489_, v___f_487_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_491_, v_inst_492_, v_a_493_);
lean_dec(v_a_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(lean_object* v_m_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_496_, v_inst_497_, v_a_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(lean_object* v_m_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(v_m_500_, v_inst_501_, v_inst_502_, v_a_503_);
lean_dec(v_a_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(lean_object* v_pendingProducer_505_, lean_object* v_pendingConsumer_506_, lean_object* v_ended_507_, lean_object* v_knownSize_508_, lean_object* v_pendingIncomplete_509_, uint8_t v_closeAfterProducer_510_, lean_object* v_a_511_, lean_object* v_inst_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_514_ = lean_box(0);
v___x_515_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_515_, 0, v_pendingProducer_505_);
lean_ctor_set(v___x_515_, 1, v_pendingConsumer_506_);
lean_ctor_set(v___x_515_, 2, v___x_514_);
lean_ctor_set(v___x_515_, 3, v_ended_507_);
lean_ctor_set(v___x_515_, 4, v_knownSize_508_);
lean_ctor_set(v___x_515_, 5, v_pendingIncomplete_509_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*6, v_closeAfterProducer_510_);
lean_inc(v_a_511_);
v___x_516_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_516_, 0, lean_box(0));
lean_closure_set(v___x_516_, 1, lean_box(0));
lean_closure_set(v___x_516_, 2, v_a_511_);
lean_closure_set(v___x_516_, 3, v___x_515_);
v___x_517_ = lean_apply_2(v_inst_512_, lean_box(0), v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(lean_object* v_pendingProducer_518_, lean_object* v_pendingConsumer_519_, lean_object* v_ended_520_, lean_object* v_knownSize_521_, lean_object* v_pendingIncomplete_522_, lean_object* v_closeAfterProducer_523_, lean_object* v_a_524_, lean_object* v_inst_525_, lean_object* v_a_526_){
_start:
{
uint8_t v_closeAfterProducer_boxed_527_; lean_object* v_res_528_; 
v_closeAfterProducer_boxed_527_ = lean_unbox(v_closeAfterProducer_523_);
v_res_528_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(v_pendingProducer_518_, v_pendingConsumer_519_, v_ended_520_, v_knownSize_521_, v_pendingIncomplete_522_, v_closeAfterProducer_boxed_527_, v_a_524_, v_inst_525_, v_a_526_);
lean_dec(v_a_524_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(lean_object* v_toApplicative_529_, lean_object* v_a_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_toBind_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_interestWaiter_535_; 
v_interestWaiter_535_ = lean_ctor_get(v_a_534_, 2);
lean_inc(v_interestWaiter_535_);
if (lean_obj_tag(v_interestWaiter_535_) == 1)
{
lean_object* v_toFunctor_536_; lean_object* v_pendingProducer_537_; lean_object* v_pendingConsumer_538_; lean_object* v_ended_539_; lean_object* v_knownSize_540_; lean_object* v_pendingIncomplete_541_; uint8_t v_closeAfterProducer_542_; lean_object* v_val_543_; lean_object* v_mapConst_544_; lean_object* v___x_545_; lean_object* v___f_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_toFunctor_536_ = lean_ctor_get(v_toApplicative_529_, 0);
lean_inc_ref(v_toFunctor_536_);
lean_dec_ref(v_toApplicative_529_);
v_pendingProducer_537_ = lean_ctor_get(v_a_534_, 0);
lean_inc(v_pendingProducer_537_);
v_pendingConsumer_538_ = lean_ctor_get(v_a_534_, 1);
lean_inc(v_pendingConsumer_538_);
v_ended_539_ = lean_ctor_get(v_a_534_, 3);
lean_inc(v_ended_539_);
v_knownSize_540_ = lean_ctor_get(v_a_534_, 4);
lean_inc(v_knownSize_540_);
v_pendingIncomplete_541_ = lean_ctor_get(v_a_534_, 5);
lean_inc(v_pendingIncomplete_541_);
v_closeAfterProducer_542_ = lean_ctor_get_uint8(v_a_534_, sizeof(void*)*6);
lean_dec_ref(v_a_534_);
v_val_543_ = lean_ctor_get(v_interestWaiter_535_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_interestWaiter_535_, 1);
v_mapConst_544_ = lean_ctor_get(v_toFunctor_536_, 1);
lean_inc(v_mapConst_544_);
lean_dec_ref(v_toFunctor_536_);
v___x_545_ = lean_box(v_closeAfterProducer_542_);
lean_inc(v_a_530_);
v___f_546_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_546_, 0, v_pendingProducer_537_);
lean_closure_set(v___f_546_, 1, v_pendingConsumer_538_);
lean_closure_set(v___f_546_, 2, v_ended_539_);
lean_closure_set(v___f_546_, 3, v_knownSize_540_);
lean_closure_set(v___f_546_, 4, v_pendingIncomplete_541_);
lean_closure_set(v___f_546_, 5, v___x_545_);
lean_closure_set(v___f_546_, 6, v_a_530_);
lean_closure_set(v___f_546_, 7, v_inst_531_);
v___x_547_ = 1;
v___x_548_ = lean_box(v___x_547_);
v___x_549_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_549_, 0, v_val_543_);
lean_closure_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_apply_2(v_inst_532_, lean_box(0), v___x_549_);
v___x_551_ = lean_box(0);
v___x_552_ = lean_apply_4(v_mapConst_544_, lean_box(0), lean_box(0), v___x_551_, v___x_550_);
v___x_553_ = lean_apply_4(v_toBind_533_, lean_box(0), lean_box(0), v___x_552_, v___f_546_);
return v___x_553_;
}
else
{
lean_object* v_toPure_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_interestWaiter_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_toBind_533_);
lean_dec(v_inst_532_);
lean_dec(v_inst_531_);
v_toPure_554_ = lean_ctor_get(v_toApplicative_529_, 1);
lean_inc(v_toPure_554_);
lean_dec_ref(v_toApplicative_529_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_apply_2(v_toPure_554_, lean_box(0), v___x_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(lean_object* v_toApplicative_557_, lean_object* v_a_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_toBind_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(v_toApplicative_557_, v_a_558_, v_inst_559_, v_inst_560_, v_toBind_561_, v_a_562_);
lean_dec(v_a_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_toApplicative_568_; lean_object* v_toBind_569_; lean_object* v___f_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_toApplicative_568_ = lean_ctor_get(v_inst_564_, 0);
lean_inc_ref(v_toApplicative_568_);
v_toBind_569_ = lean_ctor_get(v_inst_564_, 1);
lean_inc_n(v_toBind_569_, 2);
lean_dec_ref(v_inst_564_);
lean_inc(v_inst_565_);
lean_inc_n(v_a_567_, 2);
v___f_570_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_570_, 0, v_toApplicative_568_);
lean_closure_set(v___f_570_, 1, v_a_567_);
lean_closure_set(v___f_570_, 2, v_inst_565_);
lean_closure_set(v___f_570_, 3, v_inst_566_);
lean_closure_set(v___f_570_, 4, v_toBind_569_);
v___x_571_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_571_, 0, lean_box(0));
lean_closure_set(v___x_571_, 1, lean_box(0));
lean_closure_set(v___x_571_, 2, v_a_567_);
v___x_572_ = lean_apply_2(v_inst_565_, lean_box(0), v___x_571_);
v___x_573_ = lean_apply_4(v_toBind_569_, lean_box(0), lean_box(0), v___x_572_, v___f_570_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_574_, v_inst_575_, v_inst_576_, v_a_577_);
lean_dec(v_a_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(lean_object* v_m_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(v_inst_580_, v_inst_581_, v_inst_582_, v_a_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(lean_object* v_m_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(v_m_585_, v_inst_586_, v_inst_587_, v_inst_588_, v_a_589_);
lean_dec(v_a_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_591_, lean_object* v_a_592_){
_start:
{
uint8_t v___y_594_; lean_object* v_pendingProducer_598_; 
v_pendingProducer_598_ = lean_ctor_get(v_a_592_, 0);
if (lean_obj_tag(v_pendingProducer_598_) == 0)
{
lean_object* v_ended_599_; 
v_ended_599_ = lean_ctor_get(v_a_592_, 3);
if (lean_obj_tag(v_ended_599_) == 0)
{
uint8_t v___x_600_; 
v___x_600_ = 0;
v___y_594_ = v___x_600_;
goto v___jp_593_;
}
else
{
uint8_t v___x_601_; 
v___x_601_ = 1;
v___y_594_ = v___x_601_;
goto v___jp_593_;
}
}
else
{
uint8_t v___x_602_; 
v___x_602_ = 1;
v___y_594_ = v___x_602_;
goto v___jp_593_;
}
v___jp_593_:
{
lean_object* v_toPure_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_toPure_595_ = lean_ctor_get(v_toApplicative_591_, 1);
lean_inc(v_toPure_595_);
lean_dec_ref(v_toApplicative_591_);
v___x_596_ = lean_box(v___y_594_);
v___x_597_ = lean_apply_2(v_toPure_595_, lean_box(0), v___x_596_);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(v_toApplicative_603_, v_a_604_);
lean_dec_ref(v_a_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_toApplicative_609_; lean_object* v_toBind_610_; lean_object* v___f_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_toApplicative_609_ = lean_ctor_get(v_inst_606_, 0);
lean_inc_ref(v_toApplicative_609_);
v_toBind_610_ = lean_ctor_get(v_inst_606_, 1);
lean_inc(v_toBind_610_);
lean_dec_ref(v_inst_606_);
v___f_611_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_611_, 0, v_toApplicative_609_);
lean_inc(v_a_608_);
v___x_612_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_612_, 0, lean_box(0));
lean_closure_set(v___x_612_, 1, lean_box(0));
lean_closure_set(v___x_612_, 2, v_a_608_);
v___x_613_ = lean_apply_2(v_inst_607_, lean_box(0), v___x_612_);
v___x_614_ = lean_apply_4(v_toBind_610_, lean_box(0), lean_box(0), v___x_613_, v___f_611_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_615_, v_inst_616_, v_a_617_);
lean_dec(v_a_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(lean_object* v_m_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(v_inst_620_, v_inst_621_, v_a_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(lean_object* v_m_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(v_m_624_, v_inst_625_, v_inst_626_, v_a_627_);
lean_dec(v_a_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(lean_object* v_toApplicative_629_, lean_object* v_a_630_){
_start:
{
uint8_t v___y_632_; lean_object* v_pendingConsumer_636_; 
v_pendingConsumer_636_ = lean_ctor_get(v_a_630_, 1);
if (lean_obj_tag(v_pendingConsumer_636_) == 0)
{
uint8_t v___x_637_; 
v___x_637_ = 0;
v___y_632_ = v___x_637_;
goto v___jp_631_;
}
else
{
uint8_t v___x_638_; 
v___x_638_ = 1;
v___y_632_ = v___x_638_;
goto v___jp_631_;
}
v___jp_631_:
{
lean_object* v_toPure_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_toPure_633_ = lean_ctor_get(v_toApplicative_629_, 1);
lean_inc(v_toPure_633_);
lean_dec_ref(v_toApplicative_629_);
v___x_634_ = lean_box(v___y_632_);
v___x_635_ = lean_apply_2(v_toPure_633_, lean_box(0), v___x_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(v_toApplicative_639_, v_a_640_);
lean_dec_ref(v_a_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_toApplicative_645_; lean_object* v_toBind_646_; lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_toApplicative_645_ = lean_ctor_get(v_inst_642_, 0);
lean_inc_ref(v_toApplicative_645_);
v_toBind_646_ = lean_ctor_get(v_inst_642_, 1);
lean_inc(v_toBind_646_);
lean_dec_ref(v_inst_642_);
v___f_647_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_647_, 0, v_toApplicative_645_);
lean_inc(v_a_644_);
v___x_648_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_648_, 0, lean_box(0));
lean_closure_set(v___x_648_, 1, lean_box(0));
lean_closure_set(v___x_648_, 2, v_a_644_);
v___x_649_ = lean_apply_2(v_inst_643_, lean_box(0), v___x_648_);
v___x_650_ = lean_apply_4(v_toBind_646_, lean_box(0), lean_box(0), v___x_649_, v___f_647_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_651_, v_inst_652_, v_a_653_);
lean_dec(v_a_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(lean_object* v_m_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(v_inst_656_, v_inst_657_, v_a_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(lean_object* v_m_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(v_m_660_, v_inst_661_, v_inst_662_, v_a_663_);
lean_dec(v_a_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(lean_object* v_val_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v_val_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(lean_object* v_ending_667_, lean_object* v_knownSize_668_, uint8_t v___x_669_, lean_object* v___y_670_, lean_object* v_inst_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_673_ = lean_box(0);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_ending_667_);
v___x_675_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_675_, 0, v_a_672_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
lean_ctor_set(v___x_675_, 2, v___x_673_);
lean_ctor_set(v___x_675_, 3, v___x_674_);
lean_ctor_set(v___x_675_, 4, v_knownSize_668_);
lean_ctor_set(v___x_675_, 5, v___x_673_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*6, v___x_669_);
lean_inc(v___y_670_);
v___x_676_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_676_, 0, lean_box(0));
lean_closure_set(v___x_676_, 1, lean_box(0));
lean_closure_set(v___x_676_, 2, v___y_670_);
lean_closure_set(v___x_676_, 3, v___x_675_);
v___x_677_ = lean_apply_2(v_inst_671_, lean_box(0), v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(lean_object* v_ending_678_, lean_object* v_knownSize_679_, lean_object* v___x_680_, lean_object* v___y_681_, lean_object* v_inst_682_, lean_object* v_a_683_){
_start:
{
uint8_t v___x_1468__boxed_684_; lean_object* v_res_685_; 
v___x_1468__boxed_684_ = lean_unbox(v___x_680_);
v_res_685_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(v_ending_678_, v_knownSize_679_, v___x_1468__boxed_684_, v___y_681_, v_inst_682_, v_a_683_);
lean_dec(v___y_681_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(lean_object* v_val_686_, lean_object* v_toPure_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_val_686_);
lean_ctor_set(v___x_689_, 1, v_a_688_);
v___x_690_ = lean_apply_2(v_toPure_687_, lean_box(0), v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(lean_object* v_ending_692_, lean_object* v_knownSize_693_, uint8_t v___x_694_, lean_object* v_inst_695_, lean_object* v_leftover_696_, lean_object* v_toApplicative_697_, lean_object* v_toBind_698_, lean_object* v_inst_699_, lean_object* v___f_700_, lean_object* v_____r_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_703_; lean_object* v___f_704_; 
v___x_703_ = lean_box(v___x_694_);
lean_inc(v___y_702_);
v___f_704_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_704_, 0, v_ending_692_);
lean_closure_set(v___f_704_, 1, v_knownSize_693_);
lean_closure_set(v___f_704_, 2, v___x_703_);
lean_closure_set(v___f_704_, 3, v___y_702_);
lean_closure_set(v___f_704_, 4, v_inst_695_);
if (lean_obj_tag(v_leftover_696_) == 0)
{
lean_object* v_toPure_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec_ref(v___f_700_);
lean_dec(v_inst_699_);
v_toPure_705_ = lean_ctor_get(v_toApplicative_697_, 1);
lean_inc(v_toPure_705_);
lean_dec_ref(v_toApplicative_697_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_apply_2(v_toPure_705_, lean_box(0), v___x_706_);
v___x_708_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v___x_707_, v___f_704_);
return v___x_708_;
}
else
{
lean_object* v_toFunctor_709_; lean_object* v_val_710_; lean_object* v_toPure_711_; lean_object* v_map_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_toFunctor_709_ = lean_ctor_get(v_toApplicative_697_, 0);
lean_inc_ref(v_toFunctor_709_);
v_val_710_ = lean_ctor_get(v_leftover_696_, 0);
lean_inc(v_val_710_);
lean_dec_ref_known(v_leftover_696_, 1);
v_toPure_711_ = lean_ctor_get(v_toApplicative_697_, 1);
lean_inc(v_toPure_711_);
lean_dec_ref(v_toApplicative_697_);
v_map_712_ = lean_ctor_get(v_toFunctor_709_, 0);
lean_inc(v_map_712_);
lean_dec_ref(v_toFunctor_709_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_713_, 0, v_val_710_);
lean_closure_set(v___f_713_, 1, v_toPure_711_);
v___x_714_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___closed__0));
v___x_715_ = lean_apply_2(v_inst_699_, lean_box(0), v___x_714_);
lean_inc(v_toBind_698_);
v___x_716_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v___x_715_, v___f_713_);
v___x_717_ = lean_apply_4(v_map_712_, lean_box(0), lean_box(0), v___f_700_, v___x_716_);
v___x_718_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v___x_717_, v___f_704_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(lean_object* v_ending_719_, lean_object* v_knownSize_720_, lean_object* v___x_721_, lean_object* v_inst_722_, lean_object* v_leftover_723_, lean_object* v_toApplicative_724_, lean_object* v_toBind_725_, lean_object* v_inst_726_, lean_object* v___f_727_, lean_object* v_____r_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___x_1495__boxed_730_; lean_object* v_res_731_; 
v___x_1495__boxed_730_ = lean_unbox(v___x_721_);
v_res_731_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(v_ending_719_, v_knownSize_720_, v___x_1495__boxed_730_, v_inst_722_, v_leftover_723_, v_toApplicative_724_, v_toBind_725_, v_inst_726_, v___f_727_, v_____r_728_, v___y_729_);
lean_dec(v___y_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(lean_object* v___f_732_, lean_object* v___y_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_735_; 
lean_inc(v___y_733_);
v___x_735_ = lean_apply_2(v___f_732_, v_a_734_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(lean_object* v___f_736_, lean_object* v___y_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v___f_736_, v___y_737_, v_a_738_);
lean_dec(v___y_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(lean_object* v_pendingProducer_740_, lean_object* v_toApplicative_741_, lean_object* v___f_742_, uint8_t v___x_743_, lean_object* v_inst_744_, lean_object* v_toBind_745_, lean_object* v_____r_746_, lean_object* v___y_747_){
_start:
{
if (lean_obj_tag(v_pendingProducer_740_) == 1)
{
lean_object* v_val_748_; lean_object* v_toFunctor_749_; lean_object* v_done_750_; lean_object* v_mapConst_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_val_748_ = lean_ctor_get(v_pendingProducer_740_, 0);
lean_inc(v_val_748_);
lean_dec_ref_known(v_pendingProducer_740_, 1);
v_toFunctor_749_ = lean_ctor_get(v_toApplicative_741_, 0);
lean_inc_ref(v_toFunctor_749_);
lean_dec_ref(v_toApplicative_741_);
v_done_750_ = lean_ctor_get(v_val_748_, 1);
lean_inc(v_done_750_);
lean_dec(v_val_748_);
v_mapConst_751_ = lean_ctor_get(v_toFunctor_749_, 1);
lean_inc(v_mapConst_751_);
lean_dec_ref(v_toFunctor_749_);
lean_inc(v___y_747_);
v___f_752_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_752_, 0, v___f_742_);
lean_closure_set(v___f_752_, 1, v___y_747_);
v___x_753_ = lean_box(v___x_743_);
v___x_754_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_754_, 0, lean_box(0));
lean_closure_set(v___x_754_, 1, v___x_753_);
lean_closure_set(v___x_754_, 2, v_done_750_);
v___x_755_ = lean_apply_2(v_inst_744_, lean_box(0), v___x_754_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_apply_4(v_mapConst_751_, lean_box(0), lean_box(0), v___x_756_, v___x_755_);
v___x_758_ = lean_apply_4(v_toBind_745_, lean_box(0), lean_box(0), v___x_757_, v___f_752_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec(v_toBind_745_);
lean_dec(v_inst_744_);
lean_dec_ref(v_toApplicative_741_);
lean_dec(v_pendingProducer_740_);
v___x_759_ = lean_box(0);
lean_inc(v___y_747_);
v___x_760_ = lean_apply_2(v___f_742_, v___x_759_, v___y_747_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(lean_object* v_pendingProducer_761_, lean_object* v_toApplicative_762_, lean_object* v___f_763_, lean_object* v___x_764_, lean_object* v_inst_765_, lean_object* v_toBind_766_, lean_object* v_____r_767_, lean_object* v___y_768_){
_start:
{
uint8_t v___x_1547__boxed_769_; lean_object* v_res_770_; 
v___x_1547__boxed_769_ = lean_unbox(v___x_764_);
v_res_770_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(v_pendingProducer_761_, v_toApplicative_762_, v___f_763_, v___x_1547__boxed_769_, v_inst_765_, v_toBind_766_, v_____r_767_, v___y_768_);
lean_dec(v___y_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7(lean_object* v_ending_771_, uint8_t v___x_772_, lean_object* v_inst_773_, lean_object* v_toApplicative_774_, lean_object* v_toBind_775_, lean_object* v_inst_776_, lean_object* v___f_777_, lean_object* v_pendingProducer_778_, lean_object* v_interestWaiter_779_, lean_object* v_____r_780_, lean_object* v_leftover_781_, lean_object* v_knownSize_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___f_787_; 
v___x_784_ = lean_box(v___x_772_);
lean_inc_n(v_inst_776_, 2);
lean_inc_n(v_toBind_775_, 2);
lean_inc_ref_n(v_toApplicative_774_, 2);
v___f_785_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed), 11, 9);
lean_closure_set(v___f_785_, 0, v_ending_771_);
lean_closure_set(v___f_785_, 1, v_knownSize_782_);
lean_closure_set(v___f_785_, 2, v___x_784_);
lean_closure_set(v___f_785_, 3, v_inst_773_);
lean_closure_set(v___f_785_, 4, v_leftover_781_);
lean_closure_set(v___f_785_, 5, v_toApplicative_774_);
lean_closure_set(v___f_785_, 6, v_toBind_775_);
lean_closure_set(v___f_785_, 7, v_inst_776_);
lean_closure_set(v___f_785_, 8, v___f_777_);
v___x_786_ = lean_box(v___x_772_);
lean_inc_ref(v___f_785_);
lean_inc(v_pendingProducer_778_);
v___f_787_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_787_, 0, v_pendingProducer_778_);
lean_closure_set(v___f_787_, 1, v_toApplicative_774_);
lean_closure_set(v___f_787_, 2, v___f_785_);
lean_closure_set(v___f_787_, 3, v___x_786_);
lean_closure_set(v___f_787_, 4, v_inst_776_);
lean_closure_set(v___f_787_, 5, v_toBind_775_);
if (lean_obj_tag(v_interestWaiter_779_) == 1)
{
lean_object* v_toFunctor_788_; lean_object* v_val_789_; lean_object* v_mapConst_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v___f_785_);
lean_dec(v_pendingProducer_778_);
v_toFunctor_788_ = lean_ctor_get(v_toApplicative_774_, 0);
lean_inc_ref(v_toFunctor_788_);
lean_dec_ref(v_toApplicative_774_);
v_val_789_ = lean_ctor_get(v_interestWaiter_779_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_interestWaiter_779_, 1);
v_mapConst_790_ = lean_ctor_get(v_toFunctor_788_, 1);
lean_inc(v_mapConst_790_);
lean_dec_ref(v_toFunctor_788_);
lean_inc(v___y_783_);
v___f_791_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_791_, 0, v___f_787_);
lean_closure_set(v___f_791_, 1, v___y_783_);
v___x_792_ = lean_box(v___x_772_);
v___x_793_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed), 3, 2);
lean_closure_set(v___x_793_, 0, v_val_789_);
lean_closure_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_apply_2(v_inst_776_, lean_box(0), v___x_793_);
v___x_795_ = lean_box(0);
v___x_796_ = lean_apply_4(v_mapConst_790_, lean_box(0), lean_box(0), v___x_795_, v___x_794_);
v___x_797_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_796_, v___f_791_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v___f_787_);
lean_dec(v_interestWaiter_779_);
v___x_798_ = lean_box(0);
v___x_799_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(v_pendingProducer_778_, v_toApplicative_774_, v___f_785_, v___x_772_, v_inst_776_, v_toBind_775_, v___x_798_, v___y_783_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7___boxed(lean_object* v_ending_800_, lean_object* v___x_801_, lean_object* v_inst_802_, lean_object* v_toApplicative_803_, lean_object* v_toBind_804_, lean_object* v_inst_805_, lean_object* v___f_806_, lean_object* v_pendingProducer_807_, lean_object* v_interestWaiter_808_, lean_object* v_____r_809_, lean_object* v_leftover_810_, lean_object* v_knownSize_811_, lean_object* v___y_812_){
_start:
{
uint8_t v___x_1581__boxed_813_; lean_object* v_res_814_; 
v___x_1581__boxed_813_ = lean_unbox(v___x_801_);
v_res_814_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7(v_ending_800_, v___x_1581__boxed_813_, v_inst_802_, v_toApplicative_803_, v_toBind_804_, v_inst_805_, v___f_806_, v_pendingProducer_807_, v_interestWaiter_808_, v_____r_809_, v_leftover_810_, v_knownSize_811_, v___y_812_);
lean_dec(v___y_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6(lean_object* v___f_815_, lean_object* v___y_816_, lean_object* v_knownSize_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_820_; 
lean_inc(v_a_818_);
v___x_820_ = lean_apply_4(v___f_815_, v_a_819_, v___y_816_, v_knownSize_817_, v_a_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6___boxed(lean_object* v___f_821_, lean_object* v___y_822_, lean_object* v_knownSize_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6(v___f_821_, v___y_822_, v_knownSize_823_, v_a_824_, v_a_825_);
lean_dec(v_a_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8(lean_object* v___f_827_, lean_object* v___y_828_, lean_object* v_knownSize_829_, lean_object* v_a_830_, lean_object* v_val_831_, uint8_t v_a_832_){
_start:
{
if (v_a_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_box(0);
lean_inc(v_a_830_);
v___x_834_ = lean_apply_4(v___f_827_, v___x_833_, v___y_828_, v_knownSize_829_, v_a_830_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v___y_828_);
v___x_835_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_829_, v_val_831_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_box(0);
lean_inc(v_a_830_);
v___x_838_ = lean_apply_4(v___f_827_, v___x_837_, v___x_836_, v___x_835_, v_a_830_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8___boxed(lean_object* v___f_839_, lean_object* v___y_840_, lean_object* v_knownSize_841_, lean_object* v_a_842_, lean_object* v_val_843_, lean_object* v_a_844_){
_start:
{
uint8_t v_a_boxed_845_; lean_object* v_res_846_; 
v_a_boxed_845_ = lean_unbox(v_a_844_);
v_res_846_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8(v___f_839_, v___y_840_, v_knownSize_841_, v_a_842_, v_val_843_, v_a_boxed_845_);
lean_dec_ref(v_val_843_);
lean_dec(v_a_842_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9(lean_object* v_toApplicative_847_, lean_object* v_inst_848_, lean_object* v_toBind_849_, lean_object* v_ending_850_, lean_object* v_inst_851_, lean_object* v___f_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v_ended_866_; 
v_ended_866_ = lean_ctor_get(v_a_854_, 3);
if (lean_obj_tag(v_ended_866_) == 0)
{
lean_object* v_pendingProducer_867_; lean_object* v_pendingConsumer_868_; lean_object* v_interestWaiter_869_; lean_object* v_knownSize_870_; lean_object* v_pendingIncomplete_871_; uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___f_874_; lean_object* v___y_876_; 
v_pendingProducer_867_ = lean_ctor_get(v_a_854_, 0);
lean_inc_n(v_pendingProducer_867_, 2);
v_pendingConsumer_868_ = lean_ctor_get(v_a_854_, 1);
lean_inc(v_pendingConsumer_868_);
v_interestWaiter_869_ = lean_ctor_get(v_a_854_, 2);
lean_inc_n(v_interestWaiter_869_, 2);
v_knownSize_870_ = lean_ctor_get(v_a_854_, 4);
lean_inc(v_knownSize_870_);
v_pendingIncomplete_871_ = lean_ctor_get(v_a_854_, 5);
lean_inc(v_pendingIncomplete_871_);
lean_dec_ref(v_a_854_);
v___x_872_ = 0;
v___x_873_ = lean_box(v___x_872_);
lean_inc_ref(v___f_852_);
lean_inc(v_inst_848_);
lean_inc(v_toBind_849_);
lean_inc_ref(v_toApplicative_847_);
lean_inc(v_inst_851_);
lean_inc(v_ending_850_);
v___f_874_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7___boxed), 13, 9);
lean_closure_set(v___f_874_, 0, v_ending_850_);
lean_closure_set(v___f_874_, 1, v___x_873_);
lean_closure_set(v___f_874_, 2, v_inst_851_);
lean_closure_set(v___f_874_, 3, v_toApplicative_847_);
lean_closure_set(v___f_874_, 4, v_toBind_849_);
lean_closure_set(v___f_874_, 5, v_inst_848_);
lean_closure_set(v___f_874_, 6, v___f_852_);
lean_closure_set(v___f_874_, 7, v_pendingProducer_867_);
lean_closure_set(v___f_874_, 8, v_interestWaiter_869_);
if (lean_obj_tag(v_pendingProducer_867_) == 0)
{
if (lean_obj_tag(v_pendingIncomplete_871_) == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_box(0);
v___y_876_ = v___x_909_;
goto v___jp_875_;
}
else
{
lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_923_; 
v_val_910_ = lean_ctor_get(v_pendingIncomplete_871_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v_pendingIncomplete_871_);
if (v_isSharedCheck_923_ == 0)
{
v___x_912_ = v_pendingIncomplete_871_;
v_isShared_913_ = v_isSharedCheck_923_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_dec(v_pendingIncomplete_871_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_923_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v_data_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_914_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(v_val_910_);
v_data_915_ = lean_ctor_get(v___x_914_, 0);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_byte_array_size(v_data_915_);
v___x_918_ = lean_nat_dec_lt(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
lean_dec_ref(v___x_914_);
lean_del_object(v___x_912_);
v___x_919_ = lean_box(0);
v___y_876_ = v___x_919_;
goto v___jp_875_;
}
else
{
lean_object* v___x_921_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_921_ = v___x_912_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_914_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
v___y_876_ = v___x_921_;
goto v___jp_875_;
}
}
}
}
}
else
{
lean_object* v___x_924_; 
lean_dec(v_pendingIncomplete_871_);
v___x_924_ = lean_box(0);
v___y_876_ = v___x_924_;
goto v___jp_875_;
}
v___jp_875_:
{
if (lean_obj_tag(v_pendingConsumer_868_) == 1)
{
lean_dec(v_interestWaiter_869_);
lean_dec(v_pendingProducer_867_);
lean_dec_ref(v___f_852_);
lean_dec(v_inst_851_);
if (lean_obj_tag(v___y_876_) == 0)
{
lean_object* v_val_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_893_; 
v_val_877_ = lean_ctor_get(v_pendingConsumer_868_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_pendingConsumer_868_);
if (v_isSharedCheck_893_ == 0)
{
v___x_879_ = v_pendingConsumer_868_;
v_isShared_880_ = v_isSharedCheck_893_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_val_877_);
lean_dec(v_pendingConsumer_868_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_893_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___f_881_; 
lean_inc(v_a_853_);
v___f_881_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__6___boxed), 5, 4);
lean_closure_set(v___f_881_, 0, v___f_874_);
lean_closure_set(v___f_881_, 1, v___y_876_);
lean_closure_set(v___f_881_, 2, v_knownSize_870_);
lean_closure_set(v___f_881_, 3, v_a_853_);
if (lean_obj_tag(v_ending_850_) == 0)
{
lean_object* v___x_883_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___y_876_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___y_876_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
v___y_856_ = v_val_877_;
v___y_857_ = v___f_881_;
v___y_858_ = v___x_883_;
goto v___jp_855_;
}
}
else
{
lean_object* v_err_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_del_object(v___x_879_);
v_err_885_ = lean_ctor_get(v_ending_850_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_ending_850_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v_ending_850_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_err_885_);
lean_dec(v_ending_850_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 0);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_err_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
v___y_856_ = v_val_877_;
v___y_857_ = v___f_881_;
v___y_858_ = v___x_890_;
goto v___jp_855_;
}
}
}
}
}
else
{
lean_object* v_val_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_906_; 
lean_dec(v_ending_850_);
lean_dec_ref(v_toApplicative_847_);
v_val_894_ = lean_ctor_get(v_pendingConsumer_868_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_pendingConsumer_868_);
if (v_isSharedCheck_906_ == 0)
{
v___x_896_ = v_pendingConsumer_868_;
v_isShared_897_ = v_isSharedCheck_906_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_val_894_);
lean_dec(v_pendingConsumer_868_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_906_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_val_898_; lean_object* v___f_899_; lean_object* v___x_901_; 
v_val_898_ = lean_ctor_get(v___y_876_, 0);
lean_inc(v_val_898_);
lean_inc(v_a_853_);
lean_inc_ref(v___y_876_);
v___f_899_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__8___boxed), 6, 5);
lean_closure_set(v___f_899_, 0, v___f_874_);
lean_closure_set(v___f_899_, 1, v___y_876_);
lean_closure_set(v___f_899_, 2, v_knownSize_870_);
lean_closure_set(v___f_899_, 3, v_a_853_);
lean_closure_set(v___f_899_, 4, v_val_898_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___y_876_);
v___x_901_ = v___x_896_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___y_876_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed), 3, 2);
lean_closure_set(v___x_902_, 0, v_val_894_);
lean_closure_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_apply_2(v_inst_848_, lean_box(0), v___x_902_);
v___x_904_ = lean_apply_4(v_toBind_849_, lean_box(0), lean_box(0), v___x_903_, v___f_899_);
return v___x_904_;
}
}
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref(v___f_874_);
lean_dec(v_pendingConsumer_868_);
v___x_907_ = lean_box(0);
v___x_908_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__7(v_ending_850_, v___x_872_, v_inst_851_, v_toApplicative_847_, v_toBind_849_, v_inst_848_, v___f_852_, v_pendingProducer_867_, v_interestWaiter_869_, v___x_907_, v___y_876_, v_knownSize_870_, v_a_853_);
return v___x_908_;
}
}
}
else
{
lean_object* v_toPure_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec_ref(v_a_854_);
lean_dec_ref(v___f_852_);
lean_dec(v_inst_851_);
lean_dec(v_ending_850_);
lean_dec(v_toBind_849_);
lean_dec(v_inst_848_);
v_toPure_925_ = lean_ctor_get(v_toApplicative_847_, 1);
lean_inc(v_toPure_925_);
lean_dec_ref(v_toApplicative_847_);
v___x_926_ = lean_box(0);
v___x_927_ = lean_apply_2(v_toPure_925_, lean_box(0), v___x_926_);
return v___x_927_;
}
v___jp_855_:
{
lean_object* v_toFunctor_859_; lean_object* v_mapConst_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_toFunctor_859_ = lean_ctor_get(v_toApplicative_847_, 0);
lean_inc_ref(v_toFunctor_859_);
lean_dec_ref(v_toApplicative_847_);
v_mapConst_860_ = lean_ctor_get(v_toFunctor_859_, 1);
lean_inc(v_mapConst_860_);
lean_dec_ref(v_toFunctor_859_);
v___x_861_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed), 3, 2);
lean_closure_set(v___x_861_, 0, v___y_856_);
lean_closure_set(v___x_861_, 1, v___y_858_);
v___x_862_ = lean_apply_2(v_inst_848_, lean_box(0), v___x_861_);
v___x_863_ = lean_box(0);
v___x_864_ = lean_apply_4(v_mapConst_860_, lean_box(0), lean_box(0), v___x_863_, v___x_862_);
v___x_865_ = lean_apply_4(v_toBind_849_, lean_box(0), lean_box(0), v___x_864_, v___y_857_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9___boxed(lean_object* v_toApplicative_928_, lean_object* v_inst_929_, lean_object* v_toBind_930_, lean_object* v_ending_931_, lean_object* v_inst_932_, lean_object* v___f_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9(v_toApplicative_928_, v_inst_929_, v_toBind_930_, v_ending_931_, v_inst_932_, v___f_933_, v_a_934_, v_a_935_);
lean_dec(v_a_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_ending_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_toApplicative_943_; lean_object* v_toBind_944_; lean_object* v___f_945_; lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_toApplicative_943_ = lean_ctor_get(v_inst_938_, 0);
lean_inc_ref(v_toApplicative_943_);
v_toBind_944_ = lean_ctor_get(v_inst_938_, 1);
lean_inc_n(v_toBind_944_, 2);
lean_dec_ref(v_inst_938_);
v___f_945_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___closed__0));
lean_inc_n(v_a_942_, 2);
lean_inc(v_inst_939_);
v___f_946_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__9___boxed), 8, 7);
lean_closure_set(v___f_946_, 0, v_toApplicative_943_);
lean_closure_set(v___f_946_, 1, v_inst_940_);
lean_closure_set(v___f_946_, 2, v_toBind_944_);
lean_closure_set(v___f_946_, 3, v_ending_941_);
lean_closure_set(v___f_946_, 4, v_inst_939_);
lean_closure_set(v___f_946_, 5, v___f_945_);
lean_closure_set(v___f_946_, 6, v_a_942_);
v___x_947_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_947_, 0, lean_box(0));
lean_closure_set(v___x_947_, 1, lean_box(0));
lean_closure_set(v___x_947_, 2, v_a_942_);
v___x_948_ = lean_apply_2(v_inst_939_, lean_box(0), v___x_947_);
v___x_949_ = lean_apply_4(v_toBind_944_, lean_box(0), lean_box(0), v___x_948_, v___f_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_ending_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_950_, v_inst_951_, v_inst_952_, v_ending_953_, v_a_954_);
lean_dec(v_a_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(lean_object* v_m_956_, lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_ending_960_, lean_object* v_a_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_957_, v_inst_958_, v_inst_959_, v_ending_960_, v_a_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(lean_object* v_m_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_ending_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(v_m_963_, v_inst_964_, v_inst_965_, v_inst_966_, v_ending_967_, v_a_968_);
lean_dec(v_a_968_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_970_, lean_object* v_chunk_971_, lean_object* v_____r_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_toPure_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_toPure_974_ = lean_ctor_get(v_toApplicative_970_, 1);
lean_inc(v_toPure_974_);
lean_dec_ref(v_toApplicative_970_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v_chunk_971_);
v___x_976_ = lean_apply_2(v_toPure_974_, lean_box(0), v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_977_, lean_object* v_chunk_978_, lean_object* v_____r_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(v_toApplicative_977_, v_chunk_978_, v_____r_979_, v___y_980_);
lean_dec(v___y_980_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(lean_object* v___f_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_985_; 
lean_inc(v_a_983_);
v___x_985_ = lean_apply_2(v___f_982_, v_a_984_, v_a_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1___boxed(lean_object* v___f_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(v___f_986_, v_a_987_, v_a_988_);
lean_dec(v_a_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(uint8_t v_closeAfterProducer_990_, lean_object* v___f_991_, lean_object* v_a_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_toBind_996_, lean_object* v___f_997_, lean_object* v_a_998_){
_start:
{
if (v_closeAfterProducer_990_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v___f_997_);
lean_dec(v_toBind_996_);
lean_dec(v_inst_995_);
lean_dec(v_inst_994_);
lean_dec_ref(v_inst_993_);
v___x_999_ = lean_box(0);
lean_inc(v_a_992_);
v___x_1000_ = lean_apply_2(v___f_991_, v___x_999_, v_a_992_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v___f_991_);
v___x_1001_ = lean_box(0);
v___x_1002_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(v_inst_993_, v_inst_994_, v_inst_995_, v___x_1001_, v_a_992_);
v___x_1003_ = lean_apply_4(v_toBind_996_, lean_box(0), lean_box(0), v___x_1002_, v___f_997_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_closeAfterProducer_1004_, lean_object* v___f_1005_, lean_object* v_a_1006_, lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_toBind_1010_, lean_object* v___f_1011_, lean_object* v_a_1012_){
_start:
{
uint8_t v_closeAfterProducer_boxed_1013_; lean_object* v_res_1014_; 
v_closeAfterProducer_boxed_1013_ = lean_unbox(v_closeAfterProducer_1004_);
v_res_1014_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(v_closeAfterProducer_boxed_1013_, v___f_1005_, v_a_1006_, v_inst_1007_, v_inst_1008_, v_inst_1009_, v_toBind_1010_, v___f_1011_, v_a_1012_);
lean_dec(v_a_1006_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_1015_, lean_object* v_done_1016_, lean_object* v_inst_1017_, lean_object* v_toBind_1018_, lean_object* v___f_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_toFunctor_1021_; lean_object* v_mapConst_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_toFunctor_1021_ = lean_ctor_get(v_toApplicative_1015_, 0);
lean_inc_ref(v_toFunctor_1021_);
lean_dec_ref(v_toApplicative_1015_);
v_mapConst_1022_ = lean_ctor_get(v_toFunctor_1021_, 1);
lean_inc(v_mapConst_1022_);
lean_dec_ref(v_toFunctor_1021_);
v___x_1023_ = 1;
v___x_1024_ = lean_box(v___x_1023_);
v___x_1025_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1025_, 0, lean_box(0));
lean_closure_set(v___x_1025_, 1, v___x_1024_);
lean_closure_set(v___x_1025_, 2, v_done_1016_);
v___x_1026_ = lean_apply_2(v_inst_1017_, lean_box(0), v___x_1025_);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_apply_4(v_mapConst_1022_, lean_box(0), lean_box(0), v___x_1027_, v___x_1026_);
v___x_1029_ = lean_apply_4(v_toBind_1018_, lean_box(0), lean_box(0), v___x_1028_, v___f_1019_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_1030_, lean_object* v_a_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_toBind_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_pendingProducer_1037_; 
v_pendingProducer_1037_ = lean_ctor_get(v_a_1036_, 0);
if (lean_obj_tag(v_pendingProducer_1037_) == 1)
{
lean_object* v_val_1038_; lean_object* v_pendingConsumer_1039_; lean_object* v_interestWaiter_1040_; lean_object* v_ended_1041_; lean_object* v_knownSize_1042_; lean_object* v_pendingIncomplete_1043_; uint8_t v_closeAfterProducer_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1064_; 
v_val_1038_ = lean_ctor_get(v_pendingProducer_1037_, 0);
lean_inc(v_val_1038_);
v_pendingConsumer_1039_ = lean_ctor_get(v_a_1036_, 1);
v_interestWaiter_1040_ = lean_ctor_get(v_a_1036_, 2);
v_ended_1041_ = lean_ctor_get(v_a_1036_, 3);
v_knownSize_1042_ = lean_ctor_get(v_a_1036_, 4);
v_pendingIncomplete_1043_ = lean_ctor_get(v_a_1036_, 5);
v_closeAfterProducer_1044_ = lean_ctor_get_uint8(v_a_1036_, sizeof(void*)*6);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_a_1036_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_a_1036_, 0);
lean_dec(v_unused_1065_);
v___x_1046_ = v_a_1036_;
v_isShared_1047_ = v_isSharedCheck_1064_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_pendingIncomplete_1043_);
lean_inc(v_knownSize_1042_);
lean_inc(v_ended_1041_);
lean_inc(v_interestWaiter_1040_);
lean_inc(v_pendingConsumer_1039_);
lean_dec(v_a_1036_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1064_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v_chunk_1048_; lean_object* v_done_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; lean_object* v___x_1059_; 
v_chunk_1048_ = lean_ctor_get(v_val_1038_, 0);
lean_inc_ref_n(v_chunk_1048_, 2);
v_done_1049_ = lean_ctor_get(v_val_1038_, 1);
lean_inc(v_done_1049_);
lean_dec(v_val_1038_);
v___x_1050_ = lean_box(0);
lean_inc_ref(v_toApplicative_1030_);
v___f_1051_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1051_, 0, v_toApplicative_1030_);
lean_closure_set(v___f_1051_, 1, v_chunk_1048_);
lean_inc_n(v_a_1031_, 2);
lean_inc_ref(v___f_1051_);
v___f_1052_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1052_, 0, v___f_1051_);
lean_closure_set(v___f_1052_, 1, v_a_1031_);
v___x_1053_ = lean_box(v_closeAfterProducer_1044_);
lean_inc_n(v_toBind_1035_, 2);
lean_inc(v_inst_1034_);
lean_inc(v_inst_1033_);
v___f_1054_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_1054_, 0, v___x_1053_);
lean_closure_set(v___f_1054_, 1, v___f_1051_);
lean_closure_set(v___f_1054_, 2, v_a_1031_);
lean_closure_set(v___f_1054_, 3, v_inst_1032_);
lean_closure_set(v___f_1054_, 4, v_inst_1033_);
lean_closure_set(v___f_1054_, 5, v_inst_1034_);
lean_closure_set(v___f_1054_, 6, v_toBind_1035_);
lean_closure_set(v___f_1054_, 7, v___f_1052_);
v___f_1055_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1055_, 0, v_toApplicative_1030_);
lean_closure_set(v___f_1055_, 1, v_done_1049_);
lean_closure_set(v___f_1055_, 2, v_inst_1034_);
lean_closure_set(v___f_1055_, 3, v_toBind_1035_);
lean_closure_set(v___f_1055_, 4, v___f_1054_);
v___x_1056_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1042_, v_chunk_1048_);
lean_dec_ref(v_chunk_1048_);
v___x_1057_ = 0;
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 4, v___x_1056_);
lean_ctor_set(v___x_1046_, 0, v___x_1050_);
v___x_1059_ = v___x_1046_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_pendingConsumer_1039_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_interestWaiter_1040_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_ended_1041_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1063_, 5, v_pendingIncomplete_1043_);
v___x_1059_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*6, v___x_1057_);
lean_inc(v_a_1031_);
v___x_1060_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1060_, 0, lean_box(0));
lean_closure_set(v___x_1060_, 1, lean_box(0));
lean_closure_set(v___x_1060_, 2, v_a_1031_);
lean_closure_set(v___x_1060_, 3, v___x_1059_);
v___x_1061_ = lean_apply_2(v_inst_1033_, lean_box(0), v___x_1060_);
v___x_1062_ = lean_apply_4(v_toBind_1035_, lean_box(0), lean_box(0), v___x_1061_, v___f_1055_);
return v___x_1062_;
}
}
}
else
{
lean_object* v_toPure_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref(v_a_1036_);
lean_dec(v_toBind_1035_);
lean_dec(v_inst_1034_);
lean_dec(v_inst_1033_);
lean_dec_ref(v_inst_1032_);
v_toPure_1066_ = lean_ctor_get(v_toApplicative_1030_, 1);
lean_inc(v_toPure_1066_);
lean_dec_ref(v_toApplicative_1030_);
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_apply_2(v_toPure_1066_, lean_box(0), v___x_1067_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_1069_, lean_object* v_a_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_toBind_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4(v_toApplicative_1069_, v_a_1070_, v_inst_1071_, v_inst_1072_, v_inst_1073_, v_toBind_1074_, v_a_1075_);
lean_dec(v_a_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_toApplicative_1081_; lean_object* v_toBind_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_toApplicative_1081_ = lean_ctor_get(v_inst_1077_, 0);
lean_inc_ref(v_toApplicative_1081_);
v_toBind_1082_ = lean_ctor_get(v_inst_1077_, 1);
lean_inc_n(v_toBind_1082_, 2);
lean_inc(v_inst_1078_);
lean_inc_n(v_a_1080_, 2);
v___f_1083_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_1083_, 0, v_toApplicative_1081_);
lean_closure_set(v___f_1083_, 1, v_a_1080_);
lean_closure_set(v___f_1083_, 2, v_inst_1077_);
lean_closure_set(v___f_1083_, 3, v_inst_1078_);
lean_closure_set(v___f_1083_, 4, v_inst_1079_);
lean_closure_set(v___f_1083_, 5, v_toBind_1082_);
v___x_1084_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1084_, 0, lean_box(0));
lean_closure_set(v___x_1084_, 1, lean_box(0));
lean_closure_set(v___x_1084_, 2, v_a_1080_);
v___x_1085_ = lean_apply_2(v_inst_1078_, lean_box(0), v___x_1084_);
v___x_1086_ = lean_apply_4(v_toBind_1082_, lean_box(0), lean_box(0), v___x_1085_, v___f_1083_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_1087_, v_inst_1088_, v_inst_1089_, v_a_1090_);
lean_dec(v_a_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(lean_object* v_m_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_1093_, v_inst_1094_, v_inst_1095_, v_a_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(v_m_1098_, v_inst_1099_, v_inst_1100_, v_inst_1101_, v_a_1102_);
lean_dec(v_a_1102_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0(lean_object* v_toApplicative_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_ended_1112_; 
v_ended_1112_ = lean_ctor_get(v_a_1107_, 3);
lean_inc(v_ended_1112_);
lean_dec_ref(v_a_1107_);
if (lean_obj_tag(v_ended_1112_) == 1)
{
lean_object* v_val_1113_; 
v_val_1113_ = lean_ctor_get(v_ended_1112_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v_ended_1112_, 1);
if (lean_obj_tag(v_val_1113_) == 1)
{
lean_object* v_err_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1123_; 
v_err_1114_ = lean_ctor_get(v_val_1113_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_val_1113_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1116_ = v_val_1113_;
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_err_1114_);
lean_dec(v_val_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_toPure_1118_; lean_object* v___x_1120_; 
v_toPure_1118_ = lean_ctor_get(v_toApplicative_1106_, 1);
lean_inc(v_toPure_1118_);
lean_dec_ref(v_toApplicative_1106_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 0);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_err_1114_);
v___x_1120_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_apply_2(v_toPure_1118_, lean_box(0), v___x_1120_);
return v___x_1121_;
}
}
}
else
{
lean_dec(v_val_1113_);
goto v___jp_1108_;
}
}
else
{
lean_dec(v_ended_1112_);
goto v___jp_1108_;
}
v___jp_1108_:
{
lean_object* v_toPure_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_toPure_1109_ = lean_ctor_get(v_toApplicative_1106_, 1);
lean_inc(v_toPure_1109_);
lean_dec_ref(v_toApplicative_1106_);
v___x_1110_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_1111_ = lean_apply_2(v_toPure_1109_, lean_box(0), v___x_1110_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(lean_object* v_toApplicative_1124_, lean_object* v_a_1125_, lean_object* v_inst_1126_, lean_object* v_toBind_1127_, lean_object* v___f_1128_, lean_object* v_a_1129_){
_start:
{
if (lean_obj_tag(v_a_1129_) == 1)
{
lean_object* v_toPure_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec(v___f_1128_);
lean_dec(v_toBind_1127_);
lean_dec(v_inst_1126_);
v_toPure_1130_ = lean_ctor_get(v_toApplicative_1124_, 1);
lean_inc(v_toPure_1130_);
lean_dec_ref(v_toApplicative_1124_);
v___x_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_a_1129_);
v___x_1132_ = lean_apply_2(v_toPure_1130_, lean_box(0), v___x_1131_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v_a_1129_);
lean_dec_ref(v_toApplicative_1124_);
lean_inc(v_a_1125_);
v___x_1133_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1133_, 0, lean_box(0));
lean_closure_set(v___x_1133_, 1, lean_box(0));
lean_closure_set(v___x_1133_, 2, v_a_1125_);
v___x_1134_ = lean_apply_2(v_inst_1126_, lean_box(0), v___x_1133_);
v___x_1135_ = lean_apply_4(v_toBind_1127_, lean_box(0), lean_box(0), v___x_1134_, v___f_1128_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_1136_, lean_object* v_a_1137_, lean_object* v_inst_1138_, lean_object* v_toBind_1139_, lean_object* v___f_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1(v_toApplicative_1136_, v_a_1137_, v_inst_1138_, v_toBind_1139_, v___f_1140_, v_a_1141_);
lean_dec(v_a_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_toApplicative_1147_; lean_object* v_toBind_1148_; lean_object* v___f_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_toApplicative_1147_ = lean_ctor_get(v_inst_1143_, 0);
v_toBind_1148_ = lean_ctor_get(v_inst_1143_, 1);
lean_inc_n(v_toBind_1148_, 2);
lean_inc_ref_n(v_toApplicative_1147_, 2);
v___f_1149_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1149_, 0, v_toApplicative_1147_);
lean_inc(v_inst_1144_);
lean_inc(v_a_1146_);
v___f_1150_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1150_, 0, v_toApplicative_1147_);
lean_closure_set(v___f_1150_, 1, v_a_1146_);
lean_closure_set(v___f_1150_, 2, v_inst_1144_);
lean_closure_set(v___f_1150_, 3, v_toBind_1148_);
lean_closure_set(v___f_1150_, 4, v___f_1149_);
v___x_1151_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(v_inst_1143_, v_inst_1144_, v_inst_1145_, v_a_1146_);
v___x_1152_ = lean_apply_4(v_toBind_1148_, lean_box(0), lean_box(0), v___x_1151_, v___f_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___boxed(lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_1153_, v_inst_1154_, v_inst_1155_, v_a_1156_);
lean_dec(v_a_1156_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(lean_object* v_m_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg(v_inst_1159_, v_inst_1160_, v_inst_1161_, v_a_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___boxed(lean_object* v_m_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27(v_m_1164_, v_inst_1165_, v_inst_1166_, v_inst_1167_, v_a_1168_);
lean_dec(v_a_1168_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(lean_object* v_pendingProducer_1174_, lean_object* v_pendingConsumer_1175_, lean_object* v_ended_1176_, lean_object* v_knownSize_1177_, lean_object* v_pendingIncomplete_1178_, uint8_t v_closeAfterProducer_1179_, lean_object* v_interestWaiter_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1183_, 0, v_pendingProducer_1174_);
lean_ctor_set(v___x_1183_, 1, v_pendingConsumer_1175_);
lean_ctor_set(v___x_1183_, 2, v_interestWaiter_1180_);
lean_ctor_set(v___x_1183_, 3, v_ended_1176_);
lean_ctor_set(v___x_1183_, 4, v_knownSize_1177_);
lean_ctor_set(v___x_1183_, 5, v_pendingIncomplete_1178_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*6, v_closeAfterProducer_1179_);
v___x_1184_ = lean_st_ref_swap(v___y_1181_, v___x_1183_);
lean_dec(v___x_1184_);
v___x_1185_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(lean_object* v_pendingProducer_1186_, lean_object* v_pendingConsumer_1187_, lean_object* v_ended_1188_, lean_object* v_knownSize_1189_, lean_object* v_pendingIncomplete_1190_, lean_object* v_closeAfterProducer_1191_, lean_object* v_interestWaiter_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v_closeAfterProducer_boxed_1195_; lean_object* v_res_1196_; 
v_closeAfterProducer_boxed_1195_ = lean_unbox(v_closeAfterProducer_1191_);
v_res_1196_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_1186_, v_pendingConsumer_1187_, v_ended_1188_, v_knownSize_1189_, v_pendingIncomplete_1190_, v_closeAfterProducer_boxed_1195_, v_interestWaiter_1192_, v___y_1193_);
lean_dec(v___y_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(lean_object* v___f_1197_, lean_object* v___y_1198_, lean_object* v_x_1199_){
_start:
{
if (lean_obj_tag(v_x_1199_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v___f_1197_);
v_a_1201_ = lean_ctor_get(v_x_1199_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1203_ = v_x_1199_;
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v_x_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1211_; 
v_a_1210_ = lean_ctor_get(v_x_1199_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v_x_1199_, 1);
lean_inc(v___y_1198_);
v___x_1211_ = lean_apply_3(v___f_1197_, v_a_1210_, v___y_1198_, lean_box(0));
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(lean_object* v___f_1212_, lean_object* v___y_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_1212_, v___y_1213_, v_x_1214_);
lean_dec(v___y_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(lean_object* v_interestWaiter_1221_, lean_object* v___f_1222_, lean_object* v___f_1223_, lean_object* v_x_1224_){
_start:
{
if (lean_obj_tag(v_x_1224_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v___f_1223_);
lean_dec_ref(v___f_1222_);
lean_dec(v_interestWaiter_1221_);
v_a_1226_ = lean_ctor_get(v_x_1224_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_x_1224_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1228_ = v_x_1224_;
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v_x_1224_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1251_; 
v_a_1235_ = lean_ctor_get(v_x_1224_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_x_1224_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1237_ = v_x_1224_;
v_isShared_1238_ = v_isSharedCheck_1251_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v_x_1224_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1251_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_unbox(v_a_1235_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_dec_ref(v___f_1223_);
v___x_1240_ = lean_unsigned_to_nat(0u);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v_interestWaiter_1221_);
v___x_1242_ = v___x_1237_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_interestWaiter_1221_);
v___x_1242_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
v___x_1244_ = lean_unbox(v_a_1235_);
lean_dec(v_a_1235_);
v___x_1245_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1240_, v___x_1244_, v___x_1243_, v___f_1222_);
return v___x_1245_;
}
}
else
{
lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_del_object(v___x_1237_);
lean_dec(v_a_1235_);
lean_dec_ref(v___f_1222_);
lean_dec(v_interestWaiter_1221_);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = 0;
v___x_1249_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1));
v___x_1250_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1247_, v___x_1248_, v___x_1249_, v___f_1223_);
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(lean_object* v_interestWaiter_1252_, lean_object* v___f_1253_, lean_object* v___f_1254_, lean_object* v_x_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_1252_, v___f_1253_, v___f_1254_, v_x_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(lean_object* v_pendingProducer_1258_, lean_object* v_ended_1259_, lean_object* v_knownSize_1260_, lean_object* v_pendingIncomplete_1261_, uint8_t v_closeAfterProducer_1262_, lean_object* v_interestWaiter_1263_, lean_object* v_pendingConsumer_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; lean_object* v___f_1268_; 
v___x_1267_ = lean_box(v_closeAfterProducer_1262_);
v___f_1268_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1268_, 0, v_pendingProducer_1258_);
lean_closure_set(v___f_1268_, 1, v_pendingConsumer_1264_);
lean_closure_set(v___f_1268_, 2, v_ended_1259_);
lean_closure_set(v___f_1268_, 3, v_knownSize_1260_);
lean_closure_set(v___f_1268_, 4, v_pendingIncomplete_1261_);
lean_closure_set(v___f_1268_, 5, v___x_1267_);
if (lean_obj_tag(v_interestWaiter_1263_) == 0)
{
lean_object* v___f_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_inc(v___y_1265_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1269_, 0, v___f_1268_);
lean_closure_set(v___f_1269_, 1, v___y_1265_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = 0;
v___x_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1272_, 0, v_interestWaiter_1263_);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
v___x_1274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1270_, v___x_1271_, v___x_1273_, v___f_1269_);
return v___x_1274_;
}
else
{
lean_object* v_val_1275_; lean_object* v_finished_1276_; lean_object* v___f_1277_; lean_object* v___f_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_val_1275_ = lean_ctor_get(v_interestWaiter_1263_, 0);
v_finished_1276_ = lean_ctor_get(v_val_1275_, 0);
lean_inc(v_finished_1276_);
lean_inc(v___y_1265_);
v___f_1277_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1277_, 0, v___f_1268_);
lean_closure_set(v___f_1277_, 1, v___y_1265_);
lean_inc_ref(v___f_1277_);
v___f_1278_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1278_, 0, v_interestWaiter_1263_);
lean_closure_set(v___f_1278_, 1, v___f_1277_);
lean_closure_set(v___f_1278_, 2, v___f_1277_);
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = 0;
v___x_1281_ = lean_st_ref_get(v_finished_1276_);
lean_dec(v_finished_1276_);
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
v___x_1284_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1279_, v___x_1280_, v___x_1283_, v___f_1278_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(lean_object* v_pendingProducer_1285_, lean_object* v_ended_1286_, lean_object* v_knownSize_1287_, lean_object* v_pendingIncomplete_1288_, lean_object* v_closeAfterProducer_1289_, lean_object* v_interestWaiter_1290_, lean_object* v_pendingConsumer_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v_closeAfterProducer_boxed_1294_; lean_object* v_res_1295_; 
v_closeAfterProducer_boxed_1294_ = lean_unbox(v_closeAfterProducer_1289_);
v_res_1295_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_1285_, v_ended_1286_, v_knownSize_1287_, v_pendingIncomplete_1288_, v_closeAfterProducer_boxed_1294_, v_interestWaiter_1290_, v_pendingConsumer_1291_, v___y_1292_);
lean_dec(v___y_1292_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(lean_object* v___f_1296_, lean_object* v___y_1297_, lean_object* v_x_1298_){
_start:
{
if (lean_obj_tag(v_x_1298_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref(v___f_1296_);
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
lean_object* v_a_1309_; lean_object* v___x_1310_; 
v_a_1309_ = lean_ctor_get(v_x_1298_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v_x_1298_, 1);
lean_inc(v___y_1297_);
v___x_1310_ = lean_apply_3(v___f_1296_, v_a_1309_, v___y_1297_, lean_box(0));
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(lean_object* v___f_1311_, lean_object* v___y_1312_, lean_object* v_x_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_1311_, v___y_1312_, v_x_1313_);
lean_dec(v___y_1312_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(lean_object* v___f_1316_, lean_object* v_a_1317_, lean_object* v_x_1318_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v___f_1316_);
v_a_1320_ = lean_ctor_get(v_x_1318_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_x_1318_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1322_ = v_x_1318_;
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v_x_1318_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1320_);
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
lean_object* v_a_1329_; lean_object* v___x_1330_; 
v_a_1329_ = lean_ctor_get(v_x_1318_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v_x_1318_, 1);
lean_inc(v_a_1317_);
v___x_1330_ = lean_apply_3(v___f_1316_, v_a_1329_, v_a_1317_, lean_box(0));
return v___x_1330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(lean_object* v___f_1331_, lean_object* v_a_1332_, lean_object* v_x_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_1331_, v_a_1332_, v_x_1333_);
lean_dec(v_a_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(lean_object* v_pendingConsumer_1340_, lean_object* v___f_1341_, lean_object* v___f_1342_, lean_object* v_x_1343_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v___f_1342_);
lean_dec_ref(v___f_1341_);
lean_dec(v_pendingConsumer_1340_);
v_a_1345_ = lean_ctor_get(v_x_1343_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_x_1343_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1347_ = v_x_1343_;
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v_x_1343_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1370_; 
v_a_1354_ = lean_ctor_get(v_x_1343_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_x_1343_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1356_ = v_x_1343_;
v_isShared_1357_ = v_isSharedCheck_1370_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v_x_1343_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1370_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_unbox(v_a_1354_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
lean_dec_ref(v___f_1342_);
v___x_1359_ = lean_unsigned_to_nat(0u);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_pendingConsumer_1340_);
v___x_1361_ = v___x_1356_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_pendingConsumer_1340_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
v___x_1363_ = lean_unbox(v_a_1354_);
lean_dec(v_a_1354_);
v___x_1364_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1359_, v___x_1363_, v___x_1362_, v___f_1341_);
return v___x_1364_;
}
}
else
{
lean_object* v___x_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_del_object(v___x_1356_);
lean_dec(v_a_1354_);
lean_dec_ref(v___f_1341_);
lean_dec(v_pendingConsumer_1340_);
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = 0;
v___x_1368_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1));
v___x_1369_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1366_, v___x_1367_, v___x_1368_, v___f_1342_);
return v___x_1369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(lean_object* v_pendingConsumer_1371_, lean_object* v___f_1372_, lean_object* v___f_1373_, lean_object* v_x_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_1371_, v___f_1372_, v___f_1373_, v_x_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(lean_object* v_a_1377_, lean_object* v_x_1378_){
_start:
{
if (lean_obj_tag(v_x_1378_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1388_; 
v_a_1380_ = lean_ctor_get(v_x_1378_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_x_1378_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1382_ = v_x_1378_;
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v_x_1378_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1380_);
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
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1429_; 
v_a_1389_ = lean_ctor_get(v_x_1378_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_x_1378_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1391_ = v_x_1378_;
v_isShared_1392_ = v_isSharedCheck_1429_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v_x_1378_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1429_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_pendingProducer_1393_; lean_object* v_pendingConsumer_1394_; lean_object* v_interestWaiter_1395_; lean_object* v_ended_1396_; lean_object* v_knownSize_1397_; lean_object* v_pendingIncomplete_1398_; uint8_t v_closeAfterProducer_1399_; lean_object* v___x_1400_; lean_object* v___f_1401_; lean_object* v___y_1403_; 
v_pendingProducer_1393_ = lean_ctor_get(v_a_1389_, 0);
lean_inc(v_pendingProducer_1393_);
v_pendingConsumer_1394_ = lean_ctor_get(v_a_1389_, 1);
lean_inc(v_pendingConsumer_1394_);
v_interestWaiter_1395_ = lean_ctor_get(v_a_1389_, 2);
lean_inc(v_interestWaiter_1395_);
v_ended_1396_ = lean_ctor_get(v_a_1389_, 3);
lean_inc(v_ended_1396_);
v_knownSize_1397_ = lean_ctor_get(v_a_1389_, 4);
lean_inc(v_knownSize_1397_);
v_pendingIncomplete_1398_ = lean_ctor_get(v_a_1389_, 5);
lean_inc(v_pendingIncomplete_1398_);
v_closeAfterProducer_1399_ = lean_ctor_get_uint8(v_a_1389_, sizeof(void*)*6);
lean_dec(v_a_1389_);
v___x_1400_ = lean_box(v_closeAfterProducer_1399_);
v___f_1401_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed), 9, 6);
lean_closure_set(v___f_1401_, 0, v_pendingProducer_1393_);
lean_closure_set(v___f_1401_, 1, v_ended_1396_);
lean_closure_set(v___f_1401_, 2, v_knownSize_1397_);
lean_closure_set(v___f_1401_, 3, v_pendingIncomplete_1398_);
lean_closure_set(v___f_1401_, 4, v___x_1400_);
lean_closure_set(v___f_1401_, 5, v_interestWaiter_1395_);
if (lean_obj_tag(v_pendingConsumer_1394_) == 1)
{
lean_object* v_val_1412_; 
v_val_1412_ = lean_ctor_get(v_pendingConsumer_1394_, 0);
lean_inc(v_val_1412_);
if (lean_obj_tag(v_val_1412_) == 1)
{
lean_object* v_finished_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1428_; 
lean_del_object(v___x_1391_);
v_finished_1413_ = lean_ctor_get(v_val_1412_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_val_1412_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1415_ = v_val_1412_;
v_isShared_1416_ = v_isSharedCheck_1428_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_finished_1413_);
lean_dec(v_val_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1428_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_finished_1417_; lean_object* v___f_1418_; lean_object* v___f_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v_finished_1417_ = lean_ctor_get(v_finished_1413_, 0);
lean_inc(v_finished_1417_);
lean_dec_ref(v_finished_1413_);
lean_inc(v_a_1377_);
v___f_1418_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1418_, 0, v___f_1401_);
lean_closure_set(v___f_1418_, 1, v_a_1377_);
lean_inc_ref(v___f_1418_);
v___f_1419_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1419_, 0, v_pendingConsumer_1394_);
lean_closure_set(v___f_1419_, 1, v___f_1418_);
lean_closure_set(v___f_1419_, 2, v___f_1418_);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = 0;
v___x_1422_ = lean_st_ref_get(v_finished_1417_);
lean_dec(v_finished_1417_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1422_);
v___x_1424_ = v___x_1415_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
v___x_1426_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1420_, v___x_1421_, v___x_1425_, v___f_1419_);
return v___x_1426_;
}
}
}
else
{
lean_dec(v_val_1412_);
v___y_1403_ = v_a_1377_;
goto v___jp_1402_;
}
}
else
{
v___y_1403_ = v_a_1377_;
goto v___jp_1402_;
}
v___jp_1402_:
{
lean_object* v___f_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1408_; 
lean_inc(v___y_1403_);
v___f_1404_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1404_, 0, v___f_1401_);
lean_closure_set(v___f_1404_, 1, v___y_1403_);
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = 0;
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v_pendingConsumer_1394_);
v___x_1408_ = v___x_1391_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_pendingConsumer_1394_);
v___x_1408_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
v___x_1410_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1405_, v___x_1406_, v___x_1409_, v___f_1404_);
return v___x_1410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(lean_object* v_a_1430_, lean_object* v_x_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_1430_, v_x_1431_);
lean_dec(v_a_1430_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(lean_object* v_a_1434_){
_start:
{
lean_object* v___f_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_inc(v_a_1434_);
v___f_1436_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1436_, 0, v_a_1434_);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = 0;
v___x_1439_ = lean_st_ref_get(v_a_1434_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
v___x_1442_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1437_, v___x_1438_, v___x_1441_, v___f_1436_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(lean_object* v_a_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_1443_);
lean_dec(v_a_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(lean_object* v___y_1446_){
_start:
{
if (lean_obj_tag(v___y_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_a_1447_ = lean_ctor_get(v___y_1446_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___y_1446_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___y_1446_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___y_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1463_; 
v_a_1455_ = lean_ctor_get(v___y_1446_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___y_1446_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1457_ = v___y_1446_;
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___y_1446_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_fst_1459_; lean_object* v___x_1461_; 
v_fst_1459_ = lean_ctor_get(v_a_1455_, 0);
lean_inc(v_fst_1459_);
lean_dec(v_a_1455_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v_fst_1459_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_fst_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(lean_object* v_mutex_1464_, lean_object* v_x_1465_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_io_basemutex_unlock(v_mutex_1464_);
v___x_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(v_mutex_1470_, v_x_1471_);
lean_dec(v_x_1471_);
lean_dec(v_mutex_1470_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(lean_object* v_k_1474_, lean_object* v_ref_1475_, lean_object* v_x_1476_){
_start:
{
if (lean_obj_tag(v_x_1476_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_ref_1475_);
lean_dec_ref(v_k_1474_);
v_a_1478_ = lean_ctor_get(v_x_1476_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_x_1476_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v_x_1476_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v_x_1476_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
}
else
{
lean_object* v___x_1487_; 
lean_dec_ref_known(v_x_1476_, 1);
v___x_1487_ = lean_apply_2(v_k_1474_, v_ref_1475_, lean_box(0));
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(lean_object* v_k_1488_, lean_object* v_ref_1489_, lean_object* v_x_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(v_k_1488_, v_ref_1489_, v_x_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(lean_object* v_mutex_1493_, lean_object* v___f_1494_){
_start:
{
lean_object* v___x_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = 0;
v___x_1498_ = lean_io_basemutex_lock(v_mutex_1493_);
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
v___x_1501_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1496_, v___x_1497_, v___x_1500_, v___f_1494_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_1502_, lean_object* v___f_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(v_mutex_1502_, v___f_1503_);
lean_dec(v_mutex_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(lean_object* v_mutex_1507_, lean_object* v_k_1508_){
_start:
{
lean_object* v_ref_1510_; lean_object* v_mutex_1511_; lean_object* v___f_1512_; lean_object* v___f_1513_; lean_object* v___f_1514_; lean_object* v___f_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___y_1520_; 
v_ref_1510_ = lean_ctor_get(v_mutex_1507_, 0);
lean_inc(v_ref_1510_);
v_mutex_1511_ = lean_ctor_get(v_mutex_1507_, 1);
lean_inc_n(v_mutex_1511_, 2);
lean_dec_ref(v_mutex_1507_);
v___f_1512_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0));
v___f_1513_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1513_, 0, v_mutex_1511_);
v___f_1514_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1514_, 0, v_k_1508_);
lean_closure_set(v___f_1514_, 1, v_ref_1510_);
v___f_1515_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1515_, 0, v_mutex_1511_);
lean_closure_set(v___f_1515_, 1, v___f_1514_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = 0;
v___x_1518_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1515_, v___f_1513_, v___x_1516_, v___x_1517_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1522_; 
v_a_1522_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1518_, 1);
if (lean_obj_tag(v_a_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
v_a_1523_ = lean_ctor_get(v_a_1522_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_a_1522_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v_a_1522_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v_a_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
v___y_1520_ = v___x_1528_;
goto v___jp_1519_;
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1539_; 
v_a_1531_ = lean_ctor_get(v_a_1522_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_a_1522_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1533_ = v_a_1522_;
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v_a_1522_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_fst_1535_; lean_object* v___x_1537_; 
v_fst_1535_ = lean_ctor_get(v_a_1531_, 0);
lean_inc(v_fst_1535_);
lean_dec(v_a_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v_fst_1535_);
v___x_1537_ = v___x_1533_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_fst_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
v___y_1520_ = v___x_1537_;
goto v___jp_1519_;
}
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1548_; 
v_a_1540_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1542_ = v___x_1518_;
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1518_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = lean_task_map(v___f_1512_, v_a_1540_, v___x_1516_, v___x_1517_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1544_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
v___jp_1519_:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___y_1520_);
return v___x_1521_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___boxed(lean_object* v_mutex_1549_, lean_object* v_k_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1549_, v_k_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(lean_object* v_00_u03b1_1553_, lean_object* v_00_u03b2_1554_, lean_object* v_mutex_1555_, lean_object* v_k_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_mutex_1555_, v_k_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed(lean_object* v_00_u03b1_1559_, lean_object* v_00_u03b2_1560_, lean_object* v_mutex_1561_, lean_object* v_k_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(v_00_u03b1_1559_, v_00_u03b2_1560_, v_mutex_1561_, v_k_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0(lean_object* v_x_1565_){
_start:
{
if (lean_obj_tag(v_x_1565_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1575_; 
v_a_1567_ = lean_ctor_get(v_x_1565_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_x_1565_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1569_ = v_x_1565_;
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v_x_1565_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
v_a_1576_ = lean_ctor_get(v_x_1565_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v_x_1565_, 1);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_a_1576_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(lean_object* v_x_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Std_Http_Body_Stream_tryRecv___lam__0(v_x_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(lean_object* v_a_1581_, lean_object* v___f_1582_, lean_object* v_x_1583_){
_start:
{
if (lean_obj_tag(v_x_1583_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v___f_1582_);
v_a_1585_ = lean_ctor_get(v_x_1583_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_x_1583_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1587_ = v_x_1583_;
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v_x_1583_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
}
else
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v_x_1583_, 0);
lean_inc(v_a_1594_);
if (lean_obj_tag(v_a_1594_) == 1)
{
lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v___f_1582_);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_a_1594_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v_a_1594_, 0);
lean_dec(v_unused_1603_);
v___x_1596_ = v_a_1594_;
v_isShared_1597_ = v_isSharedCheck_1602_;
goto v_resetjp_1595_;
}
else
{
lean_dec(v_a_1594_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1602_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_x_1583_);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_x_1583_);
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
else
{
lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1594_);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_x_1583_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v_x_1583_, 0);
lean_dec(v_unused_1616_);
v___x_1605_ = v_x_1583_;
v_isShared_1606_ = v_isSharedCheck_1615_;
goto v_resetjp_1604_;
}
else
{
lean_dec(v_x_1583_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1615_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = 0;
v___x_1609_ = lean_st_ref_get(v_a_1581_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1609_);
v___x_1611_ = v___x_1605_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
v___x_1613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1607_, v___x_1608_, v___x_1612_, v___f_1582_);
return v___x_1613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(lean_object* v_a_1617_, lean_object* v___f_1618_, lean_object* v_x_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_a_1617_, v___f_1618_, v_x_1619_);
lean_dec(v_a_1617_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(lean_object* v_x_1626_){
_start:
{
if (lean_obj_tag(v_x_1626_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1638_; 
v_a_1630_ = lean_ctor_get(v_x_1626_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_x_1626_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1632_ = v_x_1626_;
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v_x_1626_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1663_; 
v_a_1639_ = lean_ctor_get(v_x_1626_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_x_1626_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1641_ = v_x_1626_;
v_isShared_1642_ = v_isSharedCheck_1663_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v_x_1626_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1663_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v_ended_1643_; 
v_ended_1643_ = lean_ctor_get(v_a_1639_, 3);
lean_inc(v_ended_1643_);
lean_dec(v_a_1639_);
if (lean_obj_tag(v_ended_1643_) == 1)
{
lean_object* v_val_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1662_; 
v_val_1644_ = lean_ctor_get(v_ended_1643_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_ended_1643_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1646_ = v_ended_1643_;
v_isShared_1647_ = v_isSharedCheck_1662_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_val_1644_);
lean_dec(v_ended_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1662_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
if (lean_obj_tag(v_val_1644_) == 1)
{
lean_object* v_err_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1661_; 
v_err_1648_ = lean_ctor_get(v_val_1644_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_val_1644_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1650_ = v_val_1644_;
v_isShared_1651_ = v_isSharedCheck_1661_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_err_1648_);
lean_dec(v_val_1644_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1661_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 0);
lean_ctor_set(v___x_1641_, 0, v_err_1648_);
v___x_1653_ = v___x_1641_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_err_1648_);
v___x_1653_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1657_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1655_);
v___x_1657_ = v___x_1646_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
else
{
lean_del_object(v___x_1646_);
lean_dec(v_val_1644_);
lean_del_object(v___x_1641_);
goto v___jp_1628_;
}
}
}
else
{
lean_dec(v_ended_1643_);
lean_del_object(v___x_1641_);
goto v___jp_1628_;
}
}
}
v___jp_1628_:
{
lean_object* v___x_1629_; 
v___x_1629_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___closed__1));
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(lean_object* v_x_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_x_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(lean_object* v___f_1667_, lean_object* v_a_1668_, lean_object* v_x_1669_){
_start:
{
if (lean_obj_tag(v_x_1669_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1679_; 
lean_dec_ref(v___f_1667_);
v_a_1671_ = lean_ctor_get(v_x_1669_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_x_1669_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1673_ = v_x_1669_;
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v_x_1669_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1681_; 
v_a_1680_ = lean_ctor_get(v_x_1669_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v_x_1669_, 1);
lean_inc(v_a_1668_);
v___x_1681_ = lean_apply_3(v___f_1667_, v_a_1680_, v_a_1668_, lean_box(0));
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed(lean_object* v___f_1682_, lean_object* v_a_1683_, lean_object* v_x_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1(v___f_1682_, v_a_1683_, v_x_1684_);
lean_dec(v_a_1683_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__0(lean_object* v___y_1687_){
_start:
{
if (lean_obj_tag(v___y_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1688_ = lean_ctor_get(v___y_1687_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___y_1687_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___y_1687_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___y_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
v_a_1696_ = lean_ctor_get(v___y_1687_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___y_1687_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1698_ = v___y_1687_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___y_1687_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_a_1696_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8(lean_object* v___f_1705_, lean_object* v___y_1706_, lean_object* v_knownSize_1707_, lean_object* v_a_1708_, lean_object* v_val_1709_, lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_knownSize_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___f_1705_);
v_a_1712_ = lean_ctor_get(v_x_1710_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1710_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1714_ = v_x_1710_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v_x_1710_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
}
}
else
{
lean_object* v_a_1721_; uint8_t v___x_1722_; 
v_a_1721_ = lean_ctor_get(v_x_1710_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v_x_1710_, 1);
v___x_1722_ = lean_unbox(v_a_1721_);
lean_dec(v_a_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_box(0);
lean_inc(v_a_1708_);
v___x_1724_ = lean_apply_5(v___f_1705_, v___x_1723_, v___y_1706_, v_knownSize_1707_, v_a_1708_, lean_box(0));
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_dec(v___y_1706_);
v___x_1725_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_1707_, v_val_1709_);
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_box(0);
lean_inc(v_a_1708_);
v___x_1728_ = lean_apply_5(v___f_1705_, v___x_1727_, v___x_1726_, v___x_1725_, v_a_1708_, lean_box(0));
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8___boxed(lean_object* v___f_1729_, lean_object* v___y_1730_, lean_object* v_knownSize_1731_, lean_object* v_a_1732_, lean_object* v_val_1733_, lean_object* v_x_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8(v___f_1729_, v___y_1730_, v_knownSize_1731_, v_a_1732_, v_val_1733_, v_x_1734_);
lean_dec_ref(v_val_1733_);
lean_dec(v_a_1732_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6(lean_object* v___f_1737_, lean_object* v___y_1738_, lean_object* v_knownSize_1739_, lean_object* v_a_1740_, lean_object* v_x_1741_){
_start:
{
if (lean_obj_tag(v_x_1741_) == 0)
{
lean_object* v___x_1743_; 
lean_dec(v_knownSize_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___f_1737_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_x_1741_);
return v___x_1743_;
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1745_; 
v_a_1744_ = lean_ctor_get(v_x_1741_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v_x_1741_, 1);
lean_inc(v_a_1740_);
v___x_1745_ = lean_apply_5(v___f_1737_, v_a_1744_, v___y_1738_, v_knownSize_1739_, v_a_1740_, lean_box(0));
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6___boxed(lean_object* v___f_1746_, lean_object* v___y_1747_, lean_object* v_knownSize_1748_, lean_object* v_a_1749_, lean_object* v_x_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6(v___f_1746_, v___y_1747_, v_knownSize_1748_, v_a_1749_, v_x_1750_);
lean_dec(v_a_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4(lean_object* v___f_1753_, lean_object* v___y_1754_, lean_object* v_x_1755_){
_start:
{
if (lean_obj_tag(v_x_1755_) == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v___f_1753_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_x_1755_);
return v___x_1757_;
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1759_; 
v_a_1758_ = lean_ctor_get(v_x_1755_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v_x_1755_, 1);
lean_inc(v___y_1754_);
v___x_1759_ = lean_apply_3(v___f_1753_, v_a_1758_, v___y_1754_, lean_box(0));
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed(lean_object* v___f_1760_, lean_object* v___y_1761_, lean_object* v_x_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4(v___f_1760_, v___y_1761_, v_x_1762_);
lean_dec(v___y_1761_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1(lean_object* v_ending_1765_, lean_object* v_knownSize_1766_, uint8_t v___x_1767_, lean_object* v___y_1768_, lean_object* v_x_1769_){
_start:
{
if (lean_obj_tag(v_x_1769_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v_knownSize_1766_);
lean_dec(v_ending_1765_);
v_a_1771_ = lean_ctor_get(v_x_1769_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_x_1769_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1773_ = v_x_1769_;
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v_x_1769_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_a_1780_ = lean_ctor_get(v_x_1769_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v_x_1769_, 1);
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_ending_1765_);
v___x_1783_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1783_, 0, v_a_1780_);
lean_ctor_set(v___x_1783_, 1, v___x_1781_);
lean_ctor_set(v___x_1783_, 2, v___x_1781_);
lean_ctor_set(v___x_1783_, 3, v___x_1782_);
lean_ctor_set(v___x_1783_, 4, v_knownSize_1766_);
lean_ctor_set(v___x_1783_, 5, v___x_1781_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*6, v___x_1767_);
v___x_1784_ = lean_st_ref_swap(v___y_1768_, v___x_1783_);
lean_dec(v___x_1784_);
v___x_1785_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1___boxed(lean_object* v_ending_1786_, lean_object* v_knownSize_1787_, lean_object* v___x_1788_, lean_object* v___y_1789_, lean_object* v_x_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v___x_11097__boxed_1792_; lean_object* v_res_1793_; 
v___x_11097__boxed_1792_ = lean_unbox(v___x_1788_);
v_res_1793_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1(v_ending_1786_, v_knownSize_1787_, v___x_11097__boxed_1792_, v___y_1789_, v_x_1790_);
lean_dec(v___y_1789_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3(lean_object* v_val_1794_, lean_object* v_x_1795_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v_val_1794_);
v_a_1797_ = lean_ctor_get(v_x_1795_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_x_1795_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1799_ = v_x_1795_;
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v_x_1795_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1815_; 
v_a_1806_ = lean_ctor_get(v_x_1795_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_x_1795_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1808_ = v_x_1795_;
v_isShared_1809_ = v_isSharedCheck_1815_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v_x_1795_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1815_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_val_1794_);
lean_ctor_set(v___x_1810_, 1, v_a_1806_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3___boxed(lean_object* v_val_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3(v_val_1816_, v_x_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2(lean_object* v_leftover_1824_, lean_object* v_ending_1825_, lean_object* v_knownSize_1826_, uint8_t v___x_1827_, lean_object* v___f_1828_, lean_object* v_____r_1829_, lean_object* v___y_1830_){
_start:
{
if (lean_obj_tag(v_leftover_1824_) == 0)
{
lean_object* v___x_1832_; lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v___f_1828_);
v___x_1832_ = lean_box(v___x_1827_);
lean_inc(v___y_1830_);
v___f_1833_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1833_, 0, v_ending_1825_);
lean_closure_set(v___f_1833_, 1, v_knownSize_1826_);
lean_closure_set(v___f_1833_, 2, v___x_1832_);
lean_closure_set(v___f_1833_, 3, v___y_1830_);
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___closed__1));
v___x_1836_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1834_, v___x_1827_, v___x_1835_, v___f_1833_);
return v___x_1836_;
}
else
{
lean_object* v_val_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1883_; 
v_val_1837_ = lean_ctor_get(v_leftover_1824_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_leftover_1824_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1839_ = v_leftover_1824_;
v_isShared_1840_ = v_isSharedCheck_1883_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_val_1837_);
lean_dec(v_leftover_1824_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1883_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___f_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___y_1850_; 
v___x_1841_ = lean_box(v___x_1827_);
lean_inc(v___y_1830_);
v___f_1842_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1842_, 0, v_ending_1825_);
lean_closure_set(v___f_1842_, 1, v_knownSize_1826_);
lean_closure_set(v___f_1842_, 2, v___x_1841_);
lean_closure_set(v___f_1842_, 3, v___y_1830_);
v___f_1843_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1843_, 0, v_val_1837_);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_io_promise_new();
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
v___x_1848_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1844_, v___x_1827_, v___x_1847_, v___f_1843_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1853_; 
lean_dec_ref(v___f_1828_);
v_a_1853_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1848_, 1);
if (lean_obj_tag(v_a_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_del_object(v___x_1839_);
v_a_1854_ = lean_ctor_get(v_a_1853_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_a_1853_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v_a_1853_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v_a_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
v___y_1850_ = v___x_1859_;
goto v___jp_1849_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1872_; 
v_a_1862_ = lean_ctor_get(v_a_1853_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_a_1853_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1864_ = v_a_1853_;
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v_a_1853_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v_a_1862_);
v___x_1867_ = v___x_1839_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1867_);
v___x_1869_ = v___x_1864_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
v___y_1850_ = v___x_1869_;
goto v___jp_1849_;
}
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1882_; 
lean_del_object(v___x_1839_);
v_a_1873_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1875_ = v___x_1848_;
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1848_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = lean_task_map(v___f_1828_, v_a_1873_, v___x_1844_, v___x_1827_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1877_);
v___x_1879_ = v___x_1875_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; 
v___x_1880_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1844_, v___x_1827_, v___x_1879_, v___f_1842_);
return v___x_1880_;
}
}
}
v___jp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___y_1850_);
v___x_1852_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1844_, v___x_1827_, v___x_1851_, v___f_1842_);
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___boxed(lean_object* v_leftover_1884_, lean_object* v_ending_1885_, lean_object* v_knownSize_1886_, lean_object* v___x_1887_, lean_object* v___f_1888_, lean_object* v_____r_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
uint8_t v___x_11196__boxed_1892_; lean_object* v_res_1893_; 
v___x_11196__boxed_1892_ = lean_unbox(v___x_1887_);
v_res_1893_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2(v_leftover_1884_, v_ending_1885_, v_knownSize_1886_, v___x_11196__boxed_1892_, v___f_1888_, v_____r_1889_, v___y_1890_);
lean_dec(v___y_1890_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5(lean_object* v_pendingProducer_1894_, lean_object* v___f_1895_, uint8_t v___x_1896_, lean_object* v_____r_1897_, lean_object* v___y_1898_){
_start:
{
if (lean_obj_tag(v_pendingProducer_1894_) == 1)
{
lean_object* v_val_1900_; lean_object* v_done_1901_; lean_object* v___f_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_val_1900_ = lean_ctor_get(v_pendingProducer_1894_, 0);
v_done_1901_ = lean_ctor_get(v_val_1900_, 1);
lean_inc(v___y_1898_);
v___f_1902_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1902_, 0, v___f_1895_);
lean_closure_set(v___f_1902_, 1, v___y_1898_);
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = lean_box(v___x_1896_);
v___x_1905_ = lean_io_promise_resolve(v___x_1904_, v_done_1901_);
v___x_1906_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1907_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1903_, v___x_1896_, v___x_1906_, v___f_1902_);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_box(0);
lean_inc(v___y_1898_);
v___x_1909_ = lean_apply_3(v___f_1895_, v___x_1908_, v___y_1898_, lean_box(0));
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5___boxed(lean_object* v_pendingProducer_1910_, lean_object* v___f_1911_, lean_object* v___x_1912_, lean_object* v_____r_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
uint8_t v___x_11324__boxed_1916_; lean_object* v_res_1917_; 
v___x_11324__boxed_1916_ = lean_unbox(v___x_1912_);
v_res_1917_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5(v_pendingProducer_1910_, v___f_1911_, v___x_11324__boxed_1916_, v_____r_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec(v_pendingProducer_1910_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7(lean_object* v_ending_1918_, uint8_t v___x_1919_, lean_object* v___f_1920_, lean_object* v_pendingProducer_1921_, lean_object* v_interestWaiter_1922_, lean_object* v_____r_1923_, lean_object* v_leftover_1924_, lean_object* v_knownSize_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; lean_object* v___f_1931_; 
v___x_1928_ = lean_box(v___x_1919_);
v___f_1929_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1929_, 0, v_leftover_1924_);
lean_closure_set(v___f_1929_, 1, v_ending_1918_);
lean_closure_set(v___f_1929_, 2, v_knownSize_1925_);
lean_closure_set(v___f_1929_, 3, v___x_1928_);
lean_closure_set(v___f_1929_, 4, v___f_1920_);
v___x_1930_ = lean_box(v___x_1919_);
lean_inc_ref(v___f_1929_);
lean_inc(v_pendingProducer_1921_);
v___f_1931_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1931_, 0, v_pendingProducer_1921_);
lean_closure_set(v___f_1931_, 1, v___f_1929_);
lean_closure_set(v___f_1931_, 2, v___x_1930_);
if (lean_obj_tag(v_interestWaiter_1922_) == 1)
{
lean_object* v_val_1932_; lean_object* v___f_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec_ref(v___f_1929_);
lean_dec(v_pendingProducer_1921_);
v_val_1932_ = lean_ctor_get(v_interestWaiter_1922_, 0);
lean_inc(v___y_1926_);
v___f_1933_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1933_, 0, v___f_1931_);
lean_closure_set(v___f_1933_, 1, v___y_1926_);
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_1932_, v___x_1919_);
v___x_1936_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1937_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1934_, v___x_1919_, v___x_1936_, v___f_1933_);
return v___x_1937_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec_ref(v___f_1931_);
v___x_1938_ = lean_box(0);
v___x_1939_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__5(v_pendingProducer_1921_, v___f_1929_, v___x_1919_, v___x_1938_, v___y_1926_);
lean_dec(v_pendingProducer_1921_);
return v___x_1939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7___boxed(lean_object* v_ending_1940_, lean_object* v___x_1941_, lean_object* v___f_1942_, lean_object* v_pendingProducer_1943_, lean_object* v_interestWaiter_1944_, lean_object* v_____r_1945_, lean_object* v_leftover_1946_, lean_object* v_knownSize_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
uint8_t v___x_11362__boxed_1950_; lean_object* v_res_1951_; 
v___x_11362__boxed_1950_ = lean_unbox(v___x_1941_);
v_res_1951_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7(v_ending_1940_, v___x_11362__boxed_1950_, v___f_1942_, v_pendingProducer_1943_, v_interestWaiter_1944_, v_____r_1945_, v_leftover_1946_, v_knownSize_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec(v_interestWaiter_1944_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9(lean_object* v_ending_1952_, lean_object* v___f_1953_, lean_object* v_a_1954_, lean_object* v_x_1955_){
_start:
{
if (lean_obj_tag(v_x_1955_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v___f_1953_);
lean_dec(v_ending_1952_);
v_a_1957_ = lean_ctor_get(v_x_1955_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_x_1955_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1959_ = v_x_1955_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v_x_1955_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2042_; 
v_a_1966_ = lean_ctor_get(v_x_1955_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_x_1955_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_1968_ = v_x_1955_;
v_isShared_1969_ = v_isSharedCheck_2042_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v_x_1955_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2042_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_ended_1970_; 
v_ended_1970_ = lean_ctor_get(v_a_1966_, 3);
if (lean_obj_tag(v_ended_1970_) == 0)
{
lean_object* v_pendingProducer_1971_; lean_object* v_pendingConsumer_1972_; lean_object* v_interestWaiter_1973_; lean_object* v_knownSize_1974_; lean_object* v_pendingIncomplete_1975_; uint8_t v___x_1976_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___x_1985_; lean_object* v___f_1986_; lean_object* v___y_1988_; 
v_pendingProducer_1971_ = lean_ctor_get(v_a_1966_, 0);
lean_inc_n(v_pendingProducer_1971_, 2);
v_pendingConsumer_1972_ = lean_ctor_get(v_a_1966_, 1);
lean_inc(v_pendingConsumer_1972_);
v_interestWaiter_1973_ = lean_ctor_get(v_a_1966_, 2);
lean_inc_n(v_interestWaiter_1973_, 2);
v_knownSize_1974_ = lean_ctor_get(v_a_1966_, 4);
lean_inc(v_knownSize_1974_);
v_pendingIncomplete_1975_ = lean_ctor_get(v_a_1966_, 5);
lean_inc(v_pendingIncomplete_1975_);
lean_dec(v_a_1966_);
v___x_1976_ = 0;
v___x_1985_ = lean_box(v___x_1976_);
lean_inc_ref(v___f_1953_);
lean_inc(v_ending_1952_);
v___f_1986_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7___boxed), 10, 5);
lean_closure_set(v___f_1986_, 0, v_ending_1952_);
lean_closure_set(v___f_1986_, 1, v___x_1985_);
lean_closure_set(v___f_1986_, 2, v___f_1953_);
lean_closure_set(v___f_1986_, 3, v_pendingProducer_1971_);
lean_closure_set(v___f_1986_, 4, v_interestWaiter_1973_);
if (lean_obj_tag(v_pendingProducer_1971_) == 0)
{
if (lean_obj_tag(v_pendingIncomplete_1975_) == 0)
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_box(0);
v___y_1988_ = v___x_2025_;
goto v___jp_1987_;
}
else
{
lean_object* v_val_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2039_; 
v_val_2026_ = lean_ctor_get(v_pendingIncomplete_1975_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_pendingIncomplete_1975_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2028_ = v_pendingIncomplete_1975_;
v_isShared_2029_ = v_isSharedCheck_2039_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_val_2026_);
lean_dec(v_pendingIncomplete_1975_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2039_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v_data_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2030_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(v_val_2026_);
v_data_2031_ = lean_ctor_get(v___x_2030_, 0);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_byte_array_size(v_data_2031_);
v___x_2034_ = lean_nat_dec_lt(v___x_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
lean_dec_ref(v___x_2030_);
lean_del_object(v___x_2028_);
v___x_2035_ = lean_box(0);
v___y_1988_ = v___x_2035_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_2037_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2030_);
v___x_2037_ = v___x_2028_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2030_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v___y_1988_ = v___x_2037_;
goto v___jp_1987_;
}
}
}
}
}
else
{
lean_object* v___x_2040_; 
lean_dec(v_pendingIncomplete_1975_);
v___x_2040_ = lean_box(0);
v___y_1988_ = v___x_2040_;
goto v___jp_1987_;
}
v___jp_1977_:
{
lean_object* v___x_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v___y_1979_, v___y_1980_);
lean_dec_ref(v___y_1979_);
v___x_1983_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_1984_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1981_, v___x_1976_, v___x_1983_, v___y_1978_);
return v___x_1984_;
}
v___jp_1987_:
{
if (lean_obj_tag(v_pendingConsumer_1972_) == 1)
{
lean_dec(v_interestWaiter_1973_);
lean_dec(v_pendingProducer_1971_);
lean_dec_ref(v___f_1953_);
if (lean_obj_tag(v___y_1988_) == 0)
{
lean_object* v_val_1989_; lean_object* v___f_1990_; 
v_val_1989_ = lean_ctor_get(v_pendingConsumer_1972_, 0);
lean_inc(v_val_1989_);
lean_dec_ref_known(v_pendingConsumer_1972_, 1);
lean_inc(v_a_1954_);
v___f_1990_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1990_, 0, v___f_1986_);
lean_closure_set(v___f_1990_, 1, v___y_1988_);
lean_closure_set(v___f_1990_, 2, v_knownSize_1974_);
lean_closure_set(v___f_1990_, 3, v_a_1954_);
if (lean_obj_tag(v_ending_1952_) == 0)
{
lean_object* v___x_1992_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___y_1988_);
v___x_1992_ = v___x_1968_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___y_1988_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v___y_1978_ = v___f_1990_;
v___y_1979_ = v_val_1989_;
v___y_1980_ = v___x_1992_;
goto v___jp_1977_;
}
}
else
{
lean_object* v_err_1994_; lean_object* v___x_1996_; 
v_err_1994_ = lean_ctor_get(v_ending_1952_, 0);
lean_inc(v_err_1994_);
lean_dec_ref_known(v_ending_1952_, 1);
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 0);
lean_ctor_set(v___x_1968_, 0, v_err_1994_);
v___x_1996_ = v___x_1968_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_err_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
v___y_1978_ = v___f_1990_;
v___y_1979_ = v_val_1989_;
v___y_1980_ = v___x_1996_;
goto v___jp_1977_;
}
}
}
else
{
lean_object* v_val_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_ending_1952_);
v_val_1998_ = lean_ctor_get(v_pendingConsumer_1972_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_pendingConsumer_1972_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2000_ = v_pendingConsumer_1972_;
v_isShared_2001_ = v_isSharedCheck_2022_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_val_1998_);
lean_dec(v_pendingConsumer_1972_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2022_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_val_2002_; lean_object* v___f_2003_; lean_object* v___x_2005_; 
v_val_2002_ = lean_ctor_get(v___y_1988_, 0);
lean_inc(v_val_2002_);
lean_inc(v_a_1954_);
lean_inc_ref_n(v___y_1988_, 2);
v___f_2003_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__8___boxed), 7, 5);
lean_closure_set(v___f_2003_, 0, v___f_1986_);
lean_closure_set(v___f_2003_, 1, v___y_1988_);
lean_closure_set(v___f_2003_, 2, v_knownSize_1974_);
lean_closure_set(v___f_2003_, 3, v_a_1954_);
lean_closure_set(v___f_2003_, 4, v_val_2002_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___y_1988_);
v___x_2005_ = v___x_1968_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___y_1988_);
v___x_2005_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2019_; 
v_isSharedCheck_2019_ = !lean_is_exclusive(v___y_1988_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v___y_1988_, 0);
lean_dec(v_unused_2020_);
v___x_2007_ = v___y_1988_;
v_isShared_2008_ = v_isSharedCheck_2019_;
goto v_resetjp_2006_;
}
else
{
lean_dec(v___y_1988_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2019_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_1998_, v___x_2005_);
lean_dec(v_val_1998_);
v___x_2011_ = lean_box(v___x_2010_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2011_);
v___x_2013_ = v___x_2007_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 0);
lean_ctor_set(v___x_2000_, 0, v___x_2013_);
v___x_2015_ = v___x_2000_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; 
v___x_2016_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2009_, v___x_1976_, v___x_2015_, v___f_2003_);
return v___x_2016_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec_ref(v___f_1986_);
lean_dec(v_pendingConsumer_1972_);
lean_del_object(v___x_1968_);
v___x_2023_ = lean_box(0);
v___x_2024_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__7(v_ending_1952_, v___x_1976_, v___f_1953_, v_pendingProducer_1971_, v_interestWaiter_1973_, v___x_2023_, v___y_1988_, v_knownSize_1974_, v_a_1954_);
lean_dec(v_interestWaiter_1973_);
return v___x_2024_;
}
}
}
else
{
lean_object* v___x_2041_; 
lean_del_object(v___x_1968_);
lean_dec(v_a_1966_);
lean_dec_ref(v___f_1953_);
lean_dec(v_ending_1952_);
v___x_2041_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9___boxed(lean_object* v_ending_2043_, lean_object* v___f_2044_, lean_object* v_a_2045_, lean_object* v_x_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9(v_ending_2043_, v___f_2044_, v_a_2045_, v_x_2046_);
lean_dec(v_a_2045_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(lean_object* v_ending_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v___f_2053_; lean_object* v___f_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___f_2053_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___closed__0));
lean_inc(v_a_2051_);
v___f_2054_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__9___boxed), 5, 3);
lean_closure_set(v___f_2054_, 0, v_ending_2050_);
lean_closure_set(v___f_2054_, 1, v___f_2053_);
lean_closure_set(v___f_2054_, 2, v_a_2051_);
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = 0;
v___x_2057_ = lean_st_ref_get(v_a_2051_);
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
v___x_2060_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2055_, v___x_2056_, v___x_2059_, v___f_2054_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_ending_2061_, lean_object* v_a_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v_ending_2061_, v_a_2062_);
lean_dec(v_a_2062_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(uint8_t v_closeAfterProducer_2065_, lean_object* v___f_2066_, lean_object* v___x_2067_, lean_object* v_a_2068_, uint8_t v___x_2069_, lean_object* v___f_2070_, lean_object* v_x_2071_){
_start:
{
if (lean_obj_tag(v_x_2071_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v___f_2070_);
lean_dec_ref(v___f_2066_);
v_a_2073_ = lean_ctor_get(v_x_2071_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_x_2071_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2075_ = v_x_2071_;
v_isShared_2076_ = v_isSharedCheck_2081_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v_x_2071_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2081_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2073_);
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
else
{
lean_dec_ref_known(v_x_2071_, 1);
if (v_closeAfterProducer_2065_ == 0)
{
lean_object* v___x_2082_; 
lean_dec_ref(v___f_2070_);
lean_inc(v_a_2068_);
v___x_2082_ = lean_apply_3(v___f_2066_, v___x_2067_, v_a_2068_, lean_box(0));
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec_ref(v___f_2066_);
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___x_2083_, v_a_2068_);
v___x_2086_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2084_, v___x_2069_, v___x_2085_, v___f_2070_);
return v___x_2086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed(lean_object* v_closeAfterProducer_2087_, lean_object* v___f_2088_, lean_object* v___x_2089_, lean_object* v_a_2090_, lean_object* v___x_2091_, lean_object* v___f_2092_, lean_object* v_x_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v_closeAfterProducer_boxed_2095_; uint8_t v___x_11609__boxed_2096_; lean_object* v_res_2097_; 
v_closeAfterProducer_boxed_2095_ = lean_unbox(v_closeAfterProducer_2087_);
v___x_11609__boxed_2096_ = lean_unbox(v___x_2091_);
v_res_2097_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2(v_closeAfterProducer_boxed_2095_, v___f_2088_, v___x_2089_, v_a_2090_, v___x_11609__boxed_2096_, v___f_2092_, v_x_2093_);
lean_dec(v_a_2090_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3(uint8_t v_closeAfterProducer_2098_, lean_object* v___f_2099_, lean_object* v_a_2100_, uint8_t v___x_2101_, lean_object* v___f_2102_, lean_object* v_done_2103_, lean_object* v_x_2104_){
_start:
{
if (lean_obj_tag(v_x_2104_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v___f_2102_);
lean_dec_ref(v___f_2099_);
v_a_2106_ = lean_ctor_get(v_x_2104_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_x_2104_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2108_ = v_x_2104_;
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v_x_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
}
else
{
uint8_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___f_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_dec_ref_known(v_x_2104_, 1);
v___x_2115_ = 1;
v___x_2116_ = lean_box(0);
v___x_2117_ = lean_box(v_closeAfterProducer_2098_);
v___x_2118_ = lean_box(v___x_2101_);
lean_inc(v_a_2100_);
v___f_2119_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__2___boxed), 8, 6);
lean_closure_set(v___f_2119_, 0, v___x_2117_);
lean_closure_set(v___f_2119_, 1, v___f_2099_);
lean_closure_set(v___f_2119_, 2, v___x_2116_);
lean_closure_set(v___f_2119_, 3, v_a_2100_);
lean_closure_set(v___f_2119_, 4, v___x_2118_);
lean_closure_set(v___f_2119_, 5, v___f_2102_);
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_box(v___x_2115_);
v___x_2122_ = lean_io_promise_resolve(v___x_2121_, v_done_2103_);
v___x_2123_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2124_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2120_, v___x_2101_, v___x_2123_, v___f_2119_);
return v___x_2124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3___boxed(lean_object* v_closeAfterProducer_2125_, lean_object* v___f_2126_, lean_object* v_a_2127_, lean_object* v___x_2128_, lean_object* v___f_2129_, lean_object* v_done_2130_, lean_object* v_x_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v_closeAfterProducer_boxed_2133_; uint8_t v___x_11658__boxed_2134_; lean_object* v_res_2135_; 
v_closeAfterProducer_boxed_2133_ = lean_unbox(v_closeAfterProducer_2125_);
v___x_11658__boxed_2134_ = lean_unbox(v___x_2128_);
v_res_2135_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3(v_closeAfterProducer_boxed_2133_, v___f_2126_, v_a_2127_, v___x_11658__boxed_2134_, v___f_2129_, v_done_2130_, v_x_2131_);
lean_dec(v_done_2130_);
lean_dec(v_a_2127_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(lean_object* v_chunk_2136_, lean_object* v_____r_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_chunk_2136_);
v___x_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed(lean_object* v_chunk_2143_, lean_object* v_____r_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0(v_chunk_2143_, v_____r_2144_, v___y_2145_);
lean_dec(v___y_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4(lean_object* v_a_2150_, lean_object* v_x_2151_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2161_; 
v_a_2153_ = lean_ctor_get(v_x_2151_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_x_2151_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2155_ = v_x_2151_;
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v_x_2151_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v_pendingProducer_2163_; 
v_a_2162_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v_x_2151_, 1);
v_pendingProducer_2163_ = lean_ctor_get(v_a_2162_, 0);
if (lean_obj_tag(v_pendingProducer_2163_) == 1)
{
lean_object* v_val_2164_; lean_object* v_pendingConsumer_2165_; lean_object* v_interestWaiter_2166_; lean_object* v_ended_2167_; lean_object* v_knownSize_2168_; lean_object* v_pendingIncomplete_2169_; uint8_t v_closeAfterProducer_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2191_; 
v_val_2164_ = lean_ctor_get(v_pendingProducer_2163_, 0);
lean_inc(v_val_2164_);
v_pendingConsumer_2165_ = lean_ctor_get(v_a_2162_, 1);
v_interestWaiter_2166_ = lean_ctor_get(v_a_2162_, 2);
v_ended_2167_ = lean_ctor_get(v_a_2162_, 3);
v_knownSize_2168_ = lean_ctor_get(v_a_2162_, 4);
v_pendingIncomplete_2169_ = lean_ctor_get(v_a_2162_, 5);
v_closeAfterProducer_2170_ = lean_ctor_get_uint8(v_a_2162_, sizeof(void*)*6);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_a_2162_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v_a_2162_, 0);
lean_dec(v_unused_2192_);
v___x_2172_ = v_a_2162_;
v_isShared_2173_ = v_isSharedCheck_2191_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_pendingIncomplete_2169_);
lean_inc(v_knownSize_2168_);
lean_inc(v_ended_2167_);
lean_inc(v_interestWaiter_2166_);
lean_inc(v_pendingConsumer_2165_);
lean_dec(v_a_2162_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2191_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_chunk_2174_; lean_object* v_done_2175_; lean_object* v___x_2176_; lean_object* v___f_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___f_2183_; lean_object* v___x_2185_; 
v_chunk_2174_ = lean_ctor_get(v_val_2164_, 0);
lean_inc_ref_n(v_chunk_2174_, 2);
v_done_2175_ = lean_ctor_get(v_val_2164_, 1);
lean_inc(v_done_2175_);
lean_dec(v_val_2164_);
v___x_2176_ = lean_box(0);
v___f_2177_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2177_, 0, v_chunk_2174_);
lean_inc_n(v_a_2150_, 2);
lean_inc_ref(v___f_2177_);
v___f_2178_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2178_, 0, v___f_2177_);
lean_closure_set(v___f_2178_, 1, v_a_2150_);
v___x_2179_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_2168_, v_chunk_2174_);
lean_dec_ref(v_chunk_2174_);
v___x_2180_ = 0;
v___x_2181_ = lean_box(v_closeAfterProducer_2170_);
v___x_2182_ = lean_box(v___x_2180_);
v___f_2183_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__3___boxed), 8, 6);
lean_closure_set(v___f_2183_, 0, v___x_2181_);
lean_closure_set(v___f_2183_, 1, v___f_2177_);
lean_closure_set(v___f_2183_, 2, v_a_2150_);
lean_closure_set(v___f_2183_, 3, v___x_2182_);
lean_closure_set(v___f_2183_, 4, v___f_2178_);
lean_closure_set(v___f_2183_, 5, v_done_2175_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 4, v___x_2179_);
lean_ctor_set(v___x_2172_, 0, v___x_2176_);
v___x_2185_ = v___x_2172_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_pendingConsumer_2165_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_interestWaiter_2166_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v_ended_2167_);
lean_ctor_set(v_reuseFailAlloc_2190_, 4, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2190_, 5, v_pendingIncomplete_2169_);
v___x_2185_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*6, v___x_2180_);
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = lean_st_ref_swap(v_a_2150_, v___x_2185_);
lean_dec(v___x_2187_);
v___x_2188_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_2189_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2186_, v___x_2180_, v___x_2188_, v___f_2183_);
return v___x_2189_;
}
}
}
else
{
lean_object* v___x_2193_; 
lean_dec(v_a_2162_);
v___x_2193_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___closed__0));
return v___x_2193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___boxed(lean_object* v_a_2194_, lean_object* v_x_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4(v_a_2194_, v_x_2195_);
lean_dec(v_a_2194_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(lean_object* v_a_2198_){
_start:
{
lean_object* v___f_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_inc(v_a_2198_);
v___f_2200_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2200_, 0, v_a_2198_);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = 0;
v___x_2203_ = lean_st_ref_get(v_a_2198_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
v___x_2206_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2201_, v___x_2202_, v___x_2205_, v___f_2200_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___boxed(lean_object* v_a_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_2207_);
lean_dec(v_a_2207_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(lean_object* v_a_2211_){
_start:
{
lean_object* v___f_2213_; lean_object* v___f_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___f_2213_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___closed__0));
lean_inc(v_a_2211_);
v___f_2214_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2214_, 0, v_a_2211_);
lean_closure_set(v___f_2214_, 1, v___f_2213_);
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = 0;
v___x_2217_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0(v_a_2211_);
v___x_2218_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2215_, v___x_2216_, v___x_2217_, v___f_2214_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(lean_object* v_a_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_2219_);
lean_dec(v_a_2219_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1(lean_object* v___y_2222_, lean_object* v___f_2223_, lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref(v___f_2223_);
v_a_2226_ = lean_ctor_get(v_x_2224_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_x_2224_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2228_ = v_x_2224_;
v_isShared_2229_ = v_isSharedCheck_2234_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v_x_2224_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2234_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
return v___x_2232_;
}
}
}
else
{
lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec_ref_known(v_x_2224_, 1);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = 0;
v___x_2237_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2222_);
v___x_2238_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2235_, v___x_2236_, v___x_2237_, v___f_2223_);
return v___x_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(lean_object* v___y_2239_, lean_object* v___f_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Std_Http_Body_Stream_tryRecv___lam__1(v___y_2239_, v___f_2240_, v_x_2241_);
lean_dec(v___y_2239_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2(lean_object* v___f_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___f_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_inc(v___y_2245_);
v___f_2247_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecv___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2247_, 0, v___y_2245_);
lean_closure_set(v___f_2247_, 1, v___f_2244_);
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = 0;
v___x_2250_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2245_);
v___x_2251_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2248_, v___x_2249_, v___x_2250_, v___f_2247_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___lam__2___boxed(lean_object* v___f_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Std_Http_Body_Stream_tryRecv___lam__2(v___f_2252_, v___y_2253_);
lean_dec(v___y_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv(lean_object* v_stream_2259_){
_start:
{
lean_object* v___f_2261_; lean_object* v___x_2262_; 
v___f_2261_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecv___closed__1));
v___x_2262_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2259_, v___f_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecv___boxed(lean_object* v_stream_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Std_Http_Body_Stream_tryRecv(v_stream_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(lean_object* v_x_2266_){
_start:
{
uint8_t v___y_2269_; 
if (lean_obj_tag(v_x_2266_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2281_; 
v_a_2273_ = lean_ctor_get(v_x_2266_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2275_ = v_x_2266_;
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v_x_2266_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v_pendingProducer_2283_; 
v_a_2282_ = lean_ctor_get(v_x_2266_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v_x_2266_, 1);
v_pendingProducer_2283_ = lean_ctor_get(v_a_2282_, 0);
if (lean_obj_tag(v_pendingProducer_2283_) == 0)
{
lean_object* v_ended_2284_; 
v_ended_2284_ = lean_ctor_get(v_a_2282_, 3);
lean_inc(v_ended_2284_);
lean_dec(v_a_2282_);
if (lean_obj_tag(v_ended_2284_) == 0)
{
uint8_t v___x_2285_; 
v___x_2285_ = 0;
v___y_2269_ = v___x_2285_;
goto v___jp_2268_;
}
else
{
uint8_t v___x_2286_; 
lean_dec_ref_known(v_ended_2284_, 1);
v___x_2286_ = 1;
v___y_2269_ = v___x_2286_;
goto v___jp_2268_;
}
}
else
{
uint8_t v___x_2287_; 
lean_dec(v_a_2282_);
v___x_2287_ = 1;
v___y_2269_ = v___x_2287_;
goto v___jp_2268_;
}
}
v___jp_2268_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = lean_box(v___y_2269_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed(lean_object* v_x_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(v_x_2288_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(lean_object* v_a_2292_){
_start:
{
lean_object* v___f_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___f_2294_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0));
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = 0;
v___x_2297_ = lean_st_ref_get(v_a_2292_);
v___x_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
v___x_2300_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2295_, v___x_2296_, v___x_2299_, v___f_2294_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___boxed(lean_object* v_a_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v_a_2301_);
lean_dec(v_a_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0(lean_object* v_x_2304_){
_start:
{
if (lean_obj_tag(v_x_2304_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2314_; 
v_a_2306_ = lean_ctor_get(v_x_2304_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_x_2304_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2308_ = v_x_2304_;
v_isShared_2309_ = v_isSharedCheck_2314_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v_x_2304_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2314_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
}
else
{
lean_object* v_a_2315_; 
v_a_2315_ = lean_ctor_get(v_x_2304_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v_x_2304_, 1);
if (lean_obj_tag(v_a_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2324_; 
v_a_2316_ = lean_ctor_get(v_a_2315_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_a_2315_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2318_ = v_a_2315_;
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v_a_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2334_; 
v_a_2325_ = lean_ctor_get(v_a_2315_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_a_2315_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2327_ = v_a_2315_;
v_isShared_2328_ = v_isSharedCheck_2334_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v_a_2315_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2334_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2325_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed(lean_object* v_x_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Std_Http_Body_Stream_tryRecvBody___lam__0(v_x_2335_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1(lean_object* v___y_2342_, lean_object* v___f_2343_, lean_object* v_x_2344_){
_start:
{
if (lean_obj_tag(v_x_2344_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v___f_2343_);
v_a_2346_ = lean_ctor_get(v_x_2344_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_x_2344_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2348_ = v_x_2344_;
v_isShared_2349_ = v_isSharedCheck_2354_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v_x_2344_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2354_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
return v___x_2352_;
}
}
}
else
{
lean_object* v_a_2355_; uint8_t v___x_2356_; 
v_a_2355_ = lean_ctor_get(v_x_2344_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v_x_2344_, 1);
v___x_2356_ = lean_unbox(v_a_2355_);
lean_dec(v_a_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v___f_2343_);
v___x_2357_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1));
return v___x_2357_;
}
else
{
lean_object* v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2358_ = lean_unsigned_to_nat(0u);
v___x_2359_ = 0;
v___x_2360_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_2342_);
v___x_2361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2358_, v___x_2359_, v___x_2360_, v___f_2343_);
return v___x_2361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed(lean_object* v___y_2362_, lean_object* v___f_2363_, lean_object* v_x_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1(v___y_2362_, v___f_2363_, v_x_2364_);
lean_dec(v___y_2362_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2(lean_object* v___y_2367_, lean_object* v___f_2368_, lean_object* v_x_2369_){
_start:
{
if (lean_obj_tag(v_x_2369_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2379_; 
lean_dec_ref(v___f_2368_);
v_a_2371_ = lean_ctor_get(v_x_2369_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_x_2369_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2373_ = v_x_2369_;
v_isShared_2374_ = v_isSharedCheck_2379_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v_x_2369_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2379_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
}
}
else
{
lean_object* v___x_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec_ref_known(v_x_2369_, 1);
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = 0;
v___x_2382_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_2367_);
v___x_2383_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2380_, v___x_2381_, v___x_2382_, v___f_2368_);
return v___x_2383_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed(lean_object* v___y_2384_, lean_object* v___f_2385_, lean_object* v_x_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Std_Http_Body_Stream_tryRecvBody___lam__2(v___y_2384_, v___f_2385_, v_x_2386_);
lean_dec(v___y_2384_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3(lean_object* v___f_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_inc_n(v___y_2390_, 2);
v___f_2392_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2392_, 0, v___y_2390_);
lean_closure_set(v___f_2392_, 1, v___f_2389_);
v___f_2393_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2393_, 0, v___y_2390_);
lean_closure_set(v___f_2393_, 1, v___f_2392_);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = 0;
v___x_2396_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2390_);
v___x_2397_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2394_, v___x_2395_, v___x_2396_, v___f_2393_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed(lean_object* v___f_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Std_Http_Body_Stream_tryRecvBody___lam__3(v___f_2398_, v___y_2399_);
lean_dec(v___y_2399_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody(lean_object* v_stream_2405_){
_start:
{
lean_object* v___f_2407_; lean_object* v___x_2408_; 
v___f_2407_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_2408_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2405_, v___f_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_tryRecvBody___boxed(lean_object* v_stream_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_2409_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(lean_object* v_a_2412_){
_start:
{
lean_object* v___x_2414_; lean_object* v_pendingProducer_2415_; lean_object* v_pendingConsumer_2416_; lean_object* v_interestWaiter_2417_; lean_object* v_ended_2418_; lean_object* v_knownSize_2419_; lean_object* v_pendingIncomplete_2420_; uint8_t v_closeAfterProducer_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2448_; 
v___x_2414_ = lean_st_ref_get(v_a_2412_);
v_pendingProducer_2415_ = lean_ctor_get(v___x_2414_, 0);
v_pendingConsumer_2416_ = lean_ctor_get(v___x_2414_, 1);
v_interestWaiter_2417_ = lean_ctor_get(v___x_2414_, 2);
v_ended_2418_ = lean_ctor_get(v___x_2414_, 3);
v_knownSize_2419_ = lean_ctor_get(v___x_2414_, 4);
v_pendingIncomplete_2420_ = lean_ctor_get(v___x_2414_, 5);
v_closeAfterProducer_2421_ = lean_ctor_get_uint8(v___x_2414_, sizeof(void*)*6);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2423_ = v___x_2414_;
v_isShared_2424_ = v_isSharedCheck_2448_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_pendingIncomplete_2420_);
lean_inc(v_knownSize_2419_);
lean_inc(v_ended_2418_);
lean_inc(v_interestWaiter_2417_);
lean_inc(v_pendingConsumer_2416_);
lean_inc(v_pendingProducer_2415_);
lean_dec(v___x_2414_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2448_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___y_2426_; lean_object* v_interestWaiter_2427_; lean_object* v___y_2428_; lean_object* v_pendingConsumer_2435_; lean_object* v___y_2436_; 
if (lean_obj_tag(v_pendingConsumer_2416_) == 1)
{
lean_object* v_val_2442_; 
v_val_2442_ = lean_ctor_get(v_pendingConsumer_2416_, 0);
if (lean_obj_tag(v_val_2442_) == 1)
{
lean_object* v_finished_2443_; lean_object* v_finished_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v_finished_2443_ = lean_ctor_get(v_val_2442_, 0);
v_finished_2444_ = lean_ctor_get(v_finished_2443_, 0);
v___x_2445_ = lean_st_ref_get(v_finished_2444_);
v___x_2446_ = lean_unbox(v___x_2445_);
lean_dec(v___x_2445_);
if (v___x_2446_ == 0)
{
v_pendingConsumer_2435_ = v_pendingConsumer_2416_;
v___y_2436_ = v_a_2412_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2447_; 
lean_dec_ref_known(v_pendingConsumer_2416_, 1);
v___x_2447_ = lean_box(0);
v_pendingConsumer_2435_ = v___x_2447_;
v___y_2436_ = v_a_2412_;
goto v___jp_2434_;
}
}
else
{
v_pendingConsumer_2435_ = v_pendingConsumer_2416_;
v___y_2436_ = v_a_2412_;
goto v___jp_2434_;
}
}
else
{
v_pendingConsumer_2435_ = v_pendingConsumer_2416_;
v___y_2436_ = v_a_2412_;
goto v___jp_2434_;
}
v___jp_2425_:
{
lean_object* v___x_2430_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 2, v_interestWaiter_2427_);
lean_ctor_set(v___x_2423_, 1, v___y_2426_);
v___x_2430_ = v___x_2423_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_pendingProducer_2415_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___y_2426_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_interestWaiter_2427_);
lean_ctor_set(v_reuseFailAlloc_2433_, 3, v_ended_2418_);
lean_ctor_set(v_reuseFailAlloc_2433_, 4, v_knownSize_2419_);
lean_ctor_set(v_reuseFailAlloc_2433_, 5, v_pendingIncomplete_2420_);
lean_ctor_set_uint8(v_reuseFailAlloc_2433_, sizeof(void*)*6, v_closeAfterProducer_2421_);
v___x_2430_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_st_ref_swap(v___y_2428_, v___x_2430_);
lean_dec(v___x_2432_);
return v___x_2431_;
}
}
v___jp_2434_:
{
if (lean_obj_tag(v_interestWaiter_2417_) == 0)
{
v___y_2426_ = v_pendingConsumer_2435_;
v_interestWaiter_2427_ = v_interestWaiter_2417_;
v___y_2428_ = v___y_2436_;
goto v___jp_2425_;
}
else
{
lean_object* v_val_2437_; lean_object* v_finished_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v_val_2437_ = lean_ctor_get(v_interestWaiter_2417_, 0);
v_finished_2438_ = lean_ctor_get(v_val_2437_, 0);
v___x_2439_ = lean_st_ref_get(v_finished_2438_);
v___x_2440_ = lean_unbox(v___x_2439_);
lean_dec(v___x_2439_);
if (v___x_2440_ == 0)
{
v___y_2426_ = v_pendingConsumer_2435_;
v_interestWaiter_2427_ = v_interestWaiter_2417_;
v___y_2428_ = v___y_2436_;
goto v___jp_2425_;
}
else
{
lean_object* v___x_2441_; 
lean_dec_ref_known(v_interestWaiter_2417_, 1);
v___x_2441_ = lean_box(0);
v___y_2426_ = v_pendingConsumer_2435_;
v_interestWaiter_2427_ = v___x_2441_;
v___y_2428_ = v___y_2436_;
goto v___jp_2425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(lean_object* v_a_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_2449_);
lean_dec(v_a_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(lean_object* v_a_2452_){
_start:
{
lean_object* v___x_2454_; lean_object* v_interestWaiter_2455_; 
v___x_2454_ = lean_st_ref_get(v_a_2452_);
v_interestWaiter_2455_ = lean_ctor_get(v___x_2454_, 2);
lean_inc(v_interestWaiter_2455_);
if (lean_obj_tag(v_interestWaiter_2455_) == 1)
{
lean_object* v_pendingProducer_2456_; lean_object* v_pendingConsumer_2457_; lean_object* v_ended_2458_; lean_object* v_knownSize_2459_; lean_object* v_pendingIncomplete_2460_; uint8_t v_closeAfterProducer_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2474_; 
v_pendingProducer_2456_ = lean_ctor_get(v___x_2454_, 0);
v_pendingConsumer_2457_ = lean_ctor_get(v___x_2454_, 1);
v_ended_2458_ = lean_ctor_get(v___x_2454_, 3);
v_knownSize_2459_ = lean_ctor_get(v___x_2454_, 4);
v_pendingIncomplete_2460_ = lean_ctor_get(v___x_2454_, 5);
v_closeAfterProducer_2461_ = lean_ctor_get_uint8(v___x_2454_, sizeof(void*)*6);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v___x_2454_, 2);
lean_dec(v_unused_2475_);
v___x_2463_ = v___x_2454_;
v_isShared_2464_ = v_isSharedCheck_2474_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_pendingIncomplete_2460_);
lean_inc(v_knownSize_2459_);
lean_inc(v_ended_2458_);
lean_inc(v_pendingConsumer_2457_);
lean_inc(v_pendingProducer_2456_);
lean_dec(v___x_2454_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2474_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v_val_2465_; uint8_t v___x_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v_val_2465_ = lean_ctor_get(v_interestWaiter_2455_, 0);
lean_inc(v_val_2465_);
lean_dec_ref_known(v_interestWaiter_2455_, 1);
v___x_2466_ = 1;
v___x_2467_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2465_, v___x_2466_);
lean_dec(v_val_2465_);
v___x_2468_ = lean_box(0);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 2, v___x_2468_);
v___x_2470_ = v___x_2463_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_pendingProducer_2456_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_pendingConsumer_2457_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2473_, 3, v_ended_2458_);
lean_ctor_set(v_reuseFailAlloc_2473_, 4, v_knownSize_2459_);
lean_ctor_set(v_reuseFailAlloc_2473_, 5, v_pendingIncomplete_2460_);
lean_ctor_set_uint8(v_reuseFailAlloc_2473_, sizeof(void*)*6, v_closeAfterProducer_2461_);
v___x_2470_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_box(0);
v___x_2472_ = lean_st_ref_swap(v_a_2452_, v___x_2470_);
lean_dec(v___x_2472_);
return v___x_2471_;
}
}
}
else
{
lean_object* v___x_2476_; 
lean_dec(v_interestWaiter_2455_);
lean_dec(v___x_2454_);
v___x_2476_ = lean_box(0);
return v___x_2476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(lean_object* v_a_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_2477_);
lean_dec(v_a_2477_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(lean_object* v_mutex_2480_, lean_object* v_k_2481_){
_start:
{
lean_object* v_ref_2483_; lean_object* v_mutex_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_ref_2483_ = lean_ctor_get(v_mutex_2480_, 0);
lean_inc(v_ref_2483_);
v_mutex_2484_ = lean_ctor_get(v_mutex_2480_, 1);
lean_inc(v_mutex_2484_);
lean_dec_ref(v_mutex_2480_);
v___x_2485_ = lean_io_basemutex_lock(v_mutex_2484_);
v___x_2486_ = lean_apply_2(v_k_2481_, v_ref_2483_, lean_box(0));
v___x_2487_ = lean_io_basemutex_unlock(v_mutex_2484_);
lean_dec(v_mutex_2484_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(lean_object* v_mutex_2488_, lean_object* v_k_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_2488_, v_k_2489_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(lean_object* v_00_u03b1_2492_, lean_object* v_00_u03b2_2493_, lean_object* v_mutex_2494_, lean_object* v_k_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_2494_, v_k_2495_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_00_u03b2_2499_, lean_object* v_mutex_2500_, lean_object* v_k_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(v_00_u03b1_2498_, v_00_u03b2_2499_, v_mutex_2500_, v_k_2501_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(lean_object* v_x_2509_){
_start:
{
if (lean_obj_tag(v_x_2509_) == 0)
{
lean_object* v___x_2510_; 
v___x_2510_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2));
return v___x_2510_;
}
else
{
lean_object* v_val_2511_; 
v_val_2511_ = lean_ctor_get(v_x_2509_, 0);
lean_inc(v_val_2511_);
return v_val_2511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___boxed(lean_object* v_x_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(v_x_2512_);
lean_dec(v_x_2512_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1(lean_object* v_ending_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v___x_2517_; lean_object* v_ended_2518_; 
v___x_2517_ = lean_st_ref_get(v_a_2515_);
v_ended_2518_ = lean_ctor_get(v___x_2517_, 3);
if (lean_obj_tag(v_ended_2518_) == 0)
{
lean_object* v_pendingProducer_2519_; lean_object* v_pendingConsumer_2520_; lean_object* v_interestWaiter_2521_; lean_object* v_knownSize_2522_; lean_object* v_pendingIncomplete_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2622_; 
v_pendingProducer_2519_ = lean_ctor_get(v___x_2517_, 0);
v_pendingConsumer_2520_ = lean_ctor_get(v___x_2517_, 1);
v_interestWaiter_2521_ = lean_ctor_get(v___x_2517_, 2);
v_knownSize_2522_ = lean_ctor_get(v___x_2517_, 4);
v_pendingIncomplete_2523_ = lean_ctor_get(v___x_2517_, 5);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2622_ == 0)
{
lean_object* v_unused_2623_; 
v_unused_2623_ = lean_ctor_get(v___x_2517_, 3);
lean_dec(v_unused_2623_);
v___x_2525_ = v___x_2517_;
v_isShared_2526_ = v_isSharedCheck_2622_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_pendingIncomplete_2523_);
lean_inc(v_knownSize_2522_);
lean_inc(v_interestWaiter_2521_);
lean_inc(v_pendingConsumer_2520_);
lean_inc(v_pendingProducer_2519_);
lean_dec(v___x_2517_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2622_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
uint8_t v___x_2527_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v_leftover_2565_; lean_object* v_knownSize_2566_; lean_object* v___y_2567_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2576_; 
v___x_2527_ = 0;
if (lean_obj_tag(v_pendingProducer_2519_) == 0)
{
if (lean_obj_tag(v_pendingIncomplete_2523_) == 0)
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_box(0);
v___y_2576_ = v___x_2606_;
goto v___jp_2575_;
}
else
{
lean_object* v_val_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2620_; 
v_val_2607_ = lean_ctor_get(v_pendingIncomplete_2523_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_pendingIncomplete_2523_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2609_ = v_pendingIncomplete_2523_;
v_isShared_2610_ = v_isSharedCheck_2620_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_val_2607_);
lean_dec(v_pendingIncomplete_2523_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2620_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v_data_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2611_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(v_val_2607_);
v_data_2612_ = lean_ctor_get(v___x_2611_, 0);
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_byte_array_size(v_data_2612_);
v___x_2615_ = lean_nat_dec_lt(v___x_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2609_);
v___x_2616_ = lean_box(0);
v___y_2576_ = v___x_2616_;
goto v___jp_2575_;
}
else
{
lean_object* v___x_2618_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2611_);
v___x_2618_ = v___x_2609_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2611_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
v___y_2576_ = v___x_2618_;
goto v___jp_2575_;
}
}
}
}
}
else
{
lean_object* v___x_2621_; 
lean_dec(v_pendingIncomplete_2523_);
v___x_2621_ = lean_box(0);
v___y_2576_ = v___x_2621_;
goto v___jp_2575_;
}
v___jp_2528_:
{
if (lean_obj_tag(v___y_2530_) == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = lean_box(0);
v___x_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_ending_2514_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 5, v___x_2532_);
lean_ctor_set(v___x_2525_, 4, v___y_2529_);
lean_ctor_set(v___x_2525_, 3, v___x_2533_);
lean_ctor_set(v___x_2525_, 2, v___x_2532_);
lean_ctor_set(v___x_2525_, 1, v___x_2532_);
lean_ctor_set(v___x_2525_, 0, v___x_2532_);
v___x_2535_ = v___x_2525_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2538_, 3, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2538_, 4, v___y_2529_);
lean_ctor_set(v_reuseFailAlloc_2538_, 5, v___x_2532_);
v___x_2535_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_ctor_set_uint8(v___x_2535_, sizeof(void*)*6, v___x_2527_);
v___x_2536_ = lean_box(0);
v___x_2537_ = lean_st_ref_swap(v___y_2531_, v___x_2535_);
lean_dec(v___x_2537_);
return v___x_2536_;
}
}
else
{
lean_object* v_val_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2555_; 
v_val_2539_ = lean_ctor_get(v___y_2530_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___y_2530_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2541_ = v___y_2530_;
v_isShared_2542_ = v_isSharedCheck_2555_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_val_2539_);
lean_dec(v___y_2530_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2555_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2543_ = lean_io_promise_new();
v___x_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2544_, 0, v_val_2539_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2544_);
v___x_2546_ = v___x_2541_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2547_ = lean_box(0);
v___x_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_ending_2514_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 5, v___x_2547_);
lean_ctor_set(v___x_2525_, 4, v___y_2529_);
lean_ctor_set(v___x_2525_, 3, v___x_2548_);
lean_ctor_set(v___x_2525_, 2, v___x_2547_);
lean_ctor_set(v___x_2525_, 1, v___x_2547_);
lean_ctor_set(v___x_2525_, 0, v___x_2546_);
v___x_2550_ = v___x_2525_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v___y_2529_);
lean_ctor_set(v_reuseFailAlloc_2553_, 5, v___x_2547_);
v___x_2550_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*6, v___x_2527_);
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_st_ref_swap(v___y_2531_, v___x_2550_);
lean_dec(v___x_2552_);
return v___x_2551_;
}
}
}
}
}
v___jp_2556_:
{
if (lean_obj_tag(v_pendingProducer_2519_) == 1)
{
lean_object* v_val_2560_; lean_object* v_done_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v_val_2560_ = lean_ctor_get(v_pendingProducer_2519_, 0);
lean_inc(v_val_2560_);
lean_dec_ref_known(v_pendingProducer_2519_, 1);
v_done_2561_ = lean_ctor_get(v_val_2560_, 1);
lean_inc(v_done_2561_);
lean_dec(v_val_2560_);
v___x_2562_ = lean_box(v___x_2527_);
v___x_2563_ = lean_io_promise_resolve(v___x_2562_, v_done_2561_);
lean_dec(v_done_2561_);
v___y_2529_ = v___y_2557_;
v___y_2530_ = v___y_2558_;
v___y_2531_ = v___y_2559_;
goto v___jp_2528_;
}
else
{
lean_dec(v_pendingProducer_2519_);
v___y_2529_ = v___y_2557_;
v___y_2530_ = v___y_2558_;
v___y_2531_ = v___y_2559_;
goto v___jp_2528_;
}
}
v___jp_2564_:
{
if (lean_obj_tag(v_interestWaiter_2521_) == 1)
{
lean_object* v_val_2568_; uint8_t v___x_2569_; 
v_val_2568_ = lean_ctor_get(v_interestWaiter_2521_, 0);
lean_inc(v_val_2568_);
lean_dec_ref_known(v_interestWaiter_2521_, 1);
v___x_2569_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_2568_, v___x_2527_);
lean_dec(v_val_2568_);
v___y_2557_ = v_knownSize_2566_;
v___y_2558_ = v_leftover_2565_;
v___y_2559_ = v___y_2567_;
goto v___jp_2556_;
}
else
{
lean_dec(v_interestWaiter_2521_);
v___y_2557_ = v_knownSize_2566_;
v___y_2558_ = v_leftover_2565_;
v___y_2559_ = v___y_2567_;
goto v___jp_2556_;
}
}
v___jp_2570_:
{
uint8_t v___x_2574_; 
v___x_2574_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v___y_2571_, v___y_2573_);
lean_dec_ref(v___y_2571_);
v_leftover_2565_ = v___y_2572_;
v_knownSize_2566_ = v_knownSize_2522_;
v___y_2567_ = v_a_2515_;
goto v___jp_2564_;
}
v___jp_2575_:
{
if (lean_obj_tag(v_pendingConsumer_2520_) == 1)
{
if (lean_obj_tag(v___y_2576_) == 0)
{
if (lean_obj_tag(v_ending_2514_) == 0)
{
lean_object* v_val_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v_val_2577_ = lean_ctor_get(v_pendingConsumer_2520_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_pendingConsumer_2520_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v_pendingConsumer_2520_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_val_2577_);
lean_dec(v_pendingConsumer_2520_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___y_2576_);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___y_2576_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
v___y_2571_ = v_val_2577_;
v___y_2572_ = v___y_2576_;
v___y_2573_ = v___x_2582_;
goto v___jp_2570_;
}
}
}
else
{
lean_object* v_val_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2593_; 
v_val_2585_ = lean_ctor_get(v_pendingConsumer_2520_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_pendingConsumer_2520_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2587_ = v_pendingConsumer_2520_;
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_val_2585_);
lean_dec(v_pendingConsumer_2520_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v_err_2589_; lean_object* v___x_2591_; 
v_err_2589_ = lean_ctor_get(v_ending_2514_, 0);
lean_inc(v_err_2589_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 0);
lean_ctor_set(v___x_2587_, 0, v_err_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_err_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
v___y_2571_ = v_val_2585_;
v___y_2572_ = v___y_2576_;
v___y_2573_ = v___x_2591_;
goto v___jp_2570_;
}
}
}
}
else
{
lean_object* v_val_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2605_; 
v_val_2594_ = lean_ctor_get(v_pendingConsumer_2520_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_pendingConsumer_2520_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2596_ = v_pendingConsumer_2520_;
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_val_2594_);
lean_dec(v_pendingConsumer_2520_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v_val_2598_; lean_object* v___x_2600_; 
v_val_2598_ = lean_ctor_get(v___y_2576_, 0);
lean_inc_ref(v___y_2576_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___y_2576_);
v___x_2600_ = v___x_2596_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___y_2576_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
uint8_t v___x_2601_; 
v___x_2601_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_2594_, v___x_2600_);
lean_dec(v_val_2594_);
if (v___x_2601_ == 0)
{
v_leftover_2565_ = v___y_2576_;
v_knownSize_2566_ = v_knownSize_2522_;
v___y_2567_ = v_a_2515_;
goto v___jp_2564_;
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_inc(v_val_2598_);
lean_dec_ref_known(v___y_2576_, 1);
v___x_2602_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_2522_, v_val_2598_);
lean_dec(v_val_2598_);
v___x_2603_ = lean_box(0);
v_leftover_2565_ = v___x_2603_;
v_knownSize_2566_ = v___x_2602_;
v___y_2567_ = v_a_2515_;
goto v___jp_2564_;
}
}
}
}
}
else
{
lean_dec(v_pendingConsumer_2520_);
v_leftover_2565_ = v___y_2576_;
v_knownSize_2566_ = v_knownSize_2522_;
v___y_2567_ = v_a_2515_;
goto v___jp_2564_;
}
}
}
}
else
{
lean_object* v___x_2624_; 
lean_dec(v___x_2517_);
lean_dec(v_ending_2514_);
v___x_2624_ = lean_box(0);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1___boxed(lean_object* v_ending_2625_, lean_object* v_a_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1(v_ending_2625_, v_a_2626_);
lean_dec(v_a_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(lean_object* v_a_2629_){
_start:
{
lean_object* v___x_2631_; lean_object* v_pendingProducer_2632_; 
v___x_2631_ = lean_st_ref_get(v_a_2629_);
v_pendingProducer_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_pendingProducer_2632_);
if (lean_obj_tag(v_pendingProducer_2632_) == 1)
{
lean_object* v_val_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2666_; 
v_val_2633_ = lean_ctor_get(v_pendingProducer_2632_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_pendingProducer_2632_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2635_ = v_pendingProducer_2632_;
v_isShared_2636_ = v_isSharedCheck_2666_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_val_2633_);
lean_dec(v_pendingProducer_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2666_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v_pendingConsumer_2637_; lean_object* v_interestWaiter_2638_; lean_object* v_ended_2639_; lean_object* v_knownSize_2640_; lean_object* v_pendingIncomplete_2641_; uint8_t v_closeAfterProducer_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2664_; 
v_pendingConsumer_2637_ = lean_ctor_get(v___x_2631_, 1);
v_interestWaiter_2638_ = lean_ctor_get(v___x_2631_, 2);
v_ended_2639_ = lean_ctor_get(v___x_2631_, 3);
v_knownSize_2640_ = lean_ctor_get(v___x_2631_, 4);
v_pendingIncomplete_2641_ = lean_ctor_get(v___x_2631_, 5);
v_closeAfterProducer_2642_ = lean_ctor_get_uint8(v___x_2631_, sizeof(void*)*6);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2631_, 0);
lean_dec(v_unused_2665_);
v___x_2644_ = v___x_2631_;
v_isShared_2645_ = v_isSharedCheck_2664_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_pendingIncomplete_2641_);
lean_inc(v_knownSize_2640_);
lean_inc(v_ended_2639_);
lean_inc(v_interestWaiter_2638_);
lean_inc(v_pendingConsumer_2637_);
lean_dec(v___x_2631_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2664_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v_chunk_2646_; lean_object* v_done_2647_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2656_; 
v_chunk_2646_ = lean_ctor_get(v_val_2633_, 0);
lean_inc_ref(v_chunk_2646_);
v_done_2647_ = lean_ctor_get(v_val_2633_, 1);
lean_inc(v_done_2647_);
lean_dec(v_val_2633_);
v___x_2652_ = lean_box(0);
v___x_2653_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_2640_, v_chunk_2646_);
v___x_2654_ = 0;
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v___x_2653_);
lean_ctor_set(v___x_2644_, 0, v___x_2652_);
v___x_2656_ = v___x_2644_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_pendingConsumer_2637_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_interestWaiter_2638_);
lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_ended_2639_);
lean_ctor_set(v_reuseFailAlloc_2663_, 4, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2663_, 5, v_pendingIncomplete_2641_);
v___x_2656_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2655_;
}
v___jp_2648_:
{
lean_object* v___x_2650_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v_chunk_2646_);
v___x_2650_ = v___x_2635_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_chunk_2646_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; uint8_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_ctor_set_uint8(v___x_2656_, sizeof(void*)*6, v___x_2654_);
v___x_2657_ = lean_st_ref_swap(v_a_2629_, v___x_2656_);
lean_dec(v___x_2657_);
v___x_2658_ = 1;
v___x_2659_ = lean_box(v___x_2658_);
v___x_2660_ = lean_io_promise_resolve(v___x_2659_, v_done_2647_);
lean_dec(v_done_2647_);
if (v_closeAfterProducer_2642_ == 0)
{
goto v___jp_2648_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = lean_box(0);
v___x_2662_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1_spec__1(v___x_2661_, v_a_2629_);
goto v___jp_2648_;
}
}
}
}
}
else
{
lean_object* v___x_2667_; 
lean_dec(v_pendingProducer_2632_);
lean_dec(v___x_2631_);
v___x_2667_ = lean_box(0);
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(lean_object* v_a_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_2668_);
lean_dec(v_a_2668_);
return v_res_2670_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2));
v___x_2677_ = lean_task_pure(v___x_2676_);
return v___x_2677_;
}
}
static lean_object* _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
v___x_2679_ = lean_task_pure(v___x_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(lean_object* v___f_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_2681_);
v___x_2684_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_2681_);
if (lean_obj_tag(v___x_2684_) == 1)
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_dec_ref(v___f_2680_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
v___x_2686_ = lean_task_pure(v___x_2685_);
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; lean_object* v_ended_2688_; 
lean_dec(v___x_2684_);
v___x_2687_ = lean_st_ref_get(v___y_2681_);
v_ended_2688_ = lean_ctor_get(v___x_2687_, 3);
lean_inc(v_ended_2688_);
if (lean_obj_tag(v_ended_2688_) == 0)
{
lean_object* v_pendingConsumer_2689_; 
v_pendingConsumer_2689_ = lean_ctor_get(v___x_2687_, 1);
if (lean_obj_tag(v_pendingConsumer_2689_) == 0)
{
lean_object* v_pendingProducer_2690_; lean_object* v_interestWaiter_2691_; lean_object* v_knownSize_2692_; lean_object* v_pendingIncomplete_2693_; uint8_t v_closeAfterProducer_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2710_; 
v_pendingProducer_2690_ = lean_ctor_get(v___x_2687_, 0);
v_interestWaiter_2691_ = lean_ctor_get(v___x_2687_, 2);
v_knownSize_2692_ = lean_ctor_get(v___x_2687_, 4);
v_pendingIncomplete_2693_ = lean_ctor_get(v___x_2687_, 5);
v_closeAfterProducer_2694_ = lean_ctor_get_uint8(v___x_2687_, sizeof(void*)*6);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; lean_object* v_unused_2712_; 
v_unused_2711_ = lean_ctor_get(v___x_2687_, 3);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v___x_2687_, 1);
lean_dec(v_unused_2712_);
v___x_2696_ = v___x_2687_;
v_isShared_2697_ = v_isSharedCheck_2710_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_pendingIncomplete_2693_);
lean_inc(v_knownSize_2692_);
lean_inc(v_interestWaiter_2691_);
lean_inc(v_pendingProducer_2690_);
lean_dec(v___x_2687_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2710_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2698_ = 1;
v___x_2699_ = lean_io_promise_new();
lean_inc(v___x_2699_);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v___x_2701_);
v___x_2703_ = v___x_2696_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_pendingProducer_2690_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_interestWaiter_2691_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_ended_2688_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_knownSize_2692_);
lean_ctor_set(v_reuseFailAlloc_2709_, 5, v_pendingIncomplete_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, sizeof(void*)*6, v_closeAfterProducer_2694_);
v___x_2703_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2704_ = lean_st_ref_swap(v___y_2681_, v___x_2703_);
lean_dec(v___x_2704_);
v___x_2705_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_2681_);
v___x_2706_ = lean_io_promise_result_opt(v___x_2699_);
lean_dec(v___x_2699_);
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_task_map(v___f_2680_, v___x_2706_, v___x_2707_, v___x_2698_);
return v___x_2708_;
}
}
}
else
{
lean_object* v___x_2713_; 
lean_dec(v___x_2687_);
lean_dec_ref(v___f_2680_);
v___x_2713_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3);
return v___x_2713_;
}
}
else
{
lean_object* v_val_2714_; 
lean_dec(v___x_2687_);
lean_dec_ref(v___f_2680_);
v_val_2714_ = lean_ctor_get(v_ended_2688_, 0);
lean_inc(v_val_2714_);
lean_dec_ref_known(v_ended_2688_, 1);
if (lean_obj_tag(v_val_2714_) == 0)
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_obj_once(&l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4, &l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once, _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4);
return v___x_2715_;
}
else
{
lean_object* v_err_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
v_err_2716_ = lean_ctor_get(v_val_2714_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_val_2714_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v_val_2714_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_err_2716_);
lean_dec(v_val_2714_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 0);
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_err_2716_);
v___x_2721_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_task_pure(v___x_2721_);
return v___x_2722_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(lean_object* v___f_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(v___f_2725_, v___y_2726_);
lean_dec(v___y_2726_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(lean_object* v_stream_2732_){
_start:
{
lean_object* v___f_2734_; lean_object* v___x_2735_; 
v___f_2734_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1));
v___x_2735_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_2732_, v___f_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(lean_object* v_stream_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_2736_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0(lean_object* v_x_2739_){
_start:
{
if (lean_obj_tag(v_x_2739_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2749_; 
v_a_2741_ = lean_ctor_get(v_x_2739_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_x_2739_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2743_ = v_x_2739_;
v_isShared_2744_ = v_isSharedCheck_2749_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v_x_2739_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2749_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
return v___x_2747_;
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2751_; 
v_a_2750_ = lean_ctor_get(v_x_2739_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v_x_2739_, 1);
v___x_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2751_, 0, v_a_2750_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___lam__0___boxed(lean_object* v_x_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv(lean_object* v_stream_2756_){
_start:
{
lean_object* v___f_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___f_2758_ = ((lean_object*)(l_Std_Http_Body_Stream_recv___closed__0));
v___x_2759_ = lean_unsigned_to_nat(0u);
v___x_2760_ = 0;
v___x_2761_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_2756_);
v___x_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
v___x_2764_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2759_, v___x_2760_, v___x_2763_, v___f_2758_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recv___boxed(lean_object* v_stream_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Std_Http_Body_Stream_recv(v_stream_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___lam__0(lean_object* v___x_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___x_2768_, v___y_2769_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___lam__0___boxed(lean_object* v___x_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Std_Http_Body_Stream_close___lam__0(v___x_2772_, v___y_2773_);
lean_dec(v___y_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close(lean_object* v_stream_2778_){
_start:
{
lean_object* v___f_2780_; lean_object* v___x_2781_; 
v___f_2780_ = ((lean_object*)(l_Std_Http_Body_Stream_close___closed__0));
v___x_2781_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2778_, v___f_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_close___boxed(lean_object* v_stream_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Std_Http_Body_Stream_close(v_stream_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(uint8_t v___x_2785_, lean_object* v_x_2786_){
_start:
{
if (lean_obj_tag(v_x_2786_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2796_; 
v_a_2788_ = lean_ctor_get(v_x_2786_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_x_2786_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2790_ = v_x_2786_;
v_isShared_2791_ = v_isSharedCheck_2796_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v_x_2786_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2796_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
return v___x_2794_;
}
}
}
else
{
lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2805_; 
v_isSharedCheck_2805_ = !lean_is_exclusive(v_x_2786_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v_x_2786_, 0);
lean_dec(v_unused_2806_);
v___x_2798_ = v_x_2786_;
v_isShared_2799_ = v_isSharedCheck_2805_;
goto v_resetjp_2797_;
}
else
{
lean_dec(v_x_2786_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2805_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2800_ = lean_box(v___x_2785_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2800_);
v___x_2802_ = v___x_2798_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
return v___x_2803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__0___boxed(lean_object* v___x_2807_, lean_object* v_x_2808_, lean_object* v___y_2809_){
_start:
{
uint8_t v___x_1436__boxed_2810_; lean_object* v_res_2811_; 
v___x_1436__boxed_2810_ = lean_unbox(v___x_2807_);
v_res_2811_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__0(v___x_1436__boxed_2810_, v_x_2808_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(lean_object* v___y_2815_, lean_object* v_x_2816_){
_start:
{
uint8_t v___y_2819_; 
if (lean_obj_tag(v_x_2816_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2831_; 
v_a_2823_ = lean_ctor_get(v_x_2816_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_x_2816_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2825_ = v_x_2816_;
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v_x_2816_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
return v___x_2829_;
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v_ended_2833_; 
v_a_2832_ = lean_ctor_get(v_x_2816_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v_x_2816_, 1);
v_ended_2833_ = lean_ctor_get(v_a_2832_, 3);
if (lean_obj_tag(v_ended_2833_) == 0)
{
lean_object* v_pendingConsumer_2834_; 
v_pendingConsumer_2834_ = lean_ctor_get(v_a_2832_, 1);
lean_inc(v_pendingConsumer_2834_);
lean_dec(v_a_2832_);
if (lean_obj_tag(v_pendingConsumer_2834_) == 0)
{
lean_object* v___f_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___f_2835_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___closed__0));
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_unsigned_to_nat(0u);
v___x_2838_ = 0;
v___x_2839_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___x_2836_, v___y_2815_);
v___x_2840_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2837_, v___x_2838_, v___x_2839_, v___f_2835_);
return v___x_2840_;
}
else
{
uint8_t v___x_2841_; 
lean_dec_ref_known(v_pendingConsumer_2834_, 1);
v___x_2841_ = 0;
v___y_2819_ = v___x_2841_;
goto v___jp_2818_;
}
}
else
{
uint8_t v___x_2842_; 
lean_dec(v_a_2832_);
v___x_2842_ = 0;
v___y_2819_ = v___x_2842_;
goto v___jp_2818_;
}
}
v___jp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2820_ = lean_box(v___y_2819_);
v___x_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
return v___x_2822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed(lean_object* v___y_2843_, lean_object* v_x_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__1(v___y_2843_, v_x_2844_);
lean_dec(v___y_2843_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(lean_object* v___y_2847_, lean_object* v___f_2848_, lean_object* v_x_2849_){
_start:
{
if (lean_obj_tag(v_x_2849_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v___f_2848_);
v_a_2851_ = lean_ctor_get(v_x_2849_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_x_2849_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2853_ = v_x_2849_;
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v_x_2849_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
return v___x_2857_;
}
}
}
else
{
lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2871_; 
v_isSharedCheck_2871_ = !lean_is_exclusive(v_x_2849_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; 
v_unused_2872_ = lean_ctor_get(v_x_2849_, 0);
lean_dec(v_unused_2872_);
v___x_2861_ = v_x_2849_;
v_isShared_2862_ = v_isSharedCheck_2871_;
goto v_resetjp_2860_;
}
else
{
lean_dec(v_x_2849_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2871_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = 0;
v___x_2865_ = lean_st_ref_get(v___y_2847_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2865_);
v___x_2867_ = v___x_2861_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
v___x_2869_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2863_, v___x_2864_, v___x_2868_, v___f_2848_);
return v___x_2869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed(lean_object* v___y_2873_, lean_object* v___f_2874_, lean_object* v_x_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__2(v___y_2873_, v___f_2874_, v_x_2875_);
lean_dec(v___y_2873_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(lean_object* v___y_2878_){
_start:
{
lean_object* v___f_2880_; lean_object* v___f_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_inc_n(v___y_2878_, 2);
v___f_2880_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2880_, 0, v___y_2878_);
v___f_2881_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeIfAbandoned___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2881_, 0, v___y_2878_);
lean_closure_set(v___f_2881_, 1, v___f_2880_);
v___x_2882_ = lean_unsigned_to_nat(0u);
v___x_2883_ = 0;
v___x_2884_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_2878_);
v___x_2885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2882_, v___x_2883_, v___x_2884_, v___f_2881_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___lam__3___boxed(lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Std_Http_Body_Stream_closeIfAbandoned___lam__3(v___y_2886_);
lean_dec(v___y_2886_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned(lean_object* v_stream_2890_){
_start:
{
lean_object* v___f_2892_; lean_object* v___x_2893_; 
v___f_2892_ = ((lean_object*)(l_Std_Http_Body_Stream_closeIfAbandoned___closed__0));
v___x_2893_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2890_, v___f_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeIfAbandoned___boxed(lean_object* v_stream_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Std_Http_Body_Stream_closeIfAbandoned(v_stream_2894_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0(lean_object* v_err_2897_, lean_object* v___y_2898_, lean_object* v_x_2899_){
_start:
{
if (lean_obj_tag(v_x_2899_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_err_2897_);
v_a_2901_ = lean_ctor_get(v_x_2899_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_x_2899_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2903_ = v_x_2899_;
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v_x_2899_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2901_);
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
else
{
lean_object* v_a_2910_; uint8_t v_closeAfterProducer_2911_; 
v_a_2910_ = lean_ctor_get(v_x_2899_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v_x_2899_, 1);
v_closeAfterProducer_2911_ = lean_ctor_get_uint8(v_a_2910_, sizeof(void*)*6);
lean_dec(v_a_2910_);
if (v_closeAfterProducer_2911_ == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_err_2897_);
v___x_2913_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___x_2912_, v___y_2898_);
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; 
lean_dec(v_err_2897_);
v___x_2914_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_2914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__0___boxed(lean_object* v_err_2915_, lean_object* v___y_2916_, lean_object* v_x_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Std_Http_Body_Stream_closeWithError___lam__0(v_err_2915_, v___y_2916_, v_x_2917_);
lean_dec(v___y_2916_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1(lean_object* v_err_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___f_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_inc(v___y_2921_);
v___f_2923_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2923_, 0, v_err_2920_);
lean_closure_set(v___f_2923_, 1, v___y_2921_);
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = 0;
v___x_2926_ = lean_st_ref_get(v___y_2921_);
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
v___x_2929_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2924_, v___x_2925_, v___x_2928_, v___f_2923_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___lam__1___boxed(lean_object* v_err_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Std_Http_Body_Stream_closeWithError___lam__1(v_err_2930_, v___y_2931_);
lean_dec(v___y_2931_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError(lean_object* v_stream_2934_, lean_object* v_err_2935_){
_start:
{
lean_object* v___f_2937_; lean_object* v___x_2938_; 
v___f_2937_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_closeWithError___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2937_, 0, v_err_2935_);
v___x_2938_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_2934_, v___f_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_closeWithError___boxed(lean_object* v_stream_2939_, lean_object* v_err_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Std_Http_Body_Stream_closeWithError(v_stream_2939_, v_err_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0(lean_object* v_____do__lift_2943_, lean_object* v___y_2944_){
_start:
{
uint8_t v___y_2947_; lean_object* v_ended_2951_; 
v_ended_2951_ = lean_ctor_get(v_____do__lift_2943_, 3);
if (lean_obj_tag(v_ended_2951_) == 0)
{
uint8_t v___x_2952_; 
v___x_2952_ = 0;
v___y_2947_ = v___x_2952_;
goto v___jp_2946_;
}
else
{
uint8_t v___x_2953_; 
v___x_2953_ = 1;
v___y_2947_ = v___x_2953_;
goto v___jp_2946_;
}
v___jp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_box(v___y_2947_);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___lam__0___boxed(lean_object* v_____do__lift_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v_____do__lift_2954_);
return v_res_2957_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__1(void){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_2959_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__2(void){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_2960_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__6(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___f_2967_; lean_object* v___f_2968_; 
v___x_2966_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2967_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__5));
v___f_2968_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2968_, 0, v___f_2967_);
lean_closure_set(v___f_2968_, 1, v___x_2966_);
return v___f_2968_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__11(void){
_start:
{
lean_object* v___x_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; 
v___x_2977_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__2, &l_Std_Http_Body_Stream_isClosed___closed__2_once, _init_l_Std_Http_Body_Stream_isClosed___closed__2);
v___f_2978_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__10));
v___f_2979_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2979_, 0, v___f_2978_);
lean_closure_set(v___f_2979_, 1, v___x_2977_);
return v___f_2979_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__12(void){
_start:
{
lean_object* v___f_2980_; lean_object* v___x_2981_; 
v___f_2980_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__11, &l_Std_Http_Body_Stream_isClosed___closed__11_once, _init_l_Std_Http_Body_Stream_isClosed___closed__11);
v___x_2981_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2981_, 0, lean_box(0));
lean_closure_set(v___x_2981_, 1, lean_box(0));
lean_closure_set(v___x_2981_, 2, lean_box(0));
lean_closure_set(v___x_2981_, 3, v___f_2980_);
return v___x_2981_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_isClosed___closed__13(void){
_start:
{
lean_object* v___f_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___f_2982_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__0));
v___x_2983_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_2984_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_2985_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2985_, 0, lean_box(0));
lean_closure_set(v___x_2985_, 1, lean_box(0));
lean_closure_set(v___x_2985_, 2, v___x_2984_);
lean_closure_set(v___x_2985_, 3, lean_box(0));
lean_closure_set(v___x_2985_, 4, lean_box(0));
lean_closure_set(v___x_2985_, 5, v___x_2983_);
lean_closure_set(v___x_2985_, 6, v___f_2982_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed(lean_object* v_stream_2986_){
_start:
{
lean_object* v___x_2988_; lean_object* v___f_2989_; lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_220__overap_2992_; lean_object* v___x_2993_; 
v___x_2988_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_2989_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_2990_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_2991_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__13, &l_Std_Http_Body_Stream_isClosed___closed__13_once, _init_l_Std_Http_Body_Stream_isClosed___closed__13);
v___x_220__overap_2992_ = l_Std_Mutex_atomically___redArg(v___x_2988_, v___f_2989_, v___f_2990_, v_stream_2986_, v___x_2991_);
v___x_2993_ = lean_apply_1(v___x_220__overap_2992_, lean_box(0));
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_isClosed___boxed(lean_object* v_stream_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Std_Http_Body_Stream_isClosed(v_stream_2994_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0(lean_object* v_____do__lift_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_knownSize_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_knownSize_3000_ = lean_ctor_get(v_____do__lift_2997_, 4);
lean_inc(v_knownSize_3000_);
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_knownSize_3000_);
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(lean_object* v_____do__lift_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v_____do__lift_3003_);
return v_res_3006_;
}
}
static lean_object* _init_l_Std_Http_Body_Stream_getKnownSize___closed__1(void){
_start:
{
lean_object* v___f_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___f_3008_ = ((lean_object*)(l_Std_Http_Body_Stream_getKnownSize___closed__0));
v___x_3009_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__12, &l_Std_Http_Body_Stream_isClosed___closed__12_once, _init_l_Std_Http_Body_Stream_isClosed___closed__12);
v___x_3010_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___x_3011_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_3011_, 0, lean_box(0));
lean_closure_set(v___x_3011_, 1, lean_box(0));
lean_closure_set(v___x_3011_, 2, v___x_3010_);
lean_closure_set(v___x_3011_, 3, lean_box(0));
lean_closure_set(v___x_3011_, 4, lean_box(0));
lean_closure_set(v___x_3011_, 5, v___x_3009_);
lean_closure_set(v___x_3011_, 6, v___f_3008_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize(lean_object* v_stream_3012_){
_start:
{
lean_object* v___x_3014_; lean_object* v___f_3015_; lean_object* v___f_3016_; lean_object* v___x_3017_; lean_object* v___x_214__overap_3018_; lean_object* v___x_3019_; 
v___x_3014_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_3015_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_3016_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_3017_ = lean_obj_once(&l_Std_Http_Body_Stream_getKnownSize___closed__1, &l_Std_Http_Body_Stream_getKnownSize___closed__1_once, _init_l_Std_Http_Body_Stream_getKnownSize___closed__1);
v___x_214__overap_3018_ = l_Std_Mutex_atomically___redArg(v___x_3014_, v___f_3015_, v___f_3016_, v_stream_3012_, v___x_3017_);
v___x_3019_ = lean_apply_1(v___x_214__overap_3018_, lean_box(0));
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_getKnownSize___boxed(lean_object* v_stream_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0(lean_object* v_size_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___x_3026_; lean_object* v_pendingProducer_3027_; lean_object* v_pendingConsumer_3028_; lean_object* v_interestWaiter_3029_; lean_object* v_ended_3030_; lean_object* v_pendingIncomplete_3031_; uint8_t v_closeAfterProducer_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3041_; 
v___x_3026_ = lean_st_ref_take(v___y_3024_);
v_pendingProducer_3027_ = lean_ctor_get(v___x_3026_, 0);
v_pendingConsumer_3028_ = lean_ctor_get(v___x_3026_, 1);
v_interestWaiter_3029_ = lean_ctor_get(v___x_3026_, 2);
v_ended_3030_ = lean_ctor_get(v___x_3026_, 3);
v_pendingIncomplete_3031_ = lean_ctor_get(v___x_3026_, 5);
v_closeAfterProducer_3032_ = lean_ctor_get_uint8(v___x_3026_, sizeof(void*)*6);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v___x_3026_, 4);
lean_dec(v_unused_3042_);
v___x_3034_ = v___x_3026_;
v_isShared_3035_ = v_isSharedCheck_3041_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_pendingIncomplete_3031_);
lean_inc(v_ended_3030_);
lean_inc(v_interestWaiter_3029_);
lean_inc(v_pendingConsumer_3028_);
lean_inc(v_pendingProducer_3027_);
lean_dec(v___x_3026_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3041_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 4, v_size_3023_);
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_pendingProducer_3027_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_pendingConsumer_3028_);
lean_ctor_set(v_reuseFailAlloc_3040_, 2, v_interestWaiter_3029_);
lean_ctor_set(v_reuseFailAlloc_3040_, 3, v_ended_3030_);
lean_ctor_set(v_reuseFailAlloc_3040_, 4, v_size_3023_);
lean_ctor_set(v_reuseFailAlloc_3040_, 5, v_pendingIncomplete_3031_);
lean_ctor_set_uint8(v_reuseFailAlloc_3040_, sizeof(void*)*6, v_closeAfterProducer_3032_);
v___x_3037_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = lean_st_ref_put(v___y_3024_, v___x_3037_);
v___x_3039_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(lean_object* v_size_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_3043_, v___y_3044_);
lean_dec(v___y_3044_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize(lean_object* v_stream_3047_, lean_object* v_size_3048_){
_start:
{
lean_object* v___f_3050_; lean_object* v___x_3051_; lean_object* v___f_3052_; lean_object* v___f_3053_; lean_object* v___x_207__overap_3054_; lean_object* v___x_3055_; 
v___f_3050_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3050_, 0, v_size_3048_);
v___x_3051_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__1, &l_Std_Http_Body_Stream_isClosed___closed__1_once, _init_l_Std_Http_Body_Stream_isClosed___closed__1);
v___f_3052_ = lean_obj_once(&l_Std_Http_Body_Stream_isClosed___closed__6, &l_Std_Http_Body_Stream_isClosed___closed__6_once, _init_l_Std_Http_Body_Stream_isClosed___closed__6);
v___f_3053_ = ((lean_object*)(l_Std_Http_Body_Stream_isClosed___closed__7));
v___x_207__overap_3054_ = l_Std_Mutex_atomically___redArg(v___x_3051_, v___f_3052_, v___f_3053_, v_stream_3047_, v___f_3050_);
v___x_3055_ = lean_apply_1(v___x_207__overap_3054_, lean_box(0));
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_setKnownSize___boxed(lean_object* v_stream_3056_, lean_object* v_size_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_3056_, v_size_3057_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(lean_object* v_pendingProducer_3060_, lean_object* v_pendingConsumer_3061_, lean_object* v_ended_3062_, lean_object* v_knownSize_3063_, lean_object* v_pendingIncomplete_3064_, uint8_t v_closeAfterProducer_3065_, lean_object* v_a_3066_, lean_object* v___x_3067_, lean_object* v_x_3068_){
_start:
{
if (lean_obj_tag(v_x_3068_) == 0)
{
lean_object* v___x_3070_; 
lean_dec(v_pendingIncomplete_3064_);
lean_dec(v_knownSize_3063_);
lean_dec(v_ended_3062_);
lean_dec(v_pendingConsumer_3061_);
lean_dec(v_pendingProducer_3060_);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_x_3068_);
return v___x_3070_;
}
else
{
lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3081_; 
v_isSharedCheck_3081_ = !lean_is_exclusive(v_x_3068_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v_x_3068_, 0);
lean_dec(v_unused_3082_);
v___x_3072_ = v_x_3068_;
v_isShared_3073_ = v_isSharedCheck_3081_;
goto v_resetjp_3071_;
}
else
{
lean_dec(v_x_3068_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3081_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3075_, 0, v_pendingProducer_3060_);
lean_ctor_set(v___x_3075_, 1, v_pendingConsumer_3061_);
lean_ctor_set(v___x_3075_, 2, v___x_3074_);
lean_ctor_set(v___x_3075_, 3, v_ended_3062_);
lean_ctor_set(v___x_3075_, 4, v_knownSize_3063_);
lean_ctor_set(v___x_3075_, 5, v_pendingIncomplete_3064_);
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*6, v_closeAfterProducer_3065_);
v___x_3076_ = lean_st_ref_swap(v_a_3066_, v___x_3075_);
lean_dec(v___x_3076_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3067_);
v___x_3078_ = v___x_3072_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3067_);
v___x_3078_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3079_; 
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(lean_object* v_pendingProducer_3083_, lean_object* v_pendingConsumer_3084_, lean_object* v_ended_3085_, lean_object* v_knownSize_3086_, lean_object* v_pendingIncomplete_3087_, lean_object* v_closeAfterProducer_3088_, lean_object* v_a_3089_, lean_object* v___x_3090_, lean_object* v_x_3091_, lean_object* v___y_3092_){
_start:
{
uint8_t v_closeAfterProducer_boxed_3093_; lean_object* v_res_3094_; 
v_closeAfterProducer_boxed_3093_ = lean_unbox(v_closeAfterProducer_3088_);
v_res_3094_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_3083_, v_pendingConsumer_3084_, v_ended_3085_, v_knownSize_3086_, v_pendingIncomplete_3087_, v_closeAfterProducer_boxed_3093_, v_a_3089_, v___x_3090_, v_x_3091_);
lean_dec(v_a_3089_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(lean_object* v_a_3095_, lean_object* v_x_3096_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3106_; 
v_a_3098_ = lean_ctor_get(v_x_3096_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_x_3096_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3100_ = v_x_3096_;
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v_x_3096_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
return v___x_3104_;
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v_interestWaiter_3108_; 
v_a_3107_ = lean_ctor_get(v_x_3096_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v_x_3096_, 1);
v_interestWaiter_3108_ = lean_ctor_get(v_a_3107_, 2);
lean_inc(v_interestWaiter_3108_);
if (lean_obj_tag(v_interestWaiter_3108_) == 1)
{
lean_object* v_pendingProducer_3109_; lean_object* v_pendingConsumer_3110_; lean_object* v_ended_3111_; lean_object* v_knownSize_3112_; lean_object* v_pendingIncomplete_3113_; uint8_t v_closeAfterProducer_3114_; lean_object* v_val_3115_; uint8_t v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___f_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; uint8_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v_pendingProducer_3109_ = lean_ctor_get(v_a_3107_, 0);
lean_inc(v_pendingProducer_3109_);
v_pendingConsumer_3110_ = lean_ctor_get(v_a_3107_, 1);
lean_inc(v_pendingConsumer_3110_);
v_ended_3111_ = lean_ctor_get(v_a_3107_, 3);
lean_inc(v_ended_3111_);
v_knownSize_3112_ = lean_ctor_get(v_a_3107_, 4);
lean_inc(v_knownSize_3112_);
v_pendingIncomplete_3113_ = lean_ctor_get(v_a_3107_, 5);
lean_inc(v_pendingIncomplete_3113_);
v_closeAfterProducer_3114_ = lean_ctor_get_uint8(v_a_3107_, sizeof(void*)*6);
lean_dec(v_a_3107_);
v_val_3115_ = lean_ctor_get(v_interestWaiter_3108_, 0);
lean_inc(v_val_3115_);
lean_dec_ref_known(v_interestWaiter_3108_, 1);
v___x_3116_ = 1;
v___x_3117_ = lean_box(0);
v___x_3118_ = lean_box(v_closeAfterProducer_3114_);
lean_inc(v_a_3095_);
v___f_3119_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed), 10, 8);
lean_closure_set(v___f_3119_, 0, v_pendingProducer_3109_);
lean_closure_set(v___f_3119_, 1, v_pendingConsumer_3110_);
lean_closure_set(v___f_3119_, 2, v_ended_3111_);
lean_closure_set(v___f_3119_, 3, v_knownSize_3112_);
lean_closure_set(v___f_3119_, 4, v_pendingIncomplete_3113_);
lean_closure_set(v___f_3119_, 5, v___x_3118_);
lean_closure_set(v___f_3119_, 6, v_a_3095_);
lean_closure_set(v___f_3119_, 7, v___x_3117_);
v___x_3120_ = lean_unsigned_to_nat(0u);
v___x_3121_ = 0;
v___x_3122_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_3115_, v___x_3116_);
lean_dec(v_val_3115_);
v___x_3123_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3124_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3120_, v___x_3121_, v___x_3123_, v___f_3119_);
return v___x_3124_;
}
else
{
lean_object* v___x_3125_; 
lean_dec(v_interestWaiter_3108_);
lean_dec(v_a_3107_);
v___x_3125_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_3125_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(lean_object* v_a_3126_, lean_object* v_x_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_3126_, v_x_3127_);
lean_dec(v_a_3126_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(lean_object* v_a_3130_){
_start:
{
lean_object* v___f_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_inc(v_a_3130_);
v___f_3132_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3132_, 0, v_a_3130_);
v___x_3133_ = lean_unsigned_to_nat(0u);
v___x_3134_ = 0;
v___x_3135_ = lean_st_ref_get(v_a_3130_);
v___x_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
v___x_3138_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3133_, v___x_3134_, v___x_3137_, v___f_3132_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(lean_object* v_a_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_3139_);
lean_dec(v_a_3139_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(lean_object* v_promise_3142_, lean_object* v_x_3143_){
_start:
{
if (lean_obj_tag(v_x_3143_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3153_; 
v_a_3145_ = lean_ctor_get(v_x_3143_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_x_3143_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3147_ = v_x_3143_;
v_isShared_3148_ = v_isSharedCheck_3153_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v_x_3143_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3153_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; 
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
return v___x_3151_;
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3163_; 
v_a_3154_ = lean_ctor_get(v_x_3143_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_x_3143_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3156_ = v_x_3143_;
v_isShared_3157_ = v_isSharedCheck_3163_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v_x_3143_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3163_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3158_; lean_object* v___x_3160_; 
v___x_3158_ = lean_io_promise_resolve(v_a_3154_, v_promise_3142_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 0, v___x_3158_);
v___x_3160_ = v___x_3156_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3158_);
v___x_3160_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_3164_, lean_object* v_x_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(v_promise_3164_, v_x_3165_);
lean_dec(v_promise_3164_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(lean_object* v_lose_3168_, lean_object* v___y_3169_, lean_object* v___f_3170_, lean_object* v_x_3171_){
_start:
{
if (lean_obj_tag(v_x_3171_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3181_; 
lean_dec_ref(v___f_3170_);
lean_dec_ref(v_lose_3168_);
v_a_3173_ = lean_ctor_get(v_x_3171_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_x_3171_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3175_ = v_x_3171_;
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v_x_3171_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; 
v___x_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
return v___x_3179_;
}
}
}
else
{
lean_object* v_a_3182_; uint8_t v___x_3183_; 
v_a_3182_ = lean_ctor_get(v_x_3171_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v_x_3171_, 1);
v___x_3183_ = lean_unbox(v_a_3182_);
lean_dec(v_a_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; 
lean_dec_ref(v___f_3170_);
lean_inc(v___y_3169_);
v___x_3184_ = lean_apply_2(v_lose_3168_, v___y_3169_, lean_box(0));
return v___x_3184_;
}
else
{
lean_object* v___x_3185_; uint8_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_dec_ref(v_lose_3168_);
v___x_3185_ = lean_unsigned_to_nat(0u);
v___x_3186_ = 0;
v___x_3187_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_3169_);
v___x_3188_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3185_, v___x_3186_, v___x_3187_, v___f_3170_);
return v___x_3188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(lean_object* v_lose_3189_, lean_object* v___y_3190_, lean_object* v___f_3191_, lean_object* v_x_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(v_lose_3189_, v___y_3190_, v___f_3191_, v_x_3192_);
lean_dec(v___y_3190_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(lean_object* v_w_3195_, lean_object* v_lose_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_finished_3199_; lean_object* v_promise_3200_; lean_object* v___f_3201_; lean_object* v___f_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; lean_object* v___x_3205_; uint8_t v___y_3207_; uint8_t v___x_3215_; 
v_finished_3199_ = lean_ctor_get(v_w_3195_, 0);
lean_inc(v_finished_3199_);
v_promise_3200_ = lean_ctor_get(v_w_3195_, 1);
lean_inc(v_promise_3200_);
lean_dec_ref(v_w_3195_);
v___f_3201_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3201_, 0, v_promise_3200_);
lean_inc(v___y_3197_);
v___f_3202_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3202_, 0, v_lose_3196_);
lean_closure_set(v___f_3202_, 1, v___y_3197_);
lean_closure_set(v___f_3202_, 2, v___f_3201_);
v___x_3203_ = lean_unsigned_to_nat(0u);
v___x_3204_ = 0;
v___x_3205_ = lean_st_ref_take(v_finished_3199_);
v___x_3215_ = lean_unbox(v___x_3205_);
lean_dec(v___x_3205_);
if (v___x_3215_ == 0)
{
uint8_t v___x_3216_; 
v___x_3216_ = 1;
v___y_3207_ = v___x_3216_;
goto v___jp_3206_;
}
else
{
v___y_3207_ = v___x_3204_;
goto v___jp_3206_;
}
v___jp_3206_:
{
uint8_t v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3208_ = 1;
v___x_3209_ = lean_box(v___x_3208_);
v___x_3210_ = lean_st_ref_put(v_finished_3199_, v___x_3209_);
lean_dec(v_finished_3199_);
v___x_3211_ = lean_box(v___y_3207_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
v___x_3214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3203_, v___x_3204_, v___x_3213_, v___f_3202_);
return v___x_3214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(lean_object* v_w_3217_, lean_object* v_lose_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_w_3217_, v_lose_3218_, v___y_3219_);
lean_dec(v___y_3219_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1(lean_object* v___y_3222_, lean_object* v_x_3223_){
_start:
{
if (lean_obj_tag(v_x_3223_) == 0)
{
lean_object* v___x_3225_; 
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v_x_3223_);
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; 
lean_dec_ref_known(v_x_3223_, 1);
v___x_3226_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_3222_);
return v___x_3226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(lean_object* v___y_3227_, lean_object* v_x_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_3227_, v_x_3228_);
lean_dec(v___y_3227_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0(lean_object* v_waiter_3231_, lean_object* v_pendingProducer_3232_, lean_object* v_interestWaiter_3233_, lean_object* v_ended_3234_, lean_object* v_knownSize_3235_, lean_object* v_pendingIncomplete_3236_, uint8_t v_closeAfterProducer_3237_, uint8_t v_a_3238_, lean_object* v_____r_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___f_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_inc(v___y_3240_);
v___f_3242_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3242_, 0, v___y_3240_);
v___x_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3243_, 0, v_waiter_3231_);
v___x_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
v___x_3245_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3245_, 0, v_pendingProducer_3232_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
lean_ctor_set(v___x_3245_, 2, v_interestWaiter_3233_);
lean_ctor_set(v___x_3245_, 3, v_ended_3234_);
lean_ctor_set(v___x_3245_, 4, v_knownSize_3235_);
lean_ctor_set(v___x_3245_, 5, v_pendingIncomplete_3236_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*6, v_closeAfterProducer_3237_);
v___x_3246_ = lean_unsigned_to_nat(0u);
v___x_3247_ = lean_st_ref_swap(v___y_3240_, v___x_3245_);
lean_dec(v___x_3247_);
v___x_3248_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_3249_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3246_, v_a_3238_, v___x_3248_, v___f_3242_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(lean_object* v_waiter_3250_, lean_object* v_pendingProducer_3251_, lean_object* v_interestWaiter_3252_, lean_object* v_ended_3253_, lean_object* v_knownSize_3254_, lean_object* v_pendingIncomplete_3255_, lean_object* v_closeAfterProducer_3256_, lean_object* v_a_3257_, lean_object* v_____r_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v_closeAfterProducer_boxed_3261_; uint8_t v_a_5670__boxed_3262_; lean_object* v_res_3263_; 
v_closeAfterProducer_boxed_3261_ = lean_unbox(v_closeAfterProducer_3256_);
v_a_5670__boxed_3262_ = lean_unbox(v_a_3257_);
v_res_3263_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_3250_, v_pendingProducer_3251_, v_interestWaiter_3252_, v_ended_3253_, v_knownSize_3254_, v_pendingIncomplete_3255_, v_closeAfterProducer_boxed_3261_, v_a_5670__boxed_3262_, v_____r_3258_, v___y_3259_);
lean_dec(v___y_3259_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3(lean_object* v_waiter_3268_, uint8_t v_a_3269_, lean_object* v___y_3270_, lean_object* v_x_3271_){
_start:
{
if (lean_obj_tag(v_x_3271_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3281_; 
lean_dec_ref(v_waiter_3268_);
v_a_3273_ = lean_ctor_get(v_x_3271_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_x_3271_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3275_ = v_x_3271_;
v_isShared_3276_ = v_isSharedCheck_3281_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v_x_3271_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3281_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
return v___x_3279_;
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v_pendingProducer_3283_; lean_object* v_pendingConsumer_3284_; lean_object* v_interestWaiter_3285_; lean_object* v_ended_3286_; lean_object* v_knownSize_3287_; lean_object* v_pendingIncomplete_3288_; uint8_t v_closeAfterProducer_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___f_3292_; 
v_a_3282_ = lean_ctor_get(v_x_3271_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v_x_3271_, 1);
v_pendingProducer_3283_ = lean_ctor_get(v_a_3282_, 0);
lean_inc_n(v_pendingProducer_3283_, 2);
v_pendingConsumer_3284_ = lean_ctor_get(v_a_3282_, 1);
lean_inc(v_pendingConsumer_3284_);
v_interestWaiter_3285_ = lean_ctor_get(v_a_3282_, 2);
lean_inc_n(v_interestWaiter_3285_, 2);
v_ended_3286_ = lean_ctor_get(v_a_3282_, 3);
lean_inc_n(v_ended_3286_, 2);
v_knownSize_3287_ = lean_ctor_get(v_a_3282_, 4);
lean_inc_n(v_knownSize_3287_, 2);
v_pendingIncomplete_3288_ = lean_ctor_get(v_a_3282_, 5);
lean_inc_n(v_pendingIncomplete_3288_, 2);
v_closeAfterProducer_3289_ = lean_ctor_get_uint8(v_a_3282_, sizeof(void*)*6);
lean_dec(v_a_3282_);
v___x_3290_ = lean_box(v_closeAfterProducer_3289_);
v___x_3291_ = lean_box(v_a_3269_);
lean_inc_ref(v_waiter_3268_);
v___f_3292_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__0___boxed), 11, 8);
lean_closure_set(v___f_3292_, 0, v_waiter_3268_);
lean_closure_set(v___f_3292_, 1, v_pendingProducer_3283_);
lean_closure_set(v___f_3292_, 2, v_interestWaiter_3285_);
lean_closure_set(v___f_3292_, 3, v_ended_3286_);
lean_closure_set(v___f_3292_, 4, v_knownSize_3287_);
lean_closure_set(v___f_3292_, 5, v_pendingIncomplete_3288_);
lean_closure_set(v___f_3292_, 6, v___x_3290_);
lean_closure_set(v___f_3292_, 7, v___x_3291_);
if (lean_obj_tag(v_pendingConsumer_3284_) == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec_ref(v___f_3292_);
v___x_3293_ = lean_box(0);
v___x_3294_ = l_Std_Http_Body_Stream_recvSelector___lam__0(v_waiter_3268_, v_pendingProducer_3283_, v_interestWaiter_3285_, v_ended_3286_, v_knownSize_3287_, v_pendingIncomplete_3288_, v_closeAfterProducer_3289_, v_a_3269_, v___x_3293_, v___y_3270_);
return v___x_3294_;
}
else
{
lean_object* v___f_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec_ref_known(v_pendingConsumer_3284_, 1);
lean_dec(v_pendingIncomplete_3288_);
lean_dec(v_knownSize_3287_);
lean_dec(v_ended_3286_);
lean_dec(v_interestWaiter_3285_);
lean_dec(v_pendingProducer_3283_);
lean_dec_ref(v_waiter_3268_);
lean_inc(v___y_3270_);
v___f_3295_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3295_, 0, v___f_3292_);
lean_closure_set(v___f_3295_, 1, v___y_3270_);
v___x_3296_ = lean_unsigned_to_nat(0u);
v___x_3297_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1));
v___x_3298_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3296_, v_a_3269_, v___x_3297_, v___f_3295_);
return v___x_3298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(lean_object* v_waiter_3299_, lean_object* v_a_3300_, lean_object* v___y_3301_, lean_object* v_x_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v_a_5711__boxed_3304_; lean_object* v_res_3305_; 
v_a_5711__boxed_3304_ = lean_unbox(v_a_3300_);
v_res_3305_ = l_Std_Http_Body_Stream_recvSelector___lam__3(v_waiter_3299_, v_a_5711__boxed_3304_, v___y_3301_, v_x_3302_);
lean_dec(v___y_3301_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2(lean_object* v___x_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3306_);
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(lean_object* v___x_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_3311_, v___y_3312_);
lean_dec(v___y_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4(lean_object* v_waiter_3317_, lean_object* v___y_3318_, lean_object* v_x_3319_){
_start:
{
if (lean_obj_tag(v_x_3319_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3329_; 
lean_dec_ref(v_waiter_3317_);
v_a_3321_ = lean_ctor_get(v_x_3319_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_x_3319_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3323_ = v_x_3319_;
v_isShared_3324_ = v_isSharedCheck_3329_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v_x_3319_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3329_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3346_; 
v_a_3330_ = lean_ctor_get(v_x_3319_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_x_3319_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3332_ = v_x_3319_;
v_isShared_3333_ = v_isSharedCheck_3346_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v_x_3319_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3346_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
uint8_t v___x_3334_; 
v___x_3334_ = lean_unbox(v_a_3330_);
if (v___x_3334_ == 0)
{
lean_object* v___f_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
lean_inc(v___y_3318_);
lean_inc(v_a_3330_);
v___f_3335_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3335_, 0, v_waiter_3317_);
lean_closure_set(v___f_3335_, 1, v_a_3330_);
lean_closure_set(v___f_3335_, 2, v___y_3318_);
v___x_3336_ = lean_unsigned_to_nat(0u);
v___x_3337_ = lean_st_ref_get(v___y_3318_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3337_);
v___x_3339_ = v___x_3332_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
lean_object* v___x_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; 
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
v___x_3341_ = lean_unbox(v_a_3330_);
lean_dec(v_a_3330_);
v___x_3342_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3336_, v___x_3341_, v___x_3340_, v___f_3335_);
return v___x_3342_;
}
}
else
{
lean_object* v___f_3344_; lean_object* v___x_3345_; 
lean_del_object(v___x_3332_);
lean_dec(v_a_3330_);
v___f_3344_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_3345_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(v_waiter_3317_, v___f_3344_, v___y_3318_);
return v___x_3345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(lean_object* v_waiter_3347_, lean_object* v___y_3348_, lean_object* v_x_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Std_Http_Body_Stream_recvSelector___lam__4(v_waiter_3347_, v___y_3348_, v_x_3349_);
lean_dec(v___y_3348_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5(lean_object* v___y_3352_, lean_object* v___f_3353_, lean_object* v_x_3354_){
_start:
{
if (lean_obj_tag(v_x_3354_) == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref(v___f_3353_);
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_x_3354_);
return v___x_3356_;
}
else
{
lean_object* v___x_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec_ref_known(v_x_3354_, 1);
v___x_3357_ = lean_unsigned_to_nat(0u);
v___x_3358_ = 0;
v___x_3359_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_3352_);
v___x_3360_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3357_, v___x_3358_, v___x_3359_, v___f_3353_);
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(lean_object* v___y_3361_, lean_object* v___f_3362_, lean_object* v_x_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_3361_, v___f_3362_, v_x_3363_);
lean_dec(v___y_3361_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6(lean_object* v_waiter_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___f_3369_; lean_object* v___f_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_inc_n(v___y_3367_, 2);
v___f_3369_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3369_, 0, v_waiter_3366_);
lean_closure_set(v___f_3369_, 1, v___y_3367_);
v___f_3370_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_3370_, 0, v___y_3367_);
lean_closure_set(v___f_3370_, 1, v___f_3369_);
v___x_3371_ = lean_unsigned_to_nat(0u);
v___x_3372_ = 0;
v___x_3373_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_3367_);
v___x_3374_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3371_, v___x_3372_, v___x_3373_, v___f_3370_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(lean_object* v_waiter_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_3375_, v___y_3376_);
lean_dec(v___y_3376_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7(lean_object* v_stream_3379_, lean_object* v_waiter_3380_){
_start:
{
lean_object* v___f_3382_; lean_object* v___x_3383_; 
v___f_3382_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(v___f_3382_, 0, v_waiter_3380_);
v___x_3383_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_3379_, v___f_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(lean_object* v_stream_3384_, lean_object* v_waiter_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_3384_, v_waiter_3385_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_recvSelector(lean_object* v_stream_3389_){
_start:
{
lean_object* v___f_3390_; lean_object* v___f_3391_; lean_object* v___f_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___f_3390_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_3389_, 2);
v___f_3391_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_3391_, 0, v_stream_3389_);
v___f_3392_ = ((lean_object*)(l_Std_Http_Body_Stream_tryRecvBody___closed__1));
v___x_3393_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_3393_, 0, lean_box(0));
lean_closure_set(v___x_3393_, 1, lean_box(0));
lean_closure_set(v___x_3393_, 2, v_stream_3389_);
lean_closure_set(v___x_3393_, 3, v___f_3392_);
v___x_3394_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_3394_, 0, lean_box(0));
lean_closure_set(v___x_3394_, 1, lean_box(0));
lean_closure_set(v___x_3394_, 2, v_stream_3389_);
lean_closure_set(v___x_3394_, 3, v___f_3390_);
v___x_3395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___f_3391_);
lean_ctor_set(v___x_3395_, 2, v___x_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0(lean_object* v_step_3396_, lean_object* v_acc_3397_, lean_object* v_x_3398_){
_start:
{
if (lean_obj_tag(v_x_3398_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v_acc_3397_);
lean_dec_ref(v_step_3396_);
v_a_3400_ = lean_ctor_get(v_x_3398_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_x_3398_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3402_ = v_x_3398_;
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v_x_3398_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
return v___x_3406_;
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3420_; 
v_a_3409_ = lean_ctor_get(v_x_3398_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_x_3398_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3411_ = v_x_3398_;
v_isShared_3412_ = v_isSharedCheck_3420_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v_x_3398_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3420_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
if (lean_obj_tag(v_a_3409_) == 1)
{
lean_object* v_val_3413_; lean_object* v___x_3414_; 
lean_del_object(v___x_3411_);
v_val_3413_ = lean_ctor_get(v_a_3409_, 0);
lean_inc(v_val_3413_);
lean_dec_ref_known(v_a_3409_, 1);
v___x_3414_ = lean_apply_3(v_step_3396_, v_val_3413_, v_acc_3397_, lean_box(0));
return v___x_3414_;
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
lean_dec(v_a_3409_);
lean_dec_ref(v_step_3396_);
v___x_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3415_, 0, v_acc_3397_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3415_);
v___x_3417_ = v___x_3411_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
return v___x_3418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed(lean_object* v_step_3421_, lean_object* v_acc_3422_, lean_object* v_x_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Std_Http_Body_Stream_forIn___redArg___lam__0(v_step_3421_, v_acc_3422_, v_x_3423_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1(lean_object* v_step_3426_, lean_object* v_stream_3427_, lean_object* v_x_3428_, lean_object* v_acc_3429_){
_start:
{
lean_object* v___f_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___f_3431_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3431_, 0, v_step_3426_);
lean_closure_set(v___f_3431_, 1, v_acc_3429_);
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = 0;
v___x_3434_ = l_Std_Http_Body_Stream_recv(v_stream_3427_);
v___x_3435_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3432_, v___x_3433_, v___x_3434_, v___f_3431_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed(lean_object* v_step_3436_, lean_object* v_stream_3437_, lean_object* v_x_3438_, lean_object* v_acc_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Std_Http_Body_Stream_forIn___redArg___lam__1(v_step_3436_, v_stream_3437_, v_x_3438_, v_acc_3439_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2(lean_object* v_a_3442_, lean_object* v_x_3443_){
_start:
{
if (lean_obj_tag(v_x_3443_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3453_; 
v_a_3445_ = lean_ctor_get(v_x_3443_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_x_3443_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3447_ = v_x_3443_;
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v_x_3443_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec_ref_known(v_x_3443_, 1);
v___x_3454_ = l_IO_Promise_result_x21___redArg(v_a_3442_);
v___x_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
return v___x_3455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed(lean_object* v_a_3456_, lean_object* v_x_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Std_Http_Body_Stream_forIn___redArg___lam__2(v_a_3456_, v_x_3457_);
lean_dec(v_a_3456_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3(lean_object* v___f_3460_, lean_object* v___x_3461_, lean_object* v_acc_3462_, lean_object* v_x_3463_){
_start:
{
if (lean_obj_tag(v_x_3463_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3473_; 
lean_dec(v_acc_3462_);
lean_dec(v___x_3461_);
lean_dec_ref(v___f_3460_);
v_a_3465_ = lean_ctor_get(v_x_3463_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_x_3463_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3467_ = v_x_3463_;
v_isShared_3468_ = v_isSharedCheck_3473_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v_x_3463_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3473_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3486_; 
v_a_3474_ = lean_ctor_get(v_x_3463_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_x_3463_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3476_ = v_x_3463_;
v_isShared_3477_ = v_isSharedCheck_3486_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v_x_3463_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3486_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___f_3478_; uint8_t v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
lean_inc(v_a_3474_);
v___f_3478_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3478_, 0, v_a_3474_);
v___x_3479_ = 0;
lean_inc(v___x_3461_);
v___x_3480_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_3460_, v___x_3461_, v_a_3474_, v_acc_3462_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3480_);
v___x_3482_ = v___x_3476_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
v___x_3484_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3461_, v___x_3479_, v___x_3483_, v___f_3478_);
return v___x_3484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed(lean_object* v___f_3487_, lean_object* v___x_3488_, lean_object* v_acc_3489_, lean_object* v_x_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Std_Http_Body_Stream_forIn___redArg___lam__3(v___f_3487_, v___x_3488_, v_acc_3489_, v_x_3490_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg(lean_object* v_stream_3493_, lean_object* v_acc_3494_, lean_object* v_step_3495_){
_start:
{
lean_object* v___f_3497_; lean_object* v___x_3498_; lean_object* v___f_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___f_3497_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3497_, 0, v_step_3495_);
lean_closure_set(v___f_3497_, 1, v_stream_3493_);
v___x_3498_ = lean_unsigned_to_nat(0u);
v___f_3499_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3499_, 0, v___f_3497_);
lean_closure_set(v___f_3499_, 1, v___x_3498_);
lean_closure_set(v___f_3499_, 2, v_acc_3494_);
v___x_3500_ = 0;
v___x_3501_ = lean_io_promise_new();
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
v___x_3504_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3498_, v___x_3500_, v___x_3503_, v___f_3499_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___redArg___boxed(lean_object* v_stream_3505_, lean_object* v_acc_3506_, lean_object* v_step_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_3505_, v_acc_3506_, v_step_3507_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn(lean_object* v_00_u03b2_3510_, lean_object* v_stream_3511_, lean_object* v_acc_3512_, lean_object* v_step_3513_){
_start:
{
lean_object* v___f_3515_; lean_object* v___x_3516_; lean_object* v___f_3517_; uint8_t v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___f_3515_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3515_, 0, v_step_3513_);
lean_closure_set(v___f_3515_, 1, v_stream_3511_);
v___x_3516_ = lean_unsigned_to_nat(0u);
v___f_3517_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3517_, 0, v___f_3515_);
lean_closure_set(v___f_3517_, 1, v___x_3516_);
lean_closure_set(v___f_3517_, 2, v_acc_3512_);
v___x_3518_ = 0;
v___x_3519_ = lean_io_promise_new();
v___x_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
v___x_3522_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3516_, v___x_3518_, v___x_3521_, v___f_3517_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn___boxed(lean_object* v_00_u03b2_3523_, lean_object* v_stream_3524_, lean_object* v_acc_3525_, lean_object* v_step_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Std_Http_Body_Stream_forIn(v_00_u03b2_3523_, v_stream_3524_, v_acc_3525_, v_step_3526_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3531_, 0, v___y_3529_);
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0___boxed(lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__0(v___y_3533_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(lean_object* v_x_3536_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0___lam__4___closed__0));
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1___boxed(lean_object* v_x_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__1(v_x_3539_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(lean_object* v_x_3542_){
_start:
{
if (lean_obj_tag(v_x_3542_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3552_; 
v_a_3544_ = lean_ctor_get(v_x_3542_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_x_3542_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3546_ = v_x_3542_;
v_isShared_3547_ = v_isSharedCheck_3552_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v_x_3542_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3552_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3563_; 
v_a_3553_ = lean_ctor_get(v_x_3542_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_x_3542_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3555_ = v_x_3542_;
v_isShared_3556_ = v_isSharedCheck_3563_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v_x_3542_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3563_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_token_3557_; lean_object* v___x_3558_; lean_object* v___x_3560_; 
v_token_3557_ = lean_ctor_get(v_a_3553_, 1);
lean_inc_ref(v_token_3557_);
lean_dec(v_a_3553_);
v___x_3558_ = l_Std_CancellationToken_selector(v_token_3557_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3558_);
v___x_3560_ = v___x_3555_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3558_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2___boxed(lean_object* v_x_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__2(v_x_3564_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(lean_object* v_step_3567_, lean_object* v_b_3568_, lean_object* v_a_3569_, lean_object* v_x_3570_){
_start:
{
if (lean_obj_tag(v_x_3570_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3580_; 
lean_dec(v_b_3568_);
lean_dec_ref(v_step_3567_);
v_a_3572_ = lean_ctor_get(v_x_3570_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_x_3570_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3574_ = v_x_3570_;
v_isShared_3575_ = v_isSharedCheck_3580_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v_x_3570_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3580_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3578_; 
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3592_; 
v_a_3581_ = lean_ctor_get(v_x_3570_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_x_3570_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3583_ = v_x_3570_;
v_isShared_3584_ = v_isSharedCheck_3592_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v_x_3570_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3592_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
if (lean_obj_tag(v_a_3581_) == 1)
{
lean_object* v_val_3585_; lean_object* v___x_3586_; 
lean_del_object(v___x_3583_);
v_val_3585_ = lean_ctor_get(v_a_3581_, 0);
lean_inc(v_val_3585_);
lean_dec_ref_known(v_a_3581_, 1);
lean_inc_ref(v_a_3569_);
v___x_3586_ = lean_apply_4(v_step_3567_, v_val_3585_, v_b_3568_, v_a_3569_, lean_box(0));
return v___x_3586_;
}
else
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
lean_dec(v_a_3581_);
lean_dec_ref(v_step_3567_);
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v_b_3568_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3587_);
v___x_3589_ = v___x_3583_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed(lean_object* v_step_3593_, lean_object* v_b_3594_, lean_object* v_a_3595_, lean_object* v_x_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3(v_step_3593_, v_b_3594_, v_a_3595_, v_x_3596_);
lean_dec_ref(v_a_3595_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(lean_object* v_stream_3599_, lean_object* v___f_3600_, lean_object* v___f_3601_, lean_object* v___f_3602_, lean_object* v_x_3603_){
_start:
{
if (lean_obj_tag(v_x_3603_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3613_; 
lean_dec_ref(v___f_3602_);
lean_dec_ref(v___f_3601_);
lean_dec_ref(v___f_3600_);
lean_dec_ref(v_stream_3599_);
v_a_3605_ = lean_ctor_get(v_x_3603_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_x_3603_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3607_ = v_x_3603_;
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v_x_3603_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
return v___x_3611_;
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; uint8_t v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v_a_3614_ = lean_ctor_get(v_x_3603_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v_x_3603_, 1);
v___x_3615_ = l_Std_Http_Body_Stream_recvSelector(v_stream_3599_);
v___x_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set(v___x_3616_, 1, v___f_3600_);
v___x_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3617_, 0, v_a_3614_);
lean_ctor_set(v___x_3617_, 1, v___f_3601_);
v___x_3618_ = lean_unsigned_to_nat(2u);
v___x_3619_ = lean_mk_empty_array_with_capacity(v___x_3618_);
v___x_3620_ = lean_array_push(v___x_3619_, v___x_3616_);
v___x_3621_ = lean_array_push(v___x_3620_, v___x_3617_);
v___x_3622_ = lean_unsigned_to_nat(0u);
v___x_3623_ = 0;
v___x_3624_ = l_Std_Async_Selectable_one___redArg(v___x_3621_);
v___x_3625_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3622_, v___x_3623_, v___x_3624_, v___f_3602_);
return v___x_3625_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed(lean_object* v_stream_3626_, lean_object* v___f_3627_, lean_object* v___f_3628_, lean_object* v___f_3629_, lean_object* v_x_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4(v_stream_3626_, v___f_3627_, v___f_3628_, v___f_3629_, v_x_3630_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(lean_object* v_step_3633_, lean_object* v_a_3634_, lean_object* v_stream_3635_, lean_object* v___f_3636_, lean_object* v___f_3637_, lean_object* v___f_3638_, lean_object* v_u_3639_, lean_object* v_b_3640_){
_start:
{
lean_object* v___f_3642_; lean_object* v___f_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_inc_ref_n(v_a_3634_, 2);
v___f_3642_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3642_, 0, v_step_3633_);
lean_closure_set(v___f_3642_, 1, v_b_3640_);
lean_closure_set(v___f_3642_, 2, v_a_3634_);
v___f_3643_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3643_, 0, v_stream_3635_);
lean_closure_set(v___f_3643_, 1, v___f_3636_);
lean_closure_set(v___f_3643_, 2, v___f_3637_);
lean_closure_set(v___f_3643_, 3, v___f_3642_);
v___x_3644_ = lean_unsigned_to_nat(0u);
v___x_3645_ = 0;
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v_a_3634_);
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
v___x_3648_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3644_, v___x_3645_, v___x_3647_, v___f_3638_);
v___x_3649_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3644_, v___x_3645_, v___x_3648_, v___f_3643_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed(lean_object* v_step_3650_, lean_object* v_a_3651_, lean_object* v_stream_3652_, lean_object* v___f_3653_, lean_object* v___f_3654_, lean_object* v___f_3655_, lean_object* v_u_3656_, lean_object* v_b_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5(v_step_3650_, v_a_3651_, v_stream_3652_, v___f_3653_, v___f_3654_, v___f_3655_, v_u_3656_, v_b_3657_);
lean_dec_ref(v_a_3651_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg(lean_object* v_stream_3663_, lean_object* v_acc_3664_, lean_object* v_step_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v___f_3668_; lean_object* v___f_3669_; lean_object* v___f_3670_; lean_object* v___f_3671_; lean_object* v___x_3672_; lean_object* v___f_3673_; uint8_t v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___f_3668_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_3669_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_3670_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_3666_);
v___f_3671_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_3671_, 0, v_step_3665_);
lean_closure_set(v___f_3671_, 1, v_a_3666_);
lean_closure_set(v___f_3671_, 2, v_stream_3663_);
lean_closure_set(v___f_3671_, 3, v___f_3668_);
lean_closure_set(v___f_3671_, 4, v___f_3669_);
lean_closure_set(v___f_3671_, 5, v___f_3670_);
v___x_3672_ = lean_unsigned_to_nat(0u);
v___f_3673_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3673_, 0, v___f_3671_);
lean_closure_set(v___f_3673_, 1, v___x_3672_);
lean_closure_set(v___f_3673_, 2, v_acc_3664_);
v___x_3674_ = 0;
v___x_3675_ = lean_io_promise_new();
v___x_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
v___x_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
v___x_3678_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3672_, v___x_3674_, v___x_3677_, v___f_3673_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(lean_object* v_stream_3679_, lean_object* v_acc_3680_, lean_object* v_step_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Std_Http_Body_Stream_forIn_x27___redArg(v_stream_3679_, v_acc_3680_, v_step_3681_, v_a_3682_);
lean_dec_ref(v_a_3682_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27(lean_object* v_00_u03b2_3685_, lean_object* v_stream_3686_, lean_object* v_acc_3687_, lean_object* v_step_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v___f_3691_; lean_object* v___f_3692_; lean_object* v___f_3693_; lean_object* v___f_3694_; lean_object* v___x_3695_; lean_object* v___f_3696_; uint8_t v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___f_3691_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__0));
v___f_3692_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__1));
v___f_3693_ = ((lean_object*)(l_Std_Http_Body_Stream_forIn_x27___redArg___closed__2));
lean_inc_ref(v_a_3689_);
v___f_3694_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn_x27___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_3694_, 0, v_step_3688_);
lean_closure_set(v___f_3694_, 1, v_a_3689_);
lean_closure_set(v___f_3694_, 2, v_stream_3686_);
lean_closure_set(v___f_3694_, 3, v___f_3691_);
lean_closure_set(v___f_3694_, 4, v___f_3692_);
lean_closure_set(v___f_3694_, 5, v___f_3693_);
v___x_3695_ = lean_unsigned_to_nat(0u);
v___f_3696_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_forIn___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3696_, 0, v___f_3694_);
lean_closure_set(v___f_3696_, 1, v___x_3695_);
lean_closure_set(v___f_3696_, 2, v_acc_3687_);
v___x_3697_ = 0;
v___x_3698_ = lean_io_promise_new();
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
v___x_3701_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3695_, v___x_3697_, v___x_3700_, v___f_3696_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_forIn_x27___boxed(lean_object* v_00_u03b2_3702_, lean_object* v_stream_3703_, lean_object* v_acc_3704_, lean_object* v_step_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Std_Http_Body_Stream_forIn_x27(v_00_u03b2_3702_, v_stream_3703_, v_acc_3704_, v_step_3705_, v_a_3706_);
lean_dec_ref(v_a_3706_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(lean_object* v_x_3718_){
_start:
{
if (lean_obj_tag(v_x_3718_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3728_; 
v_a_3720_ = lean_ctor_get(v_x_3718_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_x_3718_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3722_ = v_x_3718_;
v_isShared_3723_ = v_isSharedCheck_3728_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v_x_3718_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3728_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
return v___x_3726_;
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3745_; 
v_a_3729_ = lean_ctor_get(v_x_3718_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_x_3718_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3731_ = v_x_3718_;
v_isShared_3732_ = v_isSharedCheck_3745_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v_x_3718_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3745_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
if (lean_obj_tag(v_a_3729_) == 1)
{
lean_object* v_val_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3743_; 
v_val_3733_ = lean_ctor_get(v_a_3729_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_a_3729_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3735_ = v_a_3729_;
v_isShared_3736_ = v_isSharedCheck_3743_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_val_3733_);
lean_dec(v_a_3729_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3743_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 0, v_val_3733_);
v___x_3738_ = v___x_3731_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_val_3733_);
v___x_3738_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
lean_object* v___x_3740_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set_tag(v___x_3735_, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3738_);
v___x_3740_ = v___x_3735_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_object* v___x_3744_; 
lean_del_object(v___x_3731_);
lean_dec(v_a_3729_);
v___x_3744_ = ((lean_object*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___closed__3));
return v___x_3744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed(lean_object* v_x_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(v_x_3746_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(lean_object* v_stream_3749_, lean_object* v___f_3750_, lean_object* v_x_3751_){
_start:
{
lean_object* v___x_3753_; uint8_t v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = 0;
v___x_3755_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_3749_);
v___x_3756_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3753_, v___x_3754_, v___x_3755_, v___f_3750_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed(lean_object* v_stream_3757_, lean_object* v___f_3758_, lean_object* v_x_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(v_stream_3757_, v___f_3758_, v_x_3759_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(lean_object* v_stream_3762_, lean_object* v___f_3763_, lean_object* v___f_3764_, lean_object* v_x_3765_){
_start:
{
if (lean_obj_tag(v_x_3765_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v___f_3764_);
lean_dec_ref(v___f_3763_);
lean_dec_ref(v_stream_3762_);
v_a_3767_ = lean_ctor_get(v_x_3765_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_x_3765_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3769_ = v_x_3765_;
v_isShared_3770_ = v_isSharedCheck_3775_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v_x_3765_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3775_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
return v___x_3773_;
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_a_3776_ = lean_ctor_get(v_x_3765_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v_x_3765_, 1);
v___x_3777_ = l_Std_Http_Body_Stream_recvSelector(v_stream_3762_);
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
lean_ctor_set(v___x_3778_, 1, v___f_3763_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v_a_3776_);
lean_ctor_set(v___x_3779_, 1, v___f_3764_);
v___x_3780_ = lean_unsigned_to_nat(2u);
v___x_3781_ = lean_mk_empty_array_with_capacity(v___x_3780_);
v___x_3782_ = lean_array_push(v___x_3781_, v___x_3778_);
v___x_3783_ = lean_array_push(v___x_3782_, v___x_3779_);
v___x_3784_ = l_Std_Async_Selectable_one___redArg(v___x_3783_);
return v___x_3784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(lean_object* v_stream_3785_, lean_object* v___f_3786_, lean_object* v___f_3787_, lean_object* v_x_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v_stream_3785_, v___f_3786_, v___f_3787_, v_x_3788_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(lean_object* v___f_3791_, lean_object* v___f_3792_, lean_object* v___f_3793_, lean_object* v_stream_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___f_3797_; lean_object* v___f_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
lean_inc_ref(v_stream_3794_);
v___f_3797_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3797_, 0, v_stream_3794_);
lean_closure_set(v___f_3797_, 1, v___f_3791_);
v___f_3798_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3798_, 0, v_stream_3794_);
lean_closure_set(v___f_3798_, 1, v___f_3792_);
lean_closure_set(v___f_3798_, 2, v___f_3797_);
v___x_3799_ = lean_unsigned_to_nat(0u);
v___x_3800_ = 0;
lean_inc_ref(v___y_3795_);
v___x_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3801_, 0, v___y_3795_);
v___x_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
v___x_3803_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3799_, v___x_3800_, v___x_3802_, v___f_3793_);
v___x_3804_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3799_, v___x_3800_, v___x_3803_, v___f_3798_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(lean_object* v___f_3805_, lean_object* v___f_3806_, lean_object* v___f_3807_, lean_object* v_stream_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(v___f_3805_, v___f_3806_, v___f_3807_, v_stream_3808_, v___y_3809_);
lean_dec_ref(v___y_3809_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(lean_object* v___f_3818_, lean_object* v_____r_3819_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_apply_1(v___f_3818_, v_____r_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2(lean_object* v_inst_3823_, uint64_t v_val_3824_, lean_object* v_toBind_3825_, lean_object* v___f_3826_, lean_object* v_____r_3827_){
_start:
{
lean_object* v_throw_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v_throw_3828_ = lean_ctor_get(v_inst_3823_, 0);
lean_inc(v_throw_3828_);
lean_dec_ref(v_inst_3823_);
v___x_3829_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__0));
v___x_3830_ = lean_uint64_to_nat(v_val_3824_);
v___x_3831_ = l_Nat_reprFast(v___x_3830_);
v___x_3832_ = lean_string_append(v___x_3829_, v___x_3831_);
lean_dec_ref(v___x_3831_);
v___x_3833_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___closed__1));
v___x_3834_ = lean_string_append(v___x_3832_, v___x_3833_);
v___x_3835_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
v___x_3836_ = lean_apply_2(v_throw_3828_, lean_box(0), v___x_3835_);
v___x_3837_ = lean_apply_4(v_toBind_3825_, lean_box(0), lean_box(0), v___x_3836_, v___f_3826_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___boxed(lean_object* v_inst_3838_, lean_object* v_val_3839_, lean_object* v_toBind_3840_, lean_object* v___f_3841_, lean_object* v_____r_3842_){
_start:
{
uint64_t v_val_253__boxed_3843_; lean_object* v_res_3844_; 
v_val_253__boxed_3843_ = lean_unbox_uint64(v_val_3839_);
lean_dec_ref(v_val_3839_);
v_res_3844_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2(v_inst_3838_, v_val_253__boxed_3843_, v_toBind_3840_, v___f_3841_, v_____r_3842_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3(lean_object* v_pieces_3845_, lean_object* v_size_3846_, lean_object* v_toPure_3847_, lean_object* v_inst_3848_, lean_object* v_inst_3849_, lean_object* v_inst_3850_, lean_object* v_inst_3851_, lean_object* v_stream_3852_, lean_object* v_maximumSize_3853_, lean_object* v_toBind_3854_, lean_object* v_____do__lift_3855_){
_start:
{
if (lean_obj_tag(v_____do__lift_3855_) == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_dec(v_toBind_3854_);
lean_dec(v_maximumSize_3853_);
lean_dec_ref(v_stream_3852_);
lean_dec(v_inst_3851_);
lean_dec(v_inst_3850_);
lean_dec_ref(v_inst_3849_);
lean_dec_ref(v_inst_3848_);
v___x_3856_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_joinPieces(v_pieces_3845_, v_size_3846_);
v___x_3857_ = lean_apply_2(v_toPure_3847_, lean_box(0), v___x_3856_);
return v___x_3857_;
}
else
{
lean_object* v_val_3858_; lean_object* v_data_3859_; lean_object* v___x_3860_; lean_object* v_size_3861_; lean_object* v___f_3862_; 
lean_dec(v_toPure_3847_);
v_val_3858_ = lean_ctor_get(v_____do__lift_3855_, 0);
lean_inc(v_val_3858_);
lean_dec_ref_known(v_____do__lift_3855_, 1);
v_data_3859_ = lean_ctor_get(v_val_3858_, 0);
lean_inc_ref_n(v_data_3859_, 2);
lean_dec(v_val_3858_);
v___x_3860_ = lean_byte_array_size(v_data_3859_);
v_size_3861_ = lean_nat_add(v_size_3846_, v___x_3860_);
lean_inc(v_size_3861_);
lean_inc(v_maximumSize_3853_);
lean_inc_ref(v_stream_3852_);
lean_inc(v_inst_3851_);
lean_inc(v_inst_3850_);
lean_inc_ref(v_inst_3849_);
lean_inc_ref(v_inst_3848_);
lean_inc(v_pieces_3845_);
v___f_3862_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0), 10, 9);
lean_closure_set(v___f_3862_, 0, v_data_3859_);
lean_closure_set(v___f_3862_, 1, v_pieces_3845_);
lean_closure_set(v___f_3862_, 2, v_inst_3848_);
lean_closure_set(v___f_3862_, 3, v_inst_3849_);
lean_closure_set(v___f_3862_, 4, v_inst_3850_);
lean_closure_set(v___f_3862_, 5, v_inst_3851_);
lean_closure_set(v___f_3862_, 6, v_stream_3852_);
lean_closure_set(v___f_3862_, 7, v_maximumSize_3853_);
lean_closure_set(v___f_3862_, 8, v_size_3861_);
if (lean_obj_tag(v_maximumSize_3853_) == 1)
{
lean_object* v_val_3863_; uint64_t v___x_3864_; uint64_t v___x_3865_; uint8_t v___x_3866_; 
v_val_3863_ = lean_ctor_get(v_maximumSize_3853_, 0);
v___x_3864_ = lean_uint64_of_nat(v_size_3861_);
v___x_3865_ = lean_unbox_uint64(v_val_3863_);
v___x_3866_ = lean_uint64_dec_lt(v___x_3865_, v___x_3864_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
lean_dec_ref(v___f_3862_);
lean_dec(v_toBind_3854_);
v___x_3867_ = lean_box(0);
v___x_3868_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(v_data_3859_, v_pieces_3845_, v_inst_3848_, v_inst_3849_, v_inst_3850_, v_inst_3851_, v_stream_3852_, v_maximumSize_3853_, v_size_3861_, v___x_3867_);
return v___x_3868_;
}
else
{
lean_object* v___f_3869_; lean_object* v___f_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
lean_inc(v_val_3863_);
lean_dec_ref_known(v_maximumSize_3853_, 1);
lean_dec(v_size_3861_);
lean_dec_ref(v_data_3859_);
lean_dec(v_inst_3851_);
lean_dec_ref(v_inst_3848_);
lean_dec(v_pieces_3845_);
v___f_3869_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3869_, 0, v___f_3862_);
lean_inc(v_toBind_3854_);
v___f_3870_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_3870_, 0, v_inst_3849_);
lean_closure_set(v___f_3870_, 1, v_val_3863_);
lean_closure_set(v___f_3870_, 2, v_toBind_3854_);
lean_closure_set(v___f_3870_, 3, v___f_3869_);
v___x_3871_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_close___boxed), 2, 1);
lean_closure_set(v___x_3871_, 0, v_stream_3852_);
v___x_3872_ = lean_apply_2(v_inst_3850_, lean_box(0), v___x_3871_);
v___x_3873_ = lean_apply_4(v_toBind_3854_, lean_box(0), lean_box(0), v___x_3872_, v___f_3870_);
return v___x_3873_;
}
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_dec_ref(v___f_3862_);
lean_dec(v_toBind_3854_);
v___x_3874_ = lean_box(0);
v___x_3875_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(v_data_3859_, v_pieces_3845_, v_inst_3848_, v_inst_3849_, v_inst_3850_, v_inst_3851_, v_stream_3852_, v_maximumSize_3853_, v_size_3861_, v___x_3874_);
return v___x_3875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3___boxed(lean_object* v_pieces_3876_, lean_object* v_size_3877_, lean_object* v_toPure_3878_, lean_object* v_inst_3879_, lean_object* v_inst_3880_, lean_object* v_inst_3881_, lean_object* v_inst_3882_, lean_object* v_stream_3883_, lean_object* v_maximumSize_3884_, lean_object* v_toBind_3885_, lean_object* v_____do__lift_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3(v_pieces_3876_, v_size_3877_, v_toPure_3878_, v_inst_3879_, v_inst_3880_, v_inst_3881_, v_inst_3882_, v_stream_3883_, v_maximumSize_3884_, v_toBind_3885_, v_____do__lift_3886_);
lean_dec(v_size_3877_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(lean_object* v_inst_3888_, lean_object* v_inst_3889_, lean_object* v_inst_3890_, lean_object* v_inst_3891_, lean_object* v_stream_3892_, lean_object* v_maximumSize_3893_, lean_object* v_pieces_3894_, lean_object* v_size_3895_){
_start:
{
lean_object* v_toApplicative_3896_; lean_object* v_toBind_3897_; lean_object* v_toPure_3898_; lean_object* v___x_3899_; lean_object* v___f_3900_; lean_object* v___x_3901_; 
v_toApplicative_3896_ = lean_ctor_get(v_inst_3888_, 0);
v_toBind_3897_ = lean_ctor_get(v_inst_3888_, 1);
lean_inc_n(v_toBind_3897_, 2);
v_toPure_3898_ = lean_ctor_get(v_toApplicative_3896_, 1);
lean_inc(v_toPure_3898_);
lean_inc(v_inst_3891_);
lean_inc_ref(v_stream_3892_);
v___x_3899_ = lean_apply_1(v_inst_3891_, v_stream_3892_);
v___f_3900_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_3900_, 0, v_pieces_3894_);
lean_closure_set(v___f_3900_, 1, v_size_3895_);
lean_closure_set(v___f_3900_, 2, v_toPure_3898_);
lean_closure_set(v___f_3900_, 3, v_inst_3888_);
lean_closure_set(v___f_3900_, 4, v_inst_3889_);
lean_closure_set(v___f_3900_, 5, v_inst_3890_);
lean_closure_set(v___f_3900_, 6, v_inst_3891_);
lean_closure_set(v___f_3900_, 7, v_stream_3892_);
lean_closure_set(v___f_3900_, 8, v_maximumSize_3893_);
lean_closure_set(v___f_3900_, 9, v_toBind_3897_);
v___x_3901_ = lean_apply_4(v_toBind_3897_, lean_box(0), lean_box(0), v___x_3899_, v___f_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(lean_object* v_data_3902_, lean_object* v_pieces_3903_, lean_object* v_inst_3904_, lean_object* v_inst_3905_, lean_object* v_inst_3906_, lean_object* v_inst_3907_, lean_object* v_stream_3908_, lean_object* v_maximumSize_3909_, lean_object* v_size_3910_, lean_object* v_____r_3911_){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_data_3902_);
lean_ctor_set(v___x_3912_, 1, v_pieces_3903_);
v___x_3913_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3904_, v_inst_3905_, v_inst_3906_, v_inst_3907_, v_stream_3908_, v_maximumSize_3909_, v___x_3912_, v_size_3910_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(lean_object* v_m_3914_, lean_object* v_inst_3915_, lean_object* v_inst_3916_, lean_object* v_inst_3917_, lean_object* v_inst_3918_, lean_object* v_stream_3919_, lean_object* v_maximumSize_3920_, lean_object* v_pieces_3921_, lean_object* v_size_3922_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3915_, v_inst_3916_, v_inst_3917_, v_inst_3918_, v_stream_3919_, v_maximumSize_3920_, v_pieces_3921_, v_size_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg___lam__0(lean_object* v_inst_3924_, lean_object* v_inst_3925_, lean_object* v_toPure_3926_, lean_object* v_result_3927_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = lean_apply_1(v_inst_3924_, v_result_3927_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3938_; 
lean_dec(v_toPure_3926_);
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3938_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3938_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v_throw_3933_; lean_object* v___x_3935_; 
v_throw_3933_ = lean_ctor_get(v_inst_3925_, 0);
lean_inc(v_throw_3933_);
lean_dec_ref(v_inst_3925_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set_tag(v___x_3931_, 18);
v___x_3935_ = v___x_3931_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3929_);
v___x_3935_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3936_; 
v___x_3936_ = lean_apply_2(v_throw_3933_, lean_box(0), v___x_3935_);
return v___x_3936_;
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3940_; 
lean_dec_ref(v_inst_3925_);
v_a_3939_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3939_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3940_ = lean_apply_2(v_toPure_3926_, lean_box(0), v_a_3939_);
return v___x_3940_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll___redArg(lean_object* v_inst_3941_, lean_object* v_inst_3942_, lean_object* v_inst_3943_, lean_object* v_inst_3944_, lean_object* v_inst_3945_, lean_object* v_stream_3946_, lean_object* v_maximumSize_3947_){
_start:
{
lean_object* v_toApplicative_3948_; lean_object* v_toBind_3949_; lean_object* v_toPure_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___f_3954_; lean_object* v___x_3955_; 
v_toApplicative_3948_ = lean_ctor_get(v_inst_3942_, 0);
v_toBind_3949_ = lean_ctor_get(v_inst_3942_, 1);
lean_inc(v_toBind_3949_);
v_toPure_3950_ = lean_ctor_get(v_toApplicative_3948_, 1);
lean_inc(v_toPure_3950_);
v___x_3951_ = lean_box(0);
v___x_3952_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inst_3943_);
v___x_3953_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_3942_, v_inst_3943_, v_inst_3944_, v_inst_3945_, v_stream_3946_, v_maximumSize_3947_, v___x_3951_, v___x_3952_);
v___f_3954_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_readAll___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3954_, 0, v_inst_3941_);
lean_closure_set(v___f_3954_, 1, v_inst_3943_);
lean_closure_set(v___f_3954_, 2, v_toPure_3950_);
v___x_3955_ = lean_apply_4(v_toBind_3949_, lean_box(0), lean_box(0), v___x_3953_, v___f_3954_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_readAll(lean_object* v_00_u03b1_3956_, lean_object* v_m_3957_, lean_object* v_inst_3958_, lean_object* v_inst_3959_, lean_object* v_inst_3960_, lean_object* v_inst_3961_, lean_object* v_inst_3962_, lean_object* v_stream_3963_, lean_object* v_maximumSize_3964_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Std_Http_Body_Stream_readAll___redArg(v_inst_3958_, v_inst_3959_, v_inst_3960_, v_inst_3961_, v_inst_3962_, v_stream_3963_, v_maximumSize_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0(lean_object* v_toPure_3966_, lean_object* v_____r_3967_){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = lean_box(0);
v___x_3969_ = lean_apply_2(v_toPure_3966_, lean_box(0), v___x_3968_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(lean_object* v_toPure_3970_, uint64_t v_consumed_3971_, lean_object* v_drainLimit_3972_, lean_object* v_inst_3973_, lean_object* v_inst_3974_, lean_object* v_stream_3975_, lean_object* v_closeStream_3976_, lean_object* v_toBind_3977_, lean_object* v___f_3978_, lean_object* v_____do__lift_3979_){
_start:
{
if (lean_obj_tag(v_____do__lift_3979_) == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
lean_dec(v___f_3978_);
lean_dec(v_toBind_3977_);
lean_dec(v_closeStream_3976_);
lean_dec_ref(v_stream_3975_);
lean_dec(v_inst_3974_);
lean_dec_ref(v_inst_3973_);
lean_dec(v_drainLimit_3972_);
v___x_3980_ = lean_box(0);
v___x_3981_ = lean_apply_2(v_toPure_3970_, lean_box(0), v___x_3980_);
return v___x_3981_;
}
else
{
lean_object* v_val_3982_; lean_object* v_data_3983_; lean_object* v___x_3984_; uint64_t v___x_3985_; uint64_t v_consumed_3986_; 
lean_dec(v_toPure_3970_);
v_val_3982_ = lean_ctor_get(v_____do__lift_3979_, 0);
v_data_3983_ = lean_ctor_get(v_val_3982_, 0);
v___x_3984_ = lean_byte_array_size(v_data_3983_);
v___x_3985_ = lean_uint64_of_nat(v___x_3984_);
v_consumed_3986_ = lean_uint64_add(v_consumed_3971_, v___x_3985_);
if (lean_obj_tag(v_drainLimit_3972_) == 1)
{
lean_object* v_val_3987_; uint64_t v___x_3988_; uint8_t v___x_3989_; 
v_val_3987_ = lean_ctor_get(v_drainLimit_3972_, 0);
v___x_3988_ = lean_unbox_uint64(v_val_3987_);
v___x_3989_ = lean_uint64_dec_lt(v___x_3988_, v_consumed_3986_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; 
lean_dec(v___f_3978_);
lean_dec(v_toBind_3977_);
v___x_3990_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3973_, v_inst_3974_, v_stream_3975_, v_drainLimit_3972_, v_closeStream_3976_, v_consumed_3986_);
return v___x_3990_;
}
else
{
lean_object* v___x_3991_; 
lean_dec_ref_known(v_drainLimit_3972_, 1);
lean_dec_ref(v_stream_3975_);
lean_dec(v_inst_3974_);
lean_dec_ref(v_inst_3973_);
v___x_3991_ = lean_apply_4(v_toBind_3977_, lean_box(0), lean_box(0), v_closeStream_3976_, v___f_3978_);
return v___x_3991_;
}
}
else
{
lean_object* v___x_3992_; 
lean_dec(v___f_3978_);
lean_dec(v_toBind_3977_);
v___x_3992_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_3973_, v_inst_3974_, v_stream_3975_, v_drainLimit_3972_, v_closeStream_3976_, v_consumed_3986_);
return v___x_3992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed(lean_object* v_toPure_3993_, lean_object* v_consumed_3994_, lean_object* v_drainLimit_3995_, lean_object* v_inst_3996_, lean_object* v_inst_3997_, lean_object* v_stream_3998_, lean_object* v_closeStream_3999_, lean_object* v_toBind_4000_, lean_object* v___f_4001_, lean_object* v_____do__lift_4002_){
_start:
{
uint64_t v_consumed_boxed_4003_; lean_object* v_res_4004_; 
v_consumed_boxed_4003_ = lean_unbox_uint64(v_consumed_3994_);
lean_dec_ref(v_consumed_3994_);
v_res_4004_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1(v_toPure_3993_, v_consumed_boxed_4003_, v_drainLimit_3995_, v_inst_3996_, v_inst_3997_, v_stream_3998_, v_closeStream_3999_, v_toBind_4000_, v___f_4001_, v_____do__lift_4002_);
lean_dec(v_____do__lift_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(lean_object* v_inst_4005_, lean_object* v_inst_4006_, lean_object* v_stream_4007_, lean_object* v_drainLimit_4008_, lean_object* v_closeStream_4009_, uint64_t v_consumed_4010_){
_start:
{
lean_object* v_toApplicative_4011_; lean_object* v_toBind_4012_; lean_object* v_toPure_4013_; lean_object* v___x_4014_; lean_object* v___f_4015_; lean_object* v___x_4016_; lean_object* v___f_4017_; lean_object* v___x_4018_; 
v_toApplicative_4011_ = lean_ctor_get(v_inst_4005_, 0);
v_toBind_4012_ = lean_ctor_get(v_inst_4005_, 1);
lean_inc_n(v_toBind_4012_, 2);
v_toPure_4013_ = lean_ctor_get(v_toApplicative_4011_, 1);
lean_inc_n(v_toPure_4013_, 2);
lean_inc(v_inst_4006_);
lean_inc_ref(v_stream_4007_);
v___x_4014_ = lean_apply_1(v_inst_4006_, v_stream_4007_);
v___f_4015_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4015_, 0, v_toPure_4013_);
v___x_4016_ = lean_box_uint64(v_consumed_4010_);
v___f_4017_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_4017_, 0, v_toPure_4013_);
lean_closure_set(v___f_4017_, 1, v___x_4016_);
lean_closure_set(v___f_4017_, 2, v_drainLimit_4008_);
lean_closure_set(v___f_4017_, 3, v_inst_4005_);
lean_closure_set(v___f_4017_, 4, v_inst_4006_);
lean_closure_set(v___f_4017_, 5, v_stream_4007_);
lean_closure_set(v___f_4017_, 6, v_closeStream_4009_);
lean_closure_set(v___f_4017_, 7, v_toBind_4012_);
lean_closure_set(v___f_4017_, 8, v___f_4015_);
v___x_4018_ = lean_apply_4(v_toBind_4012_, lean_box(0), lean_box(0), v___x_4014_, v___f_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg___boxed(lean_object* v_inst_4019_, lean_object* v_inst_4020_, lean_object* v_stream_4021_, lean_object* v_drainLimit_4022_, lean_object* v_closeStream_4023_, lean_object* v_consumed_4024_){
_start:
{
uint64_t v_consumed_boxed_4025_; lean_object* v_res_4026_; 
v_consumed_boxed_4025_ = lean_unbox_uint64(v_consumed_4024_);
lean_dec_ref(v_consumed_4024_);
v_res_4026_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_4019_, v_inst_4020_, v_stream_4021_, v_drainLimit_4022_, v_closeStream_4023_, v_consumed_boxed_4025_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(lean_object* v_m_4027_, lean_object* v_inst_4028_, lean_object* v_inst_4029_, lean_object* v_stream_4030_, lean_object* v_drainLimit_4031_, lean_object* v_closeStream_4032_, uint64_t v_consumed_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_4028_, v_inst_4029_, v_stream_4030_, v_drainLimit_4031_, v_closeStream_4032_, v_consumed_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___boxed(lean_object* v_m_4035_, lean_object* v_inst_4036_, lean_object* v_inst_4037_, lean_object* v_stream_4038_, lean_object* v_drainLimit_4039_, lean_object* v_closeStream_4040_, lean_object* v_consumed_4041_){
_start:
{
uint64_t v_consumed_boxed_4042_; lean_object* v_res_4043_; 
v_consumed_boxed_4042_ = lean_unbox_uint64(v_consumed_4041_);
lean_dec_ref(v_consumed_4041_);
v_res_4043_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop(v_m_4035_, v_inst_4036_, v_inst_4037_, v_stream_4038_, v_drainLimit_4039_, v_closeStream_4040_, v_consumed_boxed_4042_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain___redArg(lean_object* v_inst_4044_, lean_object* v_inst_4045_, lean_object* v_stream_4046_, lean_object* v_drainLimit_4047_, lean_object* v_closeStream_4048_){
_start:
{
uint64_t v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = 0ULL;
v___x_4050_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_drain_loop___redArg(v_inst_4044_, v_inst_4045_, v_stream_4046_, v_drainLimit_4047_, v_closeStream_4048_, v___x_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_drain(lean_object* v_m_4051_, lean_object* v_inst_4052_, lean_object* v_inst_4053_, lean_object* v_stream_4054_, lean_object* v_drainLimit_4055_, lean_object* v_closeStream_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l_Std_Http_Body_Stream_drain___redArg(v_inst_4052_, v_inst_4053_, v_stream_4054_, v_drainLimit_4055_, v_closeStream_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(lean_object* v_chunk_4063_, uint8_t v_incomplete_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v_ended_4069_; 
v___x_4067_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_4065_);
v___x_4068_ = lean_st_ref_get(v___y_4065_);
v_ended_4069_ = lean_ctor_get(v___x_4068_, 3);
lean_inc(v_ended_4069_);
if (lean_obj_tag(v_ended_4069_) == 0)
{
lean_object* v_pendingProducer_4070_; lean_object* v_pendingConsumer_4071_; lean_object* v_interestWaiter_4072_; lean_object* v_knownSize_4073_; lean_object* v_pendingIncomplete_4074_; uint8_t v_closeAfterProducer_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4094_; 
v_pendingProducer_4070_ = lean_ctor_get(v___x_4068_, 0);
v_pendingConsumer_4071_ = lean_ctor_get(v___x_4068_, 1);
v_interestWaiter_4072_ = lean_ctor_get(v___x_4068_, 2);
v_knownSize_4073_ = lean_ctor_get(v___x_4068_, 4);
v_pendingIncomplete_4074_ = lean_ctor_get(v___x_4068_, 5);
v_closeAfterProducer_4075_ = lean_ctor_get_uint8(v___x_4068_, sizeof(void*)*6);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4094_ == 0)
{
lean_object* v_unused_4095_; 
v_unused_4095_ = lean_ctor_get(v___x_4068_, 3);
lean_dec(v_unused_4095_);
v___x_4077_ = v___x_4068_;
v_isShared_4078_ = v_isSharedCheck_4094_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_pendingIncomplete_4074_);
lean_inc(v_knownSize_4073_);
lean_inc(v_interestWaiter_4072_);
lean_inc(v_pendingConsumer_4071_);
lean_inc(v_pendingProducer_4070_);
lean_dec(v___x_4068_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4094_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4079_; 
v___x_4079_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_push(v_pendingIncomplete_4074_, v_chunk_4063_);
if (v_incomplete_4064_ == 0)
{
lean_object* v___x_4080_; lean_object* v___x_4082_; 
v___x_4080_ = lean_box(0);
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 5, v___x_4080_);
v___x_4082_ = v___x_4077_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_pendingProducer_4070_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_pendingConsumer_4071_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_interestWaiter_4072_);
lean_ctor_set(v_reuseFailAlloc_4087_, 3, v_ended_4069_);
lean_ctor_set(v_reuseFailAlloc_4087_, 4, v_knownSize_4073_);
lean_ctor_set(v_reuseFailAlloc_4087_, 5, v___x_4080_);
lean_ctor_set_uint8(v_reuseFailAlloc_4087_, sizeof(void*)*6, v_closeAfterProducer_4075_);
v___x_4082_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4083_ = lean_st_ref_swap(v___y_4065_, v___x_4082_);
lean_dec(v___x_4083_);
v___x_4084_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Incomplete_toChunk(v___x_4079_);
v___x_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
v___x_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
return v___x_4086_;
}
}
else
{
lean_object* v___x_4088_; lean_object* v___x_4090_; 
v___x_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4079_);
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 5, v___x_4088_);
v___x_4090_ = v___x_4077_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_pendingProducer_4070_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_pendingConsumer_4071_);
lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_interestWaiter_4072_);
lean_ctor_set(v_reuseFailAlloc_4093_, 3, v_ended_4069_);
lean_ctor_set(v_reuseFailAlloc_4093_, 4, v_knownSize_4073_);
lean_ctor_set(v_reuseFailAlloc_4093_, 5, v___x_4088_);
lean_ctor_set_uint8(v_reuseFailAlloc_4093_, sizeof(void*)*6, v_closeAfterProducer_4075_);
v___x_4090_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = lean_st_ref_swap(v___y_4065_, v___x_4090_);
lean_dec(v___x_4091_);
v___x_4092_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___redArg___lam__0___closed__0));
return v___x_4092_;
}
}
}
}
else
{
lean_object* v___x_4096_; 
lean_dec_ref_known(v_ended_4069_, 1);
lean_dec(v___x_4068_);
lean_dec_ref(v_chunk_4063_);
v___x_4096_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2));
return v___x_4096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(lean_object* v_chunk_4097_, lean_object* v_incomplete_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
uint8_t v_incomplete_boxed_4101_; lean_object* v_res_4102_; 
v_incomplete_boxed_4101_ = lean_unbox(v_incomplete_4098_);
v_res_4102_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(v_chunk_4097_, v_incomplete_boxed_4101_, v___y_4099_);
lean_dec(v___y_4099_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(lean_object* v_stream_4103_, lean_object* v_chunk_4104_, uint8_t v_incomplete_4105_){
_start:
{
lean_object* v___x_4107_; lean_object* v___f_4108_; lean_object* v___x_4109_; 
v___x_4107_ = lean_box(v_incomplete_4105_);
v___f_4108_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4108_, 0, v_chunk_4104_);
lean_closure_set(v___f_4108_, 1, v___x_4107_);
v___x_4109_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_4103_, v___f_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(lean_object* v_stream_4110_, lean_object* v_chunk_4111_, lean_object* v_incomplete_4112_, lean_object* v_a_4113_){
_start:
{
uint8_t v_incomplete_boxed_4114_; lean_object* v_res_4115_; 
v_incomplete_boxed_4114_ = lean_unbox(v_incomplete_4112_);
v_res_4115_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_4110_, v_chunk_4111_, v_incomplete_boxed_4114_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(lean_object* v_x_4122_){
_start:
{
if (lean_obj_tag(v_x_4122_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4132_; 
v_a_4124_ = lean_ctor_get(v_x_4122_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_x_4122_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4126_ = v_x_4122_;
v_isShared_4127_ = v_isSharedCheck_4132_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v_x_4122_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4132_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4130_; 
v___x_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
return v___x_4130_;
}
}
}
else
{
lean_object* v___x_4133_; 
lean_dec_ref_known(v_x_4122_, 1);
v___x_4133_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2));
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(lean_object* v_x_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_4134_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(lean_object* v_00___4137_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(lean_object* v_00___4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(v_00___4140_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(lean_object* v___f_4147_, lean_object* v_x_4148_){
_start:
{
if (lean_obj_tag(v_x_4148_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4160_; 
lean_dec_ref(v___f_4147_);
v_a_4152_ = lean_ctor_get(v_x_4148_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_x_4148_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4154_ = v_x_4148_;
v_isShared_4155_ = v_isSharedCheck_4160_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v_x_4148_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4160_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; 
v___x_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
return v___x_4158_;
}
}
}
else
{
lean_object* v_a_4161_; 
v_a_4161_ = lean_ctor_get(v_x_4148_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v_x_4148_, 1);
if (lean_obj_tag(v_a_4161_) == 1)
{
lean_object* v_val_4162_; uint8_t v___x_4163_; 
v_val_4162_ = lean_ctor_get(v_a_4161_, 0);
lean_inc(v_val_4162_);
lean_dec_ref_known(v_a_4161_, 1);
v___x_4163_ = lean_unbox(v_val_4162_);
lean_dec(v_val_4162_);
if (v___x_4163_ == 1)
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4164_ = lean_box(0);
v___x_4165_ = lean_apply_2(v___f_4147_, v___x_4164_, lean_box(0));
return v___x_4165_;
}
else
{
lean_dec_ref(v___f_4147_);
goto v___jp_4150_;
}
}
else
{
lean_dec(v_a_4161_);
lean_dec_ref(v___f_4147_);
goto v___jp_4150_;
}
}
v___jp_4150_:
{
lean_object* v___x_4151_; 
v___x_4151_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1));
return v___x_4151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(lean_object* v___f_4166_, lean_object* v_x_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(v___f_4166_, v_x_4167_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(lean_object* v_a_4170_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4171_, 0, v_a_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(uint8_t v___x_4172_, lean_object* v_x_4173_){
_start:
{
if (lean_obj_tag(v_x_4173_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4183_; 
v_a_4175_ = lean_ctor_get(v_x_4173_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v_x_4173_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4177_ = v_x_4173_;
v_isShared_4178_ = v_isSharedCheck_4183_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v_x_4173_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4183_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
lean_object* v___x_4181_; 
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
return v___x_4181_;
}
}
}
else
{
lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4194_; 
v_isSharedCheck_4194_ = !lean_is_exclusive(v_x_4173_);
if (v_isSharedCheck_4194_ == 0)
{
lean_object* v_unused_4195_; 
v_unused_4195_ = lean_ctor_get(v_x_4173_, 0);
lean_dec(v_unused_4195_);
v___x_4185_ = v_x_4173_;
v_isShared_4186_ = v_isSharedCheck_4194_;
goto v_resetjp_4184_;
}
else
{
lean_dec(v_x_4173_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4194_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4187_ = lean_box(v___x_4172_);
v___x_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 0, v___x_4188_);
v___x_4190_ = v___x_4185_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(lean_object* v___x_4196_, lean_object* v_x_4197_, lean_object* v___y_4198_){
_start:
{
uint8_t v___x_5385__boxed_4199_; lean_object* v_res_4200_; 
v___x_5385__boxed_4199_ = lean_unbox(v___x_4196_);
v_res_4200_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(v___x_5385__boxed_4199_, v_x_4197_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(uint8_t v_a_4201_, lean_object* v_x_4202_){
_start:
{
if (lean_obj_tag(v_x_4202_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4212_; 
v_a_4204_ = lean_ctor_get(v_x_4202_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_x_4202_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4206_ = v_x_4202_;
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v_x_4202_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
return v___x_4210_;
}
}
}
else
{
lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4223_; 
v_isSharedCheck_4223_ = !lean_is_exclusive(v_x_4202_);
if (v_isSharedCheck_4223_ == 0)
{
lean_object* v_unused_4224_; 
v_unused_4224_ = lean_ctor_get(v_x_4202_, 0);
lean_dec(v_unused_4224_);
v___x_4214_ = v_x_4202_;
v_isShared_4215_ = v_isSharedCheck_4223_;
goto v_resetjp_4213_;
}
else
{
lean_dec(v_x_4202_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4223_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4216_ = lean_box(v_a_4201_);
v___x_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4216_);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v___x_4217_);
v___x_4219_ = v___x_4214_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
return v___x_4221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(lean_object* v_a_4225_, lean_object* v_x_4226_, lean_object* v___y_4227_){
_start:
{
uint8_t v_a_5437__boxed_4228_; lean_object* v_res_4229_; 
v_a_5437__boxed_4228_ = lean_unbox(v_a_4225_);
v_res_4229_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(v_a_5437__boxed_4228_, v_x_4226_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(lean_object* v_pendingProducer_4230_, lean_object* v_interestWaiter_4231_, lean_object* v_ended_4232_, lean_object* v_knownSize_4233_, lean_object* v_pendingIncomplete_4234_, uint8_t v_closeAfterProducer_4235_, lean_object* v___y_4236_, lean_object* v_chunk_4237_, uint8_t v___x_4238_, lean_object* v___f_4239_, lean_object* v_x_4240_){
_start:
{
if (lean_obj_tag(v_x_4240_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v___f_4239_);
lean_dec(v_pendingIncomplete_4234_);
lean_dec(v_knownSize_4233_);
lean_dec(v_ended_4232_);
lean_dec(v_interestWaiter_4231_);
lean_dec(v_pendingProducer_4230_);
v_a_4242_ = lean_ctor_get(v_x_4240_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_x_4240_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4244_ = v_x_4240_;
v_isShared_4245_ = v_isSharedCheck_4250_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v_x_4240_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4250_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_object* v___x_4248_; 
v___x_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
return v___x_4248_;
}
}
}
else
{
lean_object* v_a_4251_; uint8_t v___x_4252_; 
v_a_4251_ = lean_ctor_get(v_x_4240_, 0);
lean_inc(v_a_4251_);
lean_dec_ref_known(v_x_4240_, 1);
v___x_4252_ = lean_unbox(v_a_4251_);
if (v___x_4252_ == 0)
{
lean_object* v___f_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; lean_object* v___x_4260_; 
lean_dec_ref(v___f_4239_);
lean_inc(v_a_4251_);
v___f_4253_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4253_, 0, v_a_4251_);
v___x_4254_ = lean_box(0);
v___x_4255_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4255_, 0, v_pendingProducer_4230_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
lean_ctor_set(v___x_4255_, 2, v_interestWaiter_4231_);
lean_ctor_set(v___x_4255_, 3, v_ended_4232_);
lean_ctor_set(v___x_4255_, 4, v_knownSize_4233_);
lean_ctor_set(v___x_4255_, 5, v_pendingIncomplete_4234_);
lean_ctor_set_uint8(v___x_4255_, sizeof(void*)*6, v_closeAfterProducer_4235_);
v___x_4256_ = lean_unsigned_to_nat(0u);
v___x_4257_ = lean_st_ref_swap(v___y_4236_, v___x_4255_);
lean_dec(v___x_4257_);
v___x_4258_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4259_ = lean_unbox(v_a_4251_);
lean_dec(v_a_4251_);
v___x_4260_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4256_, v___x_4259_, v___x_4258_, v___f_4253_);
return v___x_4260_;
}
else
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_dec(v_a_4251_);
v___x_4261_ = lean_box(0);
v___x_4262_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_4233_, v_chunk_4237_);
v___x_4263_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4263_, 0, v_pendingProducer_4230_);
lean_ctor_set(v___x_4263_, 1, v___x_4261_);
lean_ctor_set(v___x_4263_, 2, v_interestWaiter_4231_);
lean_ctor_set(v___x_4263_, 3, v_ended_4232_);
lean_ctor_set(v___x_4263_, 4, v___x_4262_);
lean_ctor_set(v___x_4263_, 5, v_pendingIncomplete_4234_);
lean_ctor_set_uint8(v___x_4263_, sizeof(void*)*6, v_closeAfterProducer_4235_);
v___x_4264_ = lean_unsigned_to_nat(0u);
v___x_4265_ = lean_st_ref_swap(v___y_4236_, v___x_4263_);
lean_dec(v___x_4265_);
v___x_4266_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4267_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4264_, v___x_4238_, v___x_4266_, v___f_4239_);
return v___x_4267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(lean_object* v_pendingProducer_4268_, lean_object* v_interestWaiter_4269_, lean_object* v_ended_4270_, lean_object* v_knownSize_4271_, lean_object* v_pendingIncomplete_4272_, lean_object* v_closeAfterProducer_4273_, lean_object* v___y_4274_, lean_object* v_chunk_4275_, lean_object* v___x_4276_, lean_object* v___f_4277_, lean_object* v_x_4278_, lean_object* v___y_4279_){
_start:
{
uint8_t v_closeAfterProducer_boxed_4280_; uint8_t v___x_5498__boxed_4281_; lean_object* v_res_4282_; 
v_closeAfterProducer_boxed_4280_ = lean_unbox(v_closeAfterProducer_4273_);
v___x_5498__boxed_4281_ = lean_unbox(v___x_4276_);
v_res_4282_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(v_pendingProducer_4268_, v_interestWaiter_4269_, v_ended_4270_, v_knownSize_4271_, v_pendingIncomplete_4272_, v_closeAfterProducer_boxed_4280_, v___y_4274_, v_chunk_4275_, v___x_5498__boxed_4281_, v___f_4277_, v_x_4278_);
lean_dec_ref(v_chunk_4275_);
lean_dec(v___y_4274_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(lean_object* v___y_4301_, lean_object* v_chunk_4302_, lean_object* v_a_4303_, lean_object* v___f_4304_, lean_object* v_x_4305_){
_start:
{
if (lean_obj_tag(v_x_4305_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v___f_4304_);
lean_dec(v_a_4303_);
lean_dec_ref(v_chunk_4302_);
v_a_4307_ = lean_ctor_get(v_x_4305_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v_x_4305_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4309_ = v_x_4305_;
v_isShared_4310_ = v_isSharedCheck_4315_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v_x_4305_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4315_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
return v___x_4313_;
}
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4365_; 
v_a_4316_ = lean_ctor_get(v_x_4305_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v_x_4305_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4318_ = v_x_4305_;
v_isShared_4319_ = v_isSharedCheck_4365_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v_x_4305_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4365_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v_ended_4320_; 
v_ended_4320_ = lean_ctor_get(v_a_4316_, 3);
lean_inc(v_ended_4320_);
if (lean_obj_tag(v_ended_4320_) == 0)
{
lean_object* v_pendingProducer_4321_; lean_object* v_pendingConsumer_4322_; lean_object* v_interestWaiter_4323_; lean_object* v_knownSize_4324_; lean_object* v_pendingIncomplete_4325_; uint8_t v_closeAfterProducer_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4362_; 
v_pendingProducer_4321_ = lean_ctor_get(v_a_4316_, 0);
v_pendingConsumer_4322_ = lean_ctor_get(v_a_4316_, 1);
v_interestWaiter_4323_ = lean_ctor_get(v_a_4316_, 2);
v_knownSize_4324_ = lean_ctor_get(v_a_4316_, 4);
v_pendingIncomplete_4325_ = lean_ctor_get(v_a_4316_, 5);
v_closeAfterProducer_4326_ = lean_ctor_get_uint8(v_a_4316_, sizeof(void*)*6);
v_isSharedCheck_4362_ = !lean_is_exclusive(v_a_4316_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; 
v_unused_4363_ = lean_ctor_get(v_a_4316_, 3);
lean_dec(v_unused_4363_);
v___x_4328_ = v_a_4316_;
v_isShared_4329_ = v_isSharedCheck_4362_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_pendingIncomplete_4325_);
lean_inc(v_knownSize_4324_);
lean_inc(v_interestWaiter_4323_);
lean_inc(v_pendingConsumer_4322_);
lean_inc(v_pendingProducer_4321_);
lean_dec(v_a_4316_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4362_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
uint8_t v___x_4330_; 
v___x_4330_ = 0;
if (lean_obj_tag(v_pendingConsumer_4322_) == 1)
{
lean_object* v_val_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4351_; 
lean_del_object(v___x_4328_);
lean_dec_ref(v___f_4304_);
lean_dec(v_a_4303_);
v_val_4331_ = lean_ctor_get(v_pendingConsumer_4322_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v_pendingConsumer_4322_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4333_ = v_pendingConsumer_4322_;
v_isShared_4334_ = v_isSharedCheck_4351_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_val_4331_);
lean_dec(v_pendingConsumer_4322_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4351_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___f_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___f_4338_; lean_object* v___x_4340_; 
v___f_4335_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0));
v___x_4336_ = lean_box(v_closeAfterProducer_4326_);
v___x_4337_ = lean_box(v___x_4330_);
lean_inc_ref(v_chunk_4302_);
lean_inc(v___y_4301_);
v___f_4338_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed), 12, 10);
lean_closure_set(v___f_4338_, 0, v_pendingProducer_4321_);
lean_closure_set(v___f_4338_, 1, v_interestWaiter_4323_);
lean_closure_set(v___f_4338_, 2, v_ended_4320_);
lean_closure_set(v___f_4338_, 3, v_knownSize_4324_);
lean_closure_set(v___f_4338_, 4, v_pendingIncomplete_4325_);
lean_closure_set(v___f_4338_, 5, v___x_4336_);
lean_closure_set(v___f_4338_, 6, v___y_4301_);
lean_closure_set(v___f_4338_, 7, v_chunk_4302_);
lean_closure_set(v___f_4338_, 8, v___x_4337_);
lean_closure_set(v___f_4338_, 9, v___f_4335_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 0, v_chunk_4302_);
v___x_4340_ = v___x_4333_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_chunk_4302_);
v___x_4340_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4342_; 
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 0, v___x_4340_);
v___x_4342_ = v___x_4318_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4340_);
v___x_4342_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
lean_object* v___x_4343_; uint8_t v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4343_ = lean_unsigned_to_nat(0u);
v___x_4344_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_4331_, v___x_4342_);
lean_dec(v_val_4331_);
v___x_4345_ = lean_box(v___x_4344_);
v___x_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4345_);
v___x_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
v___x_4348_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4343_, v___x_4330_, v___x_4347_, v___f_4338_);
return v___x_4348_;
}
}
}
}
else
{
lean_del_object(v___x_4318_);
if (lean_obj_tag(v_pendingProducer_4321_) == 0)
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4355_; 
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v_chunk_4302_);
lean_ctor_set(v___x_4352_, 1, v_a_4303_);
v___x_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4352_);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4353_);
v___x_4355_ = v___x_4328_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4353_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v_pendingConsumer_4322_);
lean_ctor_set(v_reuseFailAlloc_4360_, 2, v_interestWaiter_4323_);
lean_ctor_set(v_reuseFailAlloc_4360_, 3, v_ended_4320_);
lean_ctor_set(v_reuseFailAlloc_4360_, 4, v_knownSize_4324_);
lean_ctor_set(v_reuseFailAlloc_4360_, 5, v_pendingIncomplete_4325_);
lean_ctor_set_uint8(v_reuseFailAlloc_4360_, sizeof(void*)*6, v_closeAfterProducer_4326_);
v___x_4355_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = lean_st_ref_swap(v___y_4301_, v___x_4355_);
lean_dec(v___x_4357_);
v___x_4358_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4356_, v___x_4330_, v___x_4358_, v___f_4304_);
return v___x_4359_;
}
}
else
{
lean_object* v___x_4361_; 
lean_dec_ref_known(v_pendingProducer_4321_, 1);
lean_del_object(v___x_4328_);
lean_dec(v_pendingIncomplete_4325_);
lean_dec(v_knownSize_4324_);
lean_dec(v_interestWaiter_4323_);
lean_dec(v_pendingConsumer_4322_);
lean_dec_ref(v___f_4304_);
lean_dec(v_a_4303_);
lean_dec_ref(v_chunk_4302_);
v___x_4361_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5));
return v___x_4361_;
}
}
}
}
else
{
lean_object* v___x_4364_; 
lean_dec_ref_known(v_ended_4320_, 1);
lean_del_object(v___x_4318_);
lean_dec(v_a_4316_);
lean_dec_ref(v___f_4304_);
lean_dec(v_a_4303_);
lean_dec_ref(v_chunk_4302_);
v___x_4364_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8));
return v___x_4364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(lean_object* v___y_4366_, lean_object* v_chunk_4367_, lean_object* v_a_4368_, lean_object* v___f_4369_, lean_object* v_x_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(v___y_4366_, v_chunk_4367_, v_a_4368_, v___f_4369_, v_x_4370_);
lean_dec(v___y_4366_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(lean_object* v___y_4373_, lean_object* v___f_4374_, lean_object* v_x_4375_){
_start:
{
if (lean_obj_tag(v_x_4375_) == 0)
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4385_; 
lean_dec_ref(v___f_4374_);
v_a_4377_ = lean_ctor_get(v_x_4375_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v_x_4375_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4379_ = v_x_4375_;
v_isShared_4380_ = v_isSharedCheck_4385_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v_x_4375_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4385_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4383_; 
v___x_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
return v___x_4383_;
}
}
}
else
{
lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4397_; 
v_isSharedCheck_4397_ = !lean_is_exclusive(v_x_4375_);
if (v_isSharedCheck_4397_ == 0)
{
lean_object* v_unused_4398_; 
v_unused_4398_ = lean_ctor_get(v_x_4375_, 0);
lean_dec(v_unused_4398_);
v___x_4387_ = v_x_4375_;
v_isShared_4388_ = v_isSharedCheck_4397_;
goto v_resetjp_4386_;
}
else
{
lean_dec(v_x_4375_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4397_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4389_; uint8_t v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
v___x_4389_ = lean_unsigned_to_nat(0u);
v___x_4390_ = 0;
v___x_4391_ = lean_st_ref_get(v___y_4373_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v___x_4391_);
v___x_4393_ = v___x_4387_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
v___x_4395_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4389_, v___x_4390_, v___x_4394_, v___f_4374_);
return v___x_4395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(lean_object* v___y_4399_, lean_object* v___f_4400_, lean_object* v_x_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(v___y_4399_, v___f_4400_, v_x_4401_);
lean_dec(v___y_4399_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(lean_object* v_chunk_4404_, lean_object* v_a_4405_, lean_object* v___f_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v___f_4409_; lean_object* v___f_4410_; lean_object* v___x_4411_; uint8_t v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
lean_inc_n(v___y_4407_, 2);
v___f_4409_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4409_, 0, v___y_4407_);
lean_closure_set(v___f_4409_, 1, v_chunk_4404_);
lean_closure_set(v___f_4409_, 2, v_a_4405_);
lean_closure_set(v___f_4409_, 3, v___f_4406_);
v___f_4410_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed), 4, 2);
lean_closure_set(v___f_4410_, 0, v___y_4407_);
lean_closure_set(v___f_4410_, 1, v___f_4409_);
v___x_4411_ = lean_unsigned_to_nat(0u);
v___x_4412_ = 0;
v___x_4413_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4407_);
v___x_4414_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4411_, v___x_4412_, v___x_4413_, v___f_4410_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(lean_object* v_chunk_4415_, lean_object* v_a_4416_, lean_object* v___f_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(v_chunk_4415_, v_a_4416_, v___f_4417_, v___y_4418_);
lean_dec(v___y_4418_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(lean_object* v_a_4426_, lean_object* v___f_4427_, lean_object* v___f_4428_, lean_object* v_stream_4429_, lean_object* v_chunk_4430_, lean_object* v___f_4431_, lean_object* v_x_4432_){
_start:
{
if (lean_obj_tag(v_x_4432_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4442_; 
lean_dec_ref(v___f_4431_);
lean_dec_ref(v_chunk_4430_);
lean_dec_ref(v_stream_4429_);
lean_dec_ref(v___f_4428_);
lean_dec_ref(v___f_4427_);
v_a_4434_ = lean_ctor_get(v_x_4432_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_x_4432_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4436_ = v_x_4432_;
v_isShared_4437_ = v_isSharedCheck_4442_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v_x_4432_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4442_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; 
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
return v___x_4440_;
}
}
}
else
{
lean_object* v_a_4443_; 
v_a_4443_ = lean_ctor_get(v_x_4432_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v_x_4432_, 1);
if (lean_obj_tag(v_a_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4452_; 
lean_dec_ref(v___f_4431_);
lean_dec_ref(v_chunk_4430_);
lean_dec_ref(v_stream_4429_);
lean_dec_ref(v___f_4428_);
lean_dec_ref(v___f_4427_);
v_a_4444_ = lean_ctor_get(v_a_4443_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v_a_4443_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4446_ = v_a_4443_;
v_isShared_4447_ = v_isSharedCheck_4452_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v_a_4443_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4452_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
lean_object* v___x_4450_; 
v___x_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
return v___x_4450_;
}
}
}
else
{
lean_object* v_a_4453_; 
v_a_4453_ = lean_ctor_get(v_a_4443_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v_a_4443_, 1);
if (lean_obj_tag(v_a_4453_) == 0)
{
lean_object* v___x_4454_; lean_object* v___x_4455_; uint8_t v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
lean_dec_ref(v___f_4431_);
lean_dec_ref(v_chunk_4430_);
lean_dec_ref(v_stream_4429_);
v___x_4454_ = lean_io_promise_result_opt(v_a_4426_);
v___x_4455_ = lean_unsigned_to_nat(0u);
v___x_4456_ = 0;
v___x_4457_ = lean_task_map(v___f_4427_, v___x_4454_, v___x_4455_, v___x_4456_);
v___x_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4457_);
v___x_4459_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4455_, v___x_4456_, v___x_4458_, v___f_4428_);
return v___x_4459_;
}
else
{
lean_object* v_val_4460_; uint8_t v___x_4461_; 
lean_dec_ref(v___f_4428_);
lean_dec_ref(v___f_4427_);
v_val_4460_ = lean_ctor_get(v_a_4453_, 0);
lean_inc(v_val_4460_);
lean_dec_ref_known(v_a_4453_, 1);
v___x_4461_ = lean_unbox(v_val_4460_);
lean_dec(v_val_4460_);
if (v___x_4461_ == 0)
{
lean_object* v___x_4462_; 
lean_dec_ref(v___f_4431_);
v___x_4462_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_4429_, v_chunk_4430_);
return v___x_4462_;
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
lean_dec_ref(v_chunk_4430_);
lean_dec_ref(v_stream_4429_);
v___x_4463_ = lean_box(0);
v___x_4464_ = lean_apply_2(v___f_4431_, v___x_4463_, lean_box(0));
return v___x_4464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(lean_object* v_a_4465_, lean_object* v___f_4466_, lean_object* v___f_4467_, lean_object* v_stream_4468_, lean_object* v_chunk_4469_, lean_object* v___f_4470_, lean_object* v_x_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(v_a_4465_, v___f_4466_, v___f_4467_, v_stream_4468_, v_chunk_4469_, v___f_4470_, v_x_4471_);
lean_dec(v_a_4465_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(lean_object* v_chunk_4474_, lean_object* v___f_4475_, lean_object* v___f_4476_, lean_object* v___f_4477_, lean_object* v_stream_4478_, lean_object* v___f_4479_, lean_object* v_x_4480_){
_start:
{
if (lean_obj_tag(v_x_4480_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4490_; 
lean_dec_ref(v___f_4479_);
lean_dec_ref(v_stream_4478_);
lean_dec_ref(v___f_4477_);
lean_dec_ref(v___f_4476_);
lean_dec_ref(v___f_4475_);
lean_dec_ref(v_chunk_4474_);
v_a_4482_ = lean_ctor_get(v_x_4480_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v_x_4480_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4484_ = v_x_4480_;
v_isShared_4485_ = v_isSharedCheck_4490_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v_x_4480_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4490_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; 
v___x_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
return v___x_4488_;
}
}
}
else
{
lean_object* v_a_4491_; lean_object* v___f_4492_; lean_object* v___f_4493_; lean_object* v___x_4494_; uint8_t v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v_a_4491_ = lean_ctor_get(v_x_4480_, 0);
lean_inc_n(v_a_4491_, 2);
lean_dec_ref_known(v_x_4480_, 1);
lean_inc_ref(v_chunk_4474_);
v___f_4492_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4492_, 0, v_chunk_4474_);
lean_closure_set(v___f_4492_, 1, v_a_4491_);
lean_closure_set(v___f_4492_, 2, v___f_4475_);
lean_inc_ref(v_stream_4478_);
v___f_4493_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed), 8, 6);
lean_closure_set(v___f_4493_, 0, v_a_4491_);
lean_closure_set(v___f_4493_, 1, v___f_4476_);
lean_closure_set(v___f_4493_, 2, v___f_4477_);
lean_closure_set(v___f_4493_, 3, v_stream_4478_);
lean_closure_set(v___f_4493_, 4, v_chunk_4474_);
lean_closure_set(v___f_4493_, 5, v___f_4479_);
v___x_4494_ = lean_unsigned_to_nat(0u);
v___x_4495_ = 0;
v___x_4496_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_4478_, v___f_4492_);
v___x_4497_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4494_, v___x_4495_, v___x_4496_, v___f_4493_);
return v___x_4497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(lean_object* v_chunk_4498_, lean_object* v___f_4499_, lean_object* v___f_4500_, lean_object* v___f_4501_, lean_object* v_stream_4502_, lean_object* v___f_4503_, lean_object* v_x_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(v_chunk_4498_, v___f_4499_, v___f_4500_, v___f_4501_, v_stream_4502_, v___f_4503_, v_x_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(lean_object* v_stream_4507_, lean_object* v_chunk_4508_){
_start:
{
lean_object* v___f_4510_; lean_object* v___f_4511_; lean_object* v___f_4512_; lean_object* v___f_4513_; lean_object* v___f_4514_; lean_object* v___x_4515_; uint8_t v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___f_4510_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0));
v___f_4511_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1));
v___f_4512_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2));
v___f_4513_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3));
v___f_4514_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed), 8, 6);
lean_closure_set(v___f_4514_, 0, v_chunk_4508_);
lean_closure_set(v___f_4514_, 1, v___f_4510_);
lean_closure_set(v___f_4514_, 2, v___f_4513_);
lean_closure_set(v___f_4514_, 3, v___f_4512_);
lean_closure_set(v___f_4514_, 4, v_stream_4507_);
lean_closure_set(v___f_4514_, 5, v___f_4511_);
v___x_4515_ = lean_unsigned_to_nat(0u);
v___x_4516_ = 0;
v___x_4517_ = lean_io_promise_new();
v___x_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
v___x_4520_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4515_, v___x_4516_, v___x_4519_, v___f_4514_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(lean_object* v_stream_4521_, lean_object* v_chunk_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_4521_, v_chunk_4522_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0(lean_object* v_stream_4525_, lean_object* v_x_4526_){
_start:
{
if (lean_obj_tag(v_x_4526_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4536_; 
lean_dec_ref(v_stream_4525_);
v_a_4528_ = lean_ctor_get(v_x_4526_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v_x_4526_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4530_ = v_x_4526_;
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v_x_4526_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4528_);
v___x_4533_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; 
v___x_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
return v___x_4534_;
}
}
}
else
{
lean_object* v_a_4537_; 
v_a_4537_ = lean_ctor_get(v_x_4526_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v_x_4526_, 1);
if (lean_obj_tag(v_a_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4546_; 
lean_dec_ref(v_stream_4525_);
v_a_4538_ = lean_ctor_get(v_a_4537_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v_a_4537_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4540_ = v_a_4537_;
v_isShared_4541_ = v_isSharedCheck_4546_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v_a_4537_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4546_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4538_);
v___x_4543_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
lean_object* v___x_4544_; 
v___x_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
return v___x_4544_;
}
}
}
else
{
lean_object* v_a_4547_; 
v_a_4547_ = lean_ctor_get(v_a_4537_, 0);
lean_inc(v_a_4547_);
lean_dec_ref_known(v_a_4537_, 1);
if (lean_obj_tag(v_a_4547_) == 0)
{
lean_object* v___x_4548_; 
lean_dec_ref(v_stream_4525_);
v___x_4548_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4548_;
}
else
{
lean_object* v_val_4549_; lean_object* v_data_4550_; lean_object* v_extensions_4551_; uint8_t v___x_4552_; 
v_val_4549_ = lean_ctor_get(v_a_4547_, 0);
lean_inc(v_val_4549_);
lean_dec_ref_known(v_a_4547_, 1);
v_data_4550_ = lean_ctor_get(v_val_4549_, 0);
v_extensions_4551_ = lean_ctor_get(v_val_4549_, 1);
v___x_4552_ = l_ByteArray_isEmpty(v_data_4550_);
if (v___x_4552_ == 0)
{
lean_object* v___x_4553_; 
v___x_4553_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_4525_, v_val_4549_);
return v___x_4553_;
}
else
{
lean_object* v___x_4554_; lean_object* v___x_4555_; uint8_t v___x_4556_; 
v___x_4554_ = lean_array_get_size(v_extensions_4551_);
v___x_4555_ = lean_unsigned_to_nat(0u);
v___x_4556_ = lean_nat_dec_eq(v___x_4554_, v___x_4555_);
if (v___x_4556_ == 0)
{
lean_object* v___x_4557_; 
v___x_4557_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_4525_, v_val_4549_);
return v___x_4557_;
}
else
{
lean_object* v___x_4558_; 
lean_dec(v_val_4549_);
lean_dec_ref(v_stream_4525_);
v___x_4558_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___lam__0___boxed(lean_object* v_stream_4559_, lean_object* v_x_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_4559_, v_x_4560_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send(lean_object* v_stream_4563_, lean_object* v_chunk_4564_, uint8_t v_incomplete_4565_){
_start:
{
lean_object* v___f_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
lean_inc_ref(v_stream_4563_);
v___f_4567_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_send___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4567_, 0, v_stream_4563_);
v___x_4568_ = lean_unsigned_to_nat(0u);
v___x_4569_ = 0;
v___x_4570_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_4563_, v_chunk_4564_, v_incomplete_4565_);
v___x_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4570_);
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
v___x_4573_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4568_, v___x_4569_, v___x_4572_, v___f_4567_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_send___boxed(lean_object* v_stream_4574_, lean_object* v_chunk_4575_, lean_object* v_incomplete_4576_, lean_object* v_a_4577_){
_start:
{
uint8_t v_incomplete_boxed_4578_; lean_object* v_res_4579_; 
v_incomplete_boxed_4578_ = lean_unbox(v_incomplete_4576_);
v_res_4579_ = l_Std_Http_Body_Stream_send(v_stream_4574_, v_chunk_4575_, v_incomplete_boxed_4578_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__0(lean_object* v_x_4584_){
_start:
{
if (lean_obj_tag(v_x_4584_) == 0)
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4594_; 
v_a_4586_ = lean_ctor_get(v_x_4584_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_x_4584_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4588_ = v_x_4584_;
v_isShared_4589_ = v_isSharedCheck_4594_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v_x_4584_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4594_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
lean_object* v___x_4592_; 
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4591_);
return v___x_4592_;
}
}
}
else
{
lean_object* v___x_4595_; 
lean_dec_ref_known(v_x_4584_, 1);
v___x_4595_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___lam__0___closed__1));
return v___x_4595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__0___boxed(lean_object* v_x_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Std_Http_Body_Stream_offer___lam__0(v_x_4596_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__1(lean_object* v_____r_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___lam__0___closed__1));
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__1___boxed(lean_object* v_____r_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Std_Http_Body_Stream_offer___lam__1(v_____r_4603_, v___y_4604_);
lean_dec(v___y_4604_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__3(lean_object* v_x_4607_){
_start:
{
if (lean_obj_tag(v_x_4607_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4617_; 
v_a_4609_ = lean_ctor_get(v_x_4607_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v_x_4607_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4611_ = v_x_4607_;
v_isShared_4612_ = v_isSharedCheck_4617_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v_x_4607_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4617_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4614_; 
if (v_isShared_4612_ == 0)
{
v___x_4614_ = v___x_4611_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4609_);
v___x_4614_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4634_; 
v_a_4618_ = lean_ctor_get(v_x_4607_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v_x_4607_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4620_ = v_x_4607_;
v_isShared_4621_ = v_isSharedCheck_4634_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v_x_4607_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4634_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
if (lean_obj_tag(v_a_4618_) == 1)
{
lean_object* v_val_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4632_; 
v_val_4622_ = lean_ctor_get(v_a_4618_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v_a_4618_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4624_ = v_a_4618_;
v_isShared_4625_ = v_isSharedCheck_4632_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_val_4622_);
lean_dec(v_a_4618_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4632_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set_tag(v___x_4620_, 0);
lean_ctor_set(v___x_4620_, 0, v_val_4622_);
v___x_4627_ = v___x_4620_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_val_4622_);
v___x_4627_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
lean_object* v___x_4629_; 
if (v_isShared_4625_ == 0)
{
lean_ctor_set_tag(v___x_4624_, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4627_);
v___x_4629_ = v___x_4624_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4627_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
else
{
lean_object* v___x_4633_; 
lean_del_object(v___x_4620_);
lean_dec(v_a_4618_);
v___x_4633_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_4633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__3___boxed(lean_object* v_x_4635_, lean_object* v___y_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Std_Http_Body_Stream_offer___lam__3(v_x_4635_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__2(lean_object* v___f_4638_, lean_object* v___y_4639_, lean_object* v_x_4640_){
_start:
{
if (lean_obj_tag(v_x_4640_) == 0)
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4650_; 
lean_dec_ref(v___f_4638_);
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
lean_object* v_a_4651_; lean_object* v___x_4652_; 
v_a_4651_ = lean_ctor_get(v_x_4640_, 0);
lean_inc(v_a_4651_);
lean_dec_ref_known(v_x_4640_, 1);
lean_inc(v___y_4639_);
v___x_4652_ = lean_apply_3(v___f_4638_, v_a_4651_, v___y_4639_, lean_box(0));
return v___x_4652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__2___boxed(lean_object* v___f_4653_, lean_object* v___y_4654_, lean_object* v_x_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Std_Http_Body_Stream_offer___lam__2(v___f_4653_, v___y_4654_, v_x_4655_);
lean_dec(v___y_4654_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__5(lean_object* v_toSend_4664_, lean_object* v_a_4665_, uint8_t v_closeAfter_4666_, lean_object* v___y_4667_, uint8_t v___y_4668_, lean_object* v___f_4669_, lean_object* v_x_4670_){
_start:
{
if (lean_obj_tag(v_x_4670_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4680_; 
lean_dec_ref(v___f_4669_);
lean_dec(v_a_4665_);
lean_dec_ref(v_toSend_4664_);
v_a_4672_ = lean_ctor_get(v_x_4670_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v_x_4670_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4674_ = v_x_4670_;
v_isShared_4675_ = v_isSharedCheck_4680_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v_x_4670_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4680_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
lean_object* v___x_4678_; 
v___x_4678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
return v___x_4678_;
}
}
}
else
{
lean_object* v_a_4681_; lean_object* v_pendingProducer_4682_; 
v_a_4681_ = lean_ctor_get(v_x_4670_, 0);
lean_inc(v_a_4681_);
lean_dec_ref_known(v_x_4670_, 1);
v_pendingProducer_4682_ = lean_ctor_get(v_a_4681_, 0);
if (lean_obj_tag(v_pendingProducer_4682_) == 0)
{
lean_object* v_pendingConsumer_4683_; lean_object* v_interestWaiter_4684_; lean_object* v_ended_4685_; lean_object* v_knownSize_4686_; lean_object* v_pendingIncomplete_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4700_; 
v_pendingConsumer_4683_ = lean_ctor_get(v_a_4681_, 1);
v_interestWaiter_4684_ = lean_ctor_get(v_a_4681_, 2);
v_ended_4685_ = lean_ctor_get(v_a_4681_, 3);
v_knownSize_4686_ = lean_ctor_get(v_a_4681_, 4);
v_pendingIncomplete_4687_ = lean_ctor_get(v_a_4681_, 5);
v_isSharedCheck_4700_ = !lean_is_exclusive(v_a_4681_);
if (v_isSharedCheck_4700_ == 0)
{
lean_object* v_unused_4701_; 
v_unused_4701_ = lean_ctor_get(v_a_4681_, 0);
lean_dec(v_unused_4701_);
v___x_4689_ = v_a_4681_;
v_isShared_4690_ = v_isSharedCheck_4700_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_pendingIncomplete_4687_);
lean_inc(v_knownSize_4686_);
lean_inc(v_ended_4685_);
lean_inc(v_interestWaiter_4684_);
lean_inc(v_pendingConsumer_4683_);
lean_dec(v_a_4681_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4700_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4694_; 
v___x_4691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4691_, 0, v_toSend_4664_);
lean_ctor_set(v___x_4691_, 1, v_a_4665_);
v___x_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 0, v___x_4692_);
v___x_4694_ = v___x_4689_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v___x_4692_);
lean_ctor_set(v_reuseFailAlloc_4699_, 1, v_pendingConsumer_4683_);
lean_ctor_set(v_reuseFailAlloc_4699_, 2, v_interestWaiter_4684_);
lean_ctor_set(v_reuseFailAlloc_4699_, 3, v_ended_4685_);
lean_ctor_set(v_reuseFailAlloc_4699_, 4, v_knownSize_4686_);
lean_ctor_set(v_reuseFailAlloc_4699_, 5, v_pendingIncomplete_4687_);
v___x_4694_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
lean_ctor_set_uint8(v___x_4694_, sizeof(void*)*6, v_closeAfter_4666_);
v___x_4695_ = lean_unsigned_to_nat(0u);
v___x_4696_ = lean_st_ref_swap(v___y_4667_, v___x_4694_);
lean_dec(v___x_4696_);
v___x_4697_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4698_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4695_, v___y_4668_, v___x_4697_, v___f_4669_);
return v___x_4698_;
}
}
}
else
{
lean_object* v___x_4702_; 
lean_dec(v_a_4681_);
lean_dec_ref(v___f_4669_);
lean_dec(v_a_4665_);
lean_dec_ref(v_toSend_4664_);
v___x_4702_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___lam__5___closed__2));
return v___x_4702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__5___boxed(lean_object* v_toSend_4703_, lean_object* v_a_4704_, lean_object* v_closeAfter_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___f_4708_, lean_object* v_x_4709_, lean_object* v___y_4710_){
_start:
{
uint8_t v_closeAfter_boxed_4711_; uint8_t v___y_8541__boxed_4712_; lean_object* v_res_4713_; 
v_closeAfter_boxed_4711_ = lean_unbox(v_closeAfter_4705_);
v___y_8541__boxed_4712_ = lean_unbox(v___y_4707_);
v_res_4713_ = l_Std_Http_Body_Stream_offer___lam__5(v_toSend_4703_, v_a_4704_, v_closeAfter_boxed_4711_, v___y_4706_, v___y_8541__boxed_4712_, v___f_4708_, v_x_4709_);
lean_dec(v___y_4706_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__4(lean_object* v_toSend_4714_, lean_object* v_a_4715_, uint8_t v_closeAfter_4716_, uint8_t v___y_4717_, lean_object* v___f_4718_, lean_object* v_____r_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___f_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4722_ = lean_box(v_closeAfter_4716_);
v___x_4723_ = lean_box(v___y_4717_);
lean_inc(v___y_4720_);
v___f_4724_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__5___boxed), 8, 6);
lean_closure_set(v___f_4724_, 0, v_toSend_4714_);
lean_closure_set(v___f_4724_, 1, v_a_4715_);
lean_closure_set(v___f_4724_, 2, v___x_4722_);
lean_closure_set(v___f_4724_, 3, v___y_4720_);
lean_closure_set(v___f_4724_, 4, v___x_4723_);
lean_closure_set(v___f_4724_, 5, v___f_4718_);
v___x_4725_ = lean_unsigned_to_nat(0u);
v___x_4726_ = lean_st_ref_get(v___y_4720_);
v___x_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
v___x_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
v___x_4729_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4725_, v___y_4717_, v___x_4728_, v___f_4724_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__4___boxed(lean_object* v_toSend_4730_, lean_object* v_a_4731_, lean_object* v_closeAfter_4732_, lean_object* v___y_4733_, lean_object* v___f_4734_, lean_object* v_____r_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
uint8_t v_closeAfter_boxed_4738_; uint8_t v___y_8615__boxed_4739_; lean_object* v_res_4740_; 
v_closeAfter_boxed_4738_ = lean_unbox(v_closeAfter_4732_);
v___y_8615__boxed_4739_ = lean_unbox(v___y_4733_);
v_res_4740_ = l_Std_Http_Body_Stream_offer___lam__4(v_toSend_4730_, v_a_4731_, v_closeAfter_boxed_4738_, v___y_8615__boxed_4739_, v___f_4734_, v_____r_4735_, v___y_4736_);
lean_dec(v___y_4736_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__6(uint8_t v_closeAfter_4741_, lean_object* v___f_4742_, lean_object* v___y_4743_, uint8_t v___y_4744_, lean_object* v___f_4745_, lean_object* v_x_4746_){
_start:
{
if (lean_obj_tag(v_x_4746_) == 0)
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4756_; 
lean_dec_ref(v___f_4745_);
lean_dec_ref(v___f_4742_);
v_a_4748_ = lean_ctor_get(v_x_4746_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_x_4746_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4750_ = v_x_4746_;
v_isShared_4751_ = v_isSharedCheck_4756_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v_x_4746_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4756_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
lean_object* v___x_4754_; 
v___x_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
return v___x_4754_;
}
}
}
else
{
lean_dec_ref_known(v_x_4746_, 1);
if (v_closeAfter_4741_ == 0)
{
lean_object* v___x_4757_; lean_object* v___x_4758_; 
lean_dec_ref(v___f_4745_);
v___x_4757_ = lean_box(0);
lean_inc(v___y_4743_);
v___x_4758_ = lean_apply_3(v___f_4742_, v___x_4757_, v___y_4743_, lean_box(0));
return v___x_4758_;
}
else
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_dec_ref(v___f_4742_);
v___x_4759_ = lean_box(0);
v___x_4760_ = lean_unsigned_to_nat(0u);
v___x_4761_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___x_4759_, v___y_4743_);
v___x_4762_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4760_, v___y_4744_, v___x_4761_, v___f_4745_);
return v___x_4762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__6___boxed(lean_object* v_closeAfter_4763_, lean_object* v___f_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___f_4767_, lean_object* v_x_4768_, lean_object* v___y_4769_){
_start:
{
uint8_t v_closeAfter_boxed_4770_; uint8_t v___y_8650__boxed_4771_; lean_object* v_res_4772_; 
v_closeAfter_boxed_4770_ = lean_unbox(v_closeAfter_4763_);
v___y_8650__boxed_4771_ = lean_unbox(v___y_4766_);
v_res_4772_ = l_Std_Http_Body_Stream_offer___lam__6(v_closeAfter_boxed_4770_, v___f_4764_, v___y_4765_, v___y_8650__boxed_4771_, v___f_4767_, v_x_4768_);
lean_dec(v___y_4765_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__7(lean_object* v___f_4773_, lean_object* v___y_4774_, lean_object* v_toSend_4775_, uint8_t v___y_4776_, lean_object* v___f_4777_, lean_object* v_x_4778_){
_start:
{
if (lean_obj_tag(v_x_4778_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4788_; 
lean_dec_ref(v___f_4777_);
lean_dec_ref(v___f_4773_);
v_a_4780_ = lean_ctor_get(v_x_4778_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_x_4778_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4782_ = v_x_4778_;
v_isShared_4783_ = v_isSharedCheck_4788_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v_x_4778_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4788_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4786_; 
v___x_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
return v___x_4786_;
}
}
}
else
{
lean_object* v_a_4789_; uint8_t v___x_4790_; 
v_a_4789_ = lean_ctor_get(v_x_4778_, 0);
lean_inc(v_a_4789_);
lean_dec_ref_known(v_x_4778_, 1);
v___x_4790_ = lean_unbox(v_a_4789_);
lean_dec(v_a_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
lean_dec_ref(v___f_4777_);
v___x_4791_ = lean_box(0);
lean_inc(v___y_4774_);
v___x_4792_ = lean_apply_3(v___f_4773_, v___x_4791_, v___y_4774_, lean_box(0));
return v___x_4792_;
}
else
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v_pendingProducer_4795_; lean_object* v_pendingConsumer_4796_; lean_object* v_interestWaiter_4797_; lean_object* v_ended_4798_; lean_object* v_knownSize_4799_; lean_object* v_pendingIncomplete_4800_; uint8_t v_closeAfterProducer_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4812_; 
lean_dec_ref(v___f_4773_);
v___x_4793_ = lean_unsigned_to_nat(0u);
v___x_4794_ = lean_st_ref_take(v___y_4774_);
v_pendingProducer_4795_ = lean_ctor_get(v___x_4794_, 0);
v_pendingConsumer_4796_ = lean_ctor_get(v___x_4794_, 1);
v_interestWaiter_4797_ = lean_ctor_get(v___x_4794_, 2);
v_ended_4798_ = lean_ctor_get(v___x_4794_, 3);
v_knownSize_4799_ = lean_ctor_get(v___x_4794_, 4);
v_pendingIncomplete_4800_ = lean_ctor_get(v___x_4794_, 5);
v_closeAfterProducer_4801_ = lean_ctor_get_uint8(v___x_4794_, sizeof(void*)*6);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4803_ = v___x_4794_;
v_isShared_4804_ = v_isSharedCheck_4812_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_pendingIncomplete_4800_);
lean_inc(v_knownSize_4799_);
lean_inc(v_ended_4798_);
lean_inc(v_interestWaiter_4797_);
lean_inc(v_pendingConsumer_4796_);
lean_inc(v_pendingProducer_4795_);
lean_dec(v___x_4794_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4812_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4805_; lean_object* v___x_4807_; 
v___x_4805_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_4799_, v_toSend_4775_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 4, v___x_4805_);
v___x_4807_ = v___x_4803_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_pendingProducer_4795_);
lean_ctor_set(v_reuseFailAlloc_4811_, 1, v_pendingConsumer_4796_);
lean_ctor_set(v_reuseFailAlloc_4811_, 2, v_interestWaiter_4797_);
lean_ctor_set(v_reuseFailAlloc_4811_, 3, v_ended_4798_);
lean_ctor_set(v_reuseFailAlloc_4811_, 4, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4811_, 5, v_pendingIncomplete_4800_);
lean_ctor_set_uint8(v_reuseFailAlloc_4811_, sizeof(void*)*6, v_closeAfterProducer_4801_);
v___x_4807_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4808_ = lean_st_ref_put(v___y_4774_, v___x_4807_);
v___x_4809_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4810_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4793_, v___y_4776_, v___x_4809_, v___f_4777_);
return v___x_4810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__7___boxed(lean_object* v___f_4813_, lean_object* v___y_4814_, lean_object* v_toSend_4815_, lean_object* v___y_4816_, lean_object* v___f_4817_, lean_object* v_x_4818_, lean_object* v___y_4819_){
_start:
{
uint8_t v___y_8702__boxed_4820_; lean_object* v_res_4821_; 
v___y_8702__boxed_4820_ = lean_unbox(v___y_4816_);
v_res_4821_ = l_Std_Http_Body_Stream_offer___lam__7(v___f_4813_, v___y_4814_, v_toSend_4815_, v___y_8702__boxed_4820_, v___f_4817_, v_x_4818_);
lean_dec_ref(v_toSend_4815_);
lean_dec(v___y_4814_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__8(lean_object* v_toSend_4822_, lean_object* v_val_4823_, uint8_t v___y_4824_, lean_object* v___f_4825_, lean_object* v_x_4826_){
_start:
{
if (lean_obj_tag(v_x_4826_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4836_; 
lean_dec_ref(v___f_4825_);
lean_dec_ref(v_toSend_4822_);
v_a_4828_ = lean_ctor_get(v_x_4826_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v_x_4826_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4830_ = v_x_4826_;
v_isShared_4831_ = v_isSharedCheck_4836_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v_x_4826_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4836_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
return v___x_4834_;
}
}
}
else
{
lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4850_; 
v_isSharedCheck_4850_ = !lean_is_exclusive(v_x_4826_);
if (v_isSharedCheck_4850_ == 0)
{
lean_object* v_unused_4851_; 
v_unused_4851_ = lean_ctor_get(v_x_4826_, 0);
lean_dec(v_unused_4851_);
v___x_4838_ = v_x_4826_;
v_isShared_4839_ = v_isSharedCheck_4850_;
goto v_resetjp_4837_;
}
else
{
lean_dec(v_x_4826_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4850_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4840_; lean_object* v___x_4842_; 
v___x_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4840_, 0, v_toSend_4822_);
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 0, v___x_4840_);
v___x_4842_ = v___x_4838_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v___x_4840_);
v___x_4842_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
lean_object* v___x_4843_; uint8_t v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4843_ = lean_unsigned_to_nat(0u);
v___x_4844_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_4823_, v___x_4842_);
v___x_4845_ = lean_box(v___x_4844_);
v___x_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
v___x_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
v___x_4848_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4843_, v___y_4824_, v___x_4847_, v___f_4825_);
return v___x_4848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__8___boxed(lean_object* v_toSend_4852_, lean_object* v_val_4853_, lean_object* v___y_4854_, lean_object* v___f_4855_, lean_object* v_x_4856_, lean_object* v___y_4857_){
_start:
{
uint8_t v___y_8773__boxed_4858_; lean_object* v_res_4859_; 
v___y_8773__boxed_4858_ = lean_unbox(v___y_4854_);
v_res_4859_ = l_Std_Http_Body_Stream_offer___lam__8(v_toSend_4852_, v_val_4853_, v___y_8773__boxed_4858_, v___f_4855_, v_x_4856_);
lean_dec_ref(v_val_4853_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__9(lean_object* v_toSend_4866_, lean_object* v_a_4867_, uint8_t v_closeAfter_4868_, lean_object* v___f_4869_, lean_object* v___f_4870_, lean_object* v___y_4871_, lean_object* v___f_4872_, lean_object* v___f_4873_, lean_object* v___f_4874_, lean_object* v_x_4875_){
_start:
{
if (lean_obj_tag(v_x_4875_) == 0)
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4885_; 
lean_dec_ref(v___f_4874_);
lean_dec_ref(v___f_4873_);
lean_dec_ref(v___f_4872_);
lean_dec_ref(v___f_4870_);
lean_dec_ref(v___f_4869_);
lean_dec(v_a_4867_);
lean_dec_ref(v_toSend_4866_);
v_a_4877_ = lean_ctor_get(v_x_4875_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v_x_4875_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4879_ = v_x_4875_;
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v_x_4875_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4883_; 
v___x_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4886_; lean_object* v_pendingProducer_4887_; lean_object* v_pendingConsumer_4888_; lean_object* v_interestWaiter_4889_; lean_object* v_ended_4890_; lean_object* v_knownSize_4891_; lean_object* v_pendingIncomplete_4892_; uint8_t v_closeAfterProducer_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4933_; 
v_a_4886_ = lean_ctor_get(v_x_4875_, 0);
lean_inc(v_a_4886_);
lean_dec_ref_known(v_x_4875_, 1);
v_pendingProducer_4887_ = lean_ctor_get(v_a_4886_, 0);
v_pendingConsumer_4888_ = lean_ctor_get(v_a_4886_, 1);
v_interestWaiter_4889_ = lean_ctor_get(v_a_4886_, 2);
v_ended_4890_ = lean_ctor_get(v_a_4886_, 3);
v_knownSize_4891_ = lean_ctor_get(v_a_4886_, 4);
v_pendingIncomplete_4892_ = lean_ctor_get(v_a_4886_, 5);
v_closeAfterProducer_4893_ = lean_ctor_get_uint8(v_a_4886_, sizeof(void*)*6);
v_isSharedCheck_4933_ = !lean_is_exclusive(v_a_4886_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4895_ = v_a_4886_;
v_isShared_4896_ = v_isSharedCheck_4933_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_pendingIncomplete_4892_);
lean_inc(v_knownSize_4891_);
lean_inc(v_ended_4890_);
lean_inc(v_interestWaiter_4889_);
lean_inc(v_pendingConsumer_4888_);
lean_inc(v_pendingProducer_4887_);
lean_dec(v_a_4886_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4933_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
uint8_t v___y_4898_; 
if (lean_obj_tag(v_ended_4890_) == 0)
{
lean_object* v_data_4920_; lean_object* v_extensions_4921_; uint8_t v___x_4922_; 
v_data_4920_ = lean_ctor_get(v_toSend_4866_, 0);
v_extensions_4921_ = lean_ctor_get(v_toSend_4866_, 1);
v___x_4922_ = l_ByteArray_isEmpty(v_data_4920_);
if (v___x_4922_ == 0)
{
lean_dec_ref(v___f_4874_);
lean_dec_ref(v___f_4873_);
v___y_4898_ = v___x_4922_;
goto v___jp_4897_;
}
else
{
lean_object* v___x_4923_; lean_object* v___x_4924_; uint8_t v___x_4925_; 
v___x_4923_ = lean_array_get_size(v_extensions_4921_);
v___x_4924_ = lean_unsigned_to_nat(0u);
v___x_4925_ = lean_nat_dec_eq(v___x_4923_, v___x_4924_);
if (v___x_4925_ == 0)
{
lean_dec_ref(v___f_4874_);
lean_dec_ref(v___f_4873_);
v___y_4898_ = v___x_4925_;
goto v___jp_4897_;
}
else
{
lean_del_object(v___x_4895_);
lean_dec(v_pendingIncomplete_4892_);
lean_dec(v_knownSize_4891_);
lean_dec(v_interestWaiter_4889_);
lean_dec(v_pendingConsumer_4888_);
lean_dec(v_pendingProducer_4887_);
lean_dec_ref(v___f_4872_);
lean_dec_ref(v___f_4870_);
lean_dec_ref(v___f_4869_);
lean_dec(v_a_4867_);
lean_dec_ref(v_toSend_4866_);
if (v_closeAfter_4868_ == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
lean_dec_ref(v___f_4874_);
v___x_4926_ = lean_box(0);
lean_inc(v___y_4871_);
v___x_4927_ = lean_apply_3(v___f_4873_, v___x_4926_, v___y_4871_, lean_box(0));
return v___x_4927_;
}
else
{
uint8_t v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
lean_dec_ref(v___f_4873_);
v___x_4928_ = 0;
v___x_4929_ = lean_box(0);
v___x_4930_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReadyResult_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0_spec__0_spec__3(v___x_4929_, v___y_4871_);
v___x_4931_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4924_, v___x_4928_, v___x_4930_, v___f_4874_);
return v___x_4931_;
}
}
}
}
else
{
lean_object* v___x_4932_; 
lean_dec_ref_known(v_ended_4890_, 1);
lean_del_object(v___x_4895_);
lean_dec(v_pendingIncomplete_4892_);
lean_dec(v_knownSize_4891_);
lean_dec(v_interestWaiter_4889_);
lean_dec(v_pendingConsumer_4888_);
lean_dec(v_pendingProducer_4887_);
lean_dec_ref(v___f_4874_);
lean_dec_ref(v___f_4873_);
lean_dec_ref(v___f_4872_);
lean_dec_ref(v___f_4870_);
lean_dec_ref(v___f_4869_);
lean_dec(v_a_4867_);
lean_dec_ref(v_toSend_4866_);
v___x_4932_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___lam__9___closed__2));
return v___x_4932_;
}
v___jp_4897_:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___f_4901_; 
v___x_4899_ = lean_box(v_closeAfter_4868_);
v___x_4900_ = lean_box(v___y_4898_);
lean_inc_ref(v___f_4869_);
lean_inc(v_a_4867_);
lean_inc_ref(v_toSend_4866_);
v___f_4901_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__4___boxed), 8, 5);
lean_closure_set(v___f_4901_, 0, v_toSend_4866_);
lean_closure_set(v___f_4901_, 1, v_a_4867_);
lean_closure_set(v___f_4901_, 2, v___x_4899_);
lean_closure_set(v___f_4901_, 3, v___x_4900_);
lean_closure_set(v___f_4901_, 4, v___f_4869_);
if (lean_obj_tag(v_pendingConsumer_4888_) == 1)
{
lean_object* v_val_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___f_4905_; lean_object* v___x_4906_; lean_object* v___f_4907_; lean_object* v___x_4908_; lean_object* v___f_4909_; lean_object* v___x_4910_; lean_object* v___x_4912_; 
lean_dec_ref(v___f_4869_);
lean_dec(v_a_4867_);
v_val_4902_ = lean_ctor_get(v_pendingConsumer_4888_, 0);
lean_inc(v_val_4902_);
lean_dec_ref_known(v_pendingConsumer_4888_, 1);
v___x_4903_ = lean_box(v_closeAfter_4868_);
v___x_4904_ = lean_box(v___y_4898_);
lean_inc_n(v___y_4871_, 2);
v___f_4905_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__6___boxed), 7, 5);
lean_closure_set(v___f_4905_, 0, v___x_4903_);
lean_closure_set(v___f_4905_, 1, v___f_4870_);
lean_closure_set(v___f_4905_, 2, v___y_4871_);
lean_closure_set(v___f_4905_, 3, v___x_4904_);
lean_closure_set(v___f_4905_, 4, v___f_4872_);
v___x_4906_ = lean_box(v___y_4898_);
lean_inc_ref(v_toSend_4866_);
v___f_4907_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__7___boxed), 7, 5);
lean_closure_set(v___f_4907_, 0, v___f_4901_);
lean_closure_set(v___f_4907_, 1, v___y_4871_);
lean_closure_set(v___f_4907_, 2, v_toSend_4866_);
lean_closure_set(v___f_4907_, 3, v___x_4906_);
lean_closure_set(v___f_4907_, 4, v___f_4905_);
v___x_4908_ = lean_box(v___y_4898_);
v___f_4909_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4909_, 0, v_toSend_4866_);
lean_closure_set(v___f_4909_, 1, v_val_4902_);
lean_closure_set(v___f_4909_, 2, v___x_4908_);
lean_closure_set(v___f_4909_, 3, v___f_4907_);
v___x_4910_ = lean_box(0);
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 1, v___x_4910_);
v___x_4912_ = v___x_4895_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_pendingProducer_4887_);
lean_ctor_set(v_reuseFailAlloc_4917_, 1, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4917_, 2, v_interestWaiter_4889_);
lean_ctor_set(v_reuseFailAlloc_4917_, 3, v_ended_4890_);
lean_ctor_set(v_reuseFailAlloc_4917_, 4, v_knownSize_4891_);
lean_ctor_set(v_reuseFailAlloc_4917_, 5, v_pendingIncomplete_4892_);
lean_ctor_set_uint8(v_reuseFailAlloc_4917_, sizeof(void*)*6, v_closeAfterProducer_4893_);
v___x_4912_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4913_ = lean_unsigned_to_nat(0u);
v___x_4914_ = lean_st_ref_swap(v___y_4871_, v___x_4912_);
lean_dec(v___x_4914_);
v___x_4915_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_4916_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4913_, v___y_4898_, v___x_4915_, v___f_4909_);
return v___x_4916_;
}
}
else
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
lean_dec_ref(v___f_4901_);
lean_del_object(v___x_4895_);
lean_dec(v_pendingIncomplete_4892_);
lean_dec(v_knownSize_4891_);
lean_dec(v_ended_4890_);
lean_dec(v_interestWaiter_4889_);
lean_dec(v_pendingConsumer_4888_);
lean_dec(v_pendingProducer_4887_);
lean_dec_ref(v___f_4872_);
lean_dec_ref(v___f_4870_);
v___x_4918_ = lean_box(0);
v___x_4919_ = l_Std_Http_Body_Stream_offer___lam__4(v_toSend_4866_, v_a_4867_, v_closeAfter_4868_, v___y_4898_, v___f_4869_, v___x_4918_, v___y_4871_);
return v___x_4919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__9___boxed(lean_object* v_toSend_4934_, lean_object* v_a_4935_, lean_object* v_closeAfter_4936_, lean_object* v___f_4937_, lean_object* v___f_4938_, lean_object* v___y_4939_, lean_object* v___f_4940_, lean_object* v___f_4941_, lean_object* v___f_4942_, lean_object* v_x_4943_, lean_object* v___y_4944_){
_start:
{
uint8_t v_closeAfter_boxed_4945_; lean_object* v_res_4946_; 
v_closeAfter_boxed_4945_ = lean_unbox(v_closeAfter_4936_);
v_res_4946_ = l_Std_Http_Body_Stream_offer___lam__9(v_toSend_4934_, v_a_4935_, v_closeAfter_boxed_4945_, v___f_4937_, v___f_4938_, v___y_4939_, v___f_4940_, v___f_4941_, v___f_4942_, v_x_4943_);
lean_dec(v___y_4939_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__10(lean_object* v___y_4947_, lean_object* v___f_4948_, lean_object* v_x_4949_){
_start:
{
if (lean_obj_tag(v_x_4949_) == 0)
{
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4959_; 
lean_dec_ref(v___f_4948_);
v_a_4951_ = lean_ctor_get(v_x_4949_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v_x_4949_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4953_ = v_x_4949_;
v_isShared_4954_ = v_isSharedCheck_4959_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v_x_4949_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4959_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v___x_4956_; 
if (v_isShared_4954_ == 0)
{
v___x_4956_ = v___x_4953_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4951_);
v___x_4956_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4955_;
}
v_reusejp_4955_:
{
lean_object* v___x_4957_; 
v___x_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4956_);
return v___x_4957_;
}
}
}
else
{
lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4971_; 
v_isSharedCheck_4971_ = !lean_is_exclusive(v_x_4949_);
if (v_isSharedCheck_4971_ == 0)
{
lean_object* v_unused_4972_; 
v_unused_4972_ = lean_ctor_get(v_x_4949_, 0);
lean_dec(v_unused_4972_);
v___x_4961_ = v_x_4949_;
v_isShared_4962_ = v_isSharedCheck_4971_;
goto v_resetjp_4960_;
}
else
{
lean_dec(v_x_4949_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4971_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4963_; uint8_t v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4967_; 
v___x_4963_ = lean_unsigned_to_nat(0u);
v___x_4964_ = 0;
v___x_4965_ = lean_st_ref_get(v___y_4947_);
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 0, v___x_4965_);
v___x_4967_ = v___x_4961_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v___x_4965_);
v___x_4967_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4967_);
v___x_4969_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4963_, v___x_4964_, v___x_4968_, v___f_4948_);
return v___x_4969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__10___boxed(lean_object* v___y_4973_, lean_object* v___f_4974_, lean_object* v_x_4975_, lean_object* v___y_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Std_Http_Body_Stream_offer___lam__10(v___y_4973_, v___f_4974_, v_x_4975_);
lean_dec(v___y_4973_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__11(lean_object* v___f_4978_, lean_object* v___f_4979_, lean_object* v_toSend_4980_, lean_object* v_a_4981_, uint8_t v_closeAfter_4982_, lean_object* v___f_4983_, lean_object* v___y_4984_){
_start:
{
lean_object* v___f_4986_; lean_object* v___f_4987_; lean_object* v___x_4988_; lean_object* v___f_4989_; lean_object* v___f_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
lean_inc_n(v___y_4984_, 4);
lean_inc_ref(v___f_4978_);
v___f_4986_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4986_, 0, v___f_4978_);
lean_closure_set(v___f_4986_, 1, v___y_4984_);
lean_inc_ref(v___f_4979_);
v___f_4987_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4987_, 0, v___f_4979_);
lean_closure_set(v___f_4987_, 1, v___y_4984_);
v___x_4988_ = lean_box(v_closeAfter_4982_);
v___f_4989_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__9___boxed), 11, 9);
lean_closure_set(v___f_4989_, 0, v_toSend_4980_);
lean_closure_set(v___f_4989_, 1, v_a_4981_);
lean_closure_set(v___f_4989_, 2, v___x_4988_);
lean_closure_set(v___f_4989_, 3, v___f_4983_);
lean_closure_set(v___f_4989_, 4, v___f_4979_);
lean_closure_set(v___f_4989_, 5, v___y_4984_);
lean_closure_set(v___f_4989_, 6, v___f_4987_);
lean_closure_set(v___f_4989_, 7, v___f_4978_);
lean_closure_set(v___f_4989_, 8, v___f_4986_);
v___f_4990_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__10___boxed), 4, 2);
lean_closure_set(v___f_4990_, 0, v___y_4984_);
lean_closure_set(v___f_4990_, 1, v___f_4989_);
v___x_4991_ = lean_unsigned_to_nat(0u);
v___x_4992_ = 0;
v___x_4993_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_4984_);
v___x_4994_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4991_, v___x_4992_, v___x_4993_, v___f_4990_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__11___boxed(lean_object* v___f_4995_, lean_object* v___f_4996_, lean_object* v_toSend_4997_, lean_object* v_a_4998_, lean_object* v_closeAfter_4999_, lean_object* v___f_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
uint8_t v_closeAfter_boxed_5003_; lean_object* v_res_5004_; 
v_closeAfter_boxed_5003_ = lean_unbox(v_closeAfter_4999_);
v_res_5004_ = l_Std_Http_Body_Stream_offer___lam__11(v___f_4995_, v___f_4996_, v_toSend_4997_, v_a_4998_, v_closeAfter_boxed_5003_, v___f_5000_, v___y_5001_);
lean_dec(v___y_5001_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__12(lean_object* v___f_5005_, lean_object* v___f_5006_, lean_object* v_toSend_5007_, uint8_t v_closeAfter_5008_, lean_object* v___f_5009_, lean_object* v_stream_5010_, lean_object* v___f_5011_, lean_object* v_x_5012_){
_start:
{
if (lean_obj_tag(v_x_5012_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5022_; 
lean_dec_ref(v___f_5011_);
lean_dec_ref(v_stream_5010_);
lean_dec_ref(v___f_5009_);
lean_dec_ref(v_toSend_5007_);
lean_dec_ref(v___f_5006_);
lean_dec_ref(v___f_5005_);
v_a_5014_ = lean_ctor_get(v_x_5012_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v_x_5012_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5016_ = v_x_5012_;
v_isShared_5017_ = v_isSharedCheck_5022_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v_x_5012_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5022_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5020_; 
v___x_5020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5019_);
return v___x_5020_;
}
}
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5024_; lean_object* v___f_5025_; lean_object* v___x_5026_; uint8_t v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v_a_5023_ = lean_ctor_get(v_x_5012_, 0);
lean_inc(v_a_5023_);
lean_dec_ref_known(v_x_5012_, 1);
v___x_5024_ = lean_box(v_closeAfter_5008_);
v___f_5025_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__11___boxed), 8, 6);
lean_closure_set(v___f_5025_, 0, v___f_5005_);
lean_closure_set(v___f_5025_, 1, v___f_5006_);
lean_closure_set(v___f_5025_, 2, v_toSend_5007_);
lean_closure_set(v___f_5025_, 3, v_a_5023_);
lean_closure_set(v___f_5025_, 4, v___x_5024_);
lean_closure_set(v___f_5025_, 5, v___f_5009_);
v___x_5026_ = lean_unsigned_to_nat(0u);
v___x_5027_ = 0;
v___x_5028_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_5010_, v___f_5025_);
v___x_5029_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5026_, v___x_5027_, v___x_5028_, v___f_5011_);
return v___x_5029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__12___boxed(lean_object* v___f_5030_, lean_object* v___f_5031_, lean_object* v_toSend_5032_, lean_object* v_closeAfter_5033_, lean_object* v___f_5034_, lean_object* v_stream_5035_, lean_object* v___f_5036_, lean_object* v_x_5037_, lean_object* v___y_5038_){
_start:
{
uint8_t v_closeAfter_boxed_5039_; lean_object* v_res_5040_; 
v_closeAfter_boxed_5039_ = lean_unbox(v_closeAfter_5033_);
v_res_5040_ = l_Std_Http_Body_Stream_offer___lam__12(v___f_5030_, v___f_5031_, v_toSend_5032_, v_closeAfter_boxed_5039_, v___f_5034_, v_stream_5035_, v___f_5036_, v_x_5037_);
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__13(lean_object* v___f_5041_, lean_object* v___f_5042_, uint8_t v_closeAfter_5043_, lean_object* v___f_5044_, lean_object* v_stream_5045_, lean_object* v___f_5046_, lean_object* v_toSend_5047_){
_start:
{
lean_object* v___x_5049_; lean_object* v___f_5050_; lean_object* v___x_5051_; uint8_t v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5049_ = lean_box(v_closeAfter_5043_);
v___f_5050_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__12___boxed), 9, 7);
lean_closure_set(v___f_5050_, 0, v___f_5041_);
lean_closure_set(v___f_5050_, 1, v___f_5042_);
lean_closure_set(v___f_5050_, 2, v_toSend_5047_);
lean_closure_set(v___f_5050_, 3, v___x_5049_);
lean_closure_set(v___f_5050_, 4, v___f_5044_);
lean_closure_set(v___f_5050_, 5, v_stream_5045_);
lean_closure_set(v___f_5050_, 6, v___f_5046_);
v___x_5051_ = lean_unsigned_to_nat(0u);
v___x_5052_ = 0;
v___x_5053_ = lean_io_promise_new();
v___x_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5053_);
v___x_5055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5055_, 0, v___x_5054_);
v___x_5056_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5051_, v___x_5052_, v___x_5055_, v___f_5050_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__13___boxed(lean_object* v___f_5057_, lean_object* v___f_5058_, lean_object* v_closeAfter_5059_, lean_object* v___f_5060_, lean_object* v_stream_5061_, lean_object* v___f_5062_, lean_object* v_toSend_5063_, lean_object* v___y_5064_){
_start:
{
uint8_t v_closeAfter_boxed_5065_; lean_object* v_res_5066_; 
v_closeAfter_boxed_5065_ = lean_unbox(v_closeAfter_5059_);
v_res_5066_ = l_Std_Http_Body_Stream_offer___lam__13(v___f_5057_, v___f_5058_, v_closeAfter_boxed_5065_, v___f_5060_, v_stream_5061_, v___f_5062_, v_toSend_5063_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__14(lean_object* v___f_5067_, lean_object* v_x_5068_){
_start:
{
if (lean_obj_tag(v_x_5068_) == 0)
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5078_; 
lean_dec_ref(v___f_5067_);
v_a_5070_ = lean_ctor_get(v_x_5068_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v_x_5068_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5072_ = v_x_5068_;
v_isShared_5073_ = v_isSharedCheck_5078_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v_x_5068_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5078_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5073_ == 0)
{
v___x_5075_ = v___x_5072_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5070_);
v___x_5075_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
lean_object* v___x_5076_; 
v___x_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5075_);
return v___x_5076_;
}
}
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5080_; 
v_a_5079_ = lean_ctor_get(v_x_5068_, 0);
lean_inc(v_a_5079_);
lean_dec_ref_known(v_x_5068_, 1);
v___x_5080_ = lean_apply_2(v___f_5067_, v_a_5079_, lean_box(0));
return v___x_5080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__14___boxed(lean_object* v___f_5081_, lean_object* v_x_5082_, lean_object* v___y_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Std_Http_Body_Stream_offer___lam__14(v___f_5081_, v_x_5082_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__16(lean_object* v___f_5085_, lean_object* v___f_5086_, lean_object* v_x_5087_){
_start:
{
if (lean_obj_tag(v_x_5087_) == 0)
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5097_; 
lean_dec_ref(v___f_5086_);
lean_dec_ref(v___f_5085_);
v_a_5089_ = lean_ctor_get(v_x_5087_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v_x_5087_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5091_ = v_x_5087_;
v_isShared_5092_ = v_isSharedCheck_5097_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v_x_5087_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5097_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5089_);
v___x_5094_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5095_; 
v___x_5095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5095_, 0, v___x_5094_);
return v___x_5095_;
}
}
}
else
{
lean_object* v_a_5098_; 
v_a_5098_ = lean_ctor_get(v_x_5087_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v_x_5087_, 1);
if (lean_obj_tag(v_a_5098_) == 0)
{
lean_object* v_a_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5110_; 
lean_dec_ref(v___f_5086_);
v_a_5099_ = lean_ctor_get(v_a_5098_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v_a_5098_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5101_ = v_a_5098_;
v_isShared_5102_ = v_isSharedCheck_5110_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_a_5099_);
lean_dec(v_a_5098_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5110_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5103_; uint8_t v___x_5104_; lean_object* v___x_5106_; 
v___x_5103_ = lean_unsigned_to_nat(0u);
v___x_5104_ = 0;
if (v_isShared_5102_ == 0)
{
v___x_5106_ = v___x_5101_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5099_);
v___x_5106_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
v___x_5108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5103_, v___x_5104_, v___x_5107_, v___f_5085_);
return v___x_5108_;
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5130_; 
lean_dec_ref(v___f_5085_);
v_a_5111_ = lean_ctor_get(v_a_5098_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v_a_5098_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5113_ = v_a_5098_;
v_isShared_5114_ = v_isSharedCheck_5130_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v_a_5098_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5130_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
if (lean_obj_tag(v_a_5111_) == 0)
{
lean_object* v___x_5115_; 
lean_del_object(v___x_5113_);
lean_dec_ref(v___f_5086_);
v___x_5115_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_5115_;
}
else
{
lean_object* v_val_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5129_; 
v_val_5116_ = lean_ctor_get(v_a_5111_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v_a_5111_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5118_ = v_a_5111_;
v_isShared_5119_ = v_isSharedCheck_5129_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_val_5116_);
lean_dec(v_a_5111_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5129_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5120_; uint8_t v___x_5121_; lean_object* v___x_5123_; 
v___x_5120_ = lean_unsigned_to_nat(0u);
v___x_5121_ = 0;
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 0, v_val_5116_);
v___x_5123_ = v___x_5113_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_val_5116_);
v___x_5123_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
lean_object* v___x_5125_; 
if (v_isShared_5119_ == 0)
{
lean_ctor_set_tag(v___x_5118_, 0);
lean_ctor_set(v___x_5118_, 0, v___x_5123_);
v___x_5125_ = v___x_5118_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v___x_5123_);
v___x_5125_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
lean_object* v___x_5126_; 
v___x_5126_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5120_, v___x_5121_, v___x_5125_, v___f_5086_);
return v___x_5126_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___lam__16___boxed(lean_object* v___f_5131_, lean_object* v___f_5132_, lean_object* v_x_5133_, lean_object* v___y_5134_){
_start:
{
lean_object* v_res_5135_; 
v_res_5135_ = l_Std_Http_Body_Stream_offer___lam__16(v___f_5131_, v___f_5132_, v_x_5133_);
return v_res_5135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer(lean_object* v_stream_5139_, lean_object* v_chunk_5140_, uint8_t v_incomplete_5141_, uint8_t v_closeAfter_5142_){
_start:
{
lean_object* v___f_5144_; lean_object* v___f_5145_; lean_object* v___f_5146_; lean_object* v___x_5147_; lean_object* v___f_5148_; lean_object* v___f_5149_; lean_object* v___f_5150_; uint8_t v___y_5152_; 
v___f_5144_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___closed__0));
v___f_5145_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___closed__1));
v___f_5146_ = ((lean_object*)(l_Std_Http_Body_Stream_offer___closed__2));
v___x_5147_ = lean_box(v_closeAfter_5142_);
lean_inc_ref(v_stream_5139_);
v___f_5148_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__13___boxed), 8, 6);
lean_closure_set(v___f_5148_, 0, v___f_5145_);
lean_closure_set(v___f_5148_, 1, v___f_5145_);
lean_closure_set(v___f_5148_, 2, v___x_5147_);
lean_closure_set(v___f_5148_, 3, v___f_5144_);
lean_closure_set(v___f_5148_, 4, v_stream_5139_);
lean_closure_set(v___f_5148_, 5, v___f_5146_);
v___f_5149_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__14___boxed), 3, 1);
lean_closure_set(v___f_5149_, 0, v___f_5148_);
lean_inc_ref(v___f_5149_);
v___f_5150_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_offer___lam__16___boxed), 4, 2);
lean_closure_set(v___f_5150_, 0, v___f_5149_);
lean_closure_set(v___f_5150_, 1, v___f_5149_);
if (v_incomplete_5141_ == 0)
{
v___y_5152_ = v_incomplete_5141_;
goto v___jp_5151_;
}
else
{
if (v_closeAfter_5142_ == 0)
{
v___y_5152_ = v_incomplete_5141_;
goto v___jp_5151_;
}
else
{
uint8_t v___x_5159_; 
v___x_5159_ = 0;
v___y_5152_ = v___x_5159_;
goto v___jp_5151_;
}
}
v___jp_5151_:
{
lean_object* v___x_5153_; uint8_t v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; 
v___x_5153_ = lean_unsigned_to_nat(0u);
v___x_5154_ = 0;
v___x_5155_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(v_stream_5139_, v_chunk_5140_, v___y_5152_);
v___x_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5156_, 0, v___x_5155_);
v___x_5157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5156_);
v___x_5158_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5153_, v___x_5154_, v___x_5157_, v___f_5150_);
return v___x_5158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_offer___boxed(lean_object* v_stream_5160_, lean_object* v_chunk_5161_, lean_object* v_incomplete_5162_, lean_object* v_closeAfter_5163_, lean_object* v_a_5164_){
_start:
{
uint8_t v_incomplete_boxed_5165_; uint8_t v_closeAfter_boxed_5166_; lean_object* v_res_5167_; 
v_incomplete_boxed_5165_ = lean_unbox(v_incomplete_5162_);
v_closeAfter_boxed_5166_ = lean_unbox(v_closeAfter_5163_);
v_res_5167_ = l_Std_Http_Body_Stream_offer(v_stream_5160_, v_chunk_5161_, v_incomplete_boxed_5165_, v_closeAfter_boxed_5166_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(lean_object* v_x_5168_){
_start:
{
uint8_t v___y_5171_; 
if (lean_obj_tag(v_x_5168_) == 0)
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5183_; 
v_a_5175_ = lean_ctor_get(v_x_5168_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v_x_5168_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5177_ = v_x_5168_;
v_isShared_5178_ = v_isSharedCheck_5183_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v_x_5168_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5183_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
if (v_isShared_5178_ == 0)
{
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
lean_object* v___x_5181_; 
v___x_5181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5180_);
return v___x_5181_;
}
}
}
else
{
lean_object* v_a_5184_; lean_object* v_pendingConsumer_5185_; 
v_a_5184_ = lean_ctor_get(v_x_5168_, 0);
lean_inc(v_a_5184_);
lean_dec_ref_known(v_x_5168_, 1);
v_pendingConsumer_5185_ = lean_ctor_get(v_a_5184_, 1);
lean_inc(v_pendingConsumer_5185_);
lean_dec(v_a_5184_);
if (lean_obj_tag(v_pendingConsumer_5185_) == 0)
{
uint8_t v___x_5186_; 
v___x_5186_ = 0;
v___y_5171_ = v___x_5186_;
goto v___jp_5170_;
}
else
{
uint8_t v___x_5187_; 
lean_dec_ref_known(v_pendingConsumer_5185_, 1);
v___x_5187_ = 1;
v___y_5171_ = v___x_5187_;
goto v___jp_5170_;
}
}
v___jp_5170_:
{
lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
v___x_5172_ = lean_box(v___y_5171_);
v___x_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5173_, 0, v___x_5172_);
v___x_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5174_, 0, v___x_5173_);
return v___x_5174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(lean_object* v_x_5188_, lean_object* v___y_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_5188_);
return v_res_5190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(lean_object* v_a_5192_){
_start:
{
lean_object* v___f_5194_; lean_object* v___x_5195_; uint8_t v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; 
v___f_5194_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0));
v___x_5195_ = lean_unsigned_to_nat(0u);
v___x_5196_ = 0;
v___x_5197_ = lean_st_ref_get(v_a_5192_);
v___x_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5197_);
v___x_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5198_);
v___x_5200_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5195_, v___x_5196_, v___x_5199_, v___f_5194_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(lean_object* v_a_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_5201_);
lean_dec(v_a_5201_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0(lean_object* v___y_5204_, lean_object* v_x_5205_){
_start:
{
if (lean_obj_tag(v_x_5205_) == 0)
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5215_; 
v_a_5207_ = lean_ctor_get(v_x_5205_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v_x_5205_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5209_ = v_x_5205_;
v_isShared_5210_ = v_isSharedCheck_5215_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v_x_5205_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5215_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5212_; 
if (v_isShared_5210_ == 0)
{
v___x_5212_ = v___x_5209_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5207_);
v___x_5212_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
lean_object* v___x_5213_; 
v___x_5213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5213_, 0, v___x_5212_);
return v___x_5213_;
}
}
}
else
{
lean_object* v___x_5216_; 
lean_dec_ref_known(v_x_5205_, 1);
v___x_5216_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_5204_);
return v___x_5216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(lean_object* v___y_5217_, lean_object* v_x_5218_, lean_object* v___y_5219_){
_start:
{
lean_object* v_res_5220_; 
v_res_5220_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_5217_, v_x_5218_);
lean_dec(v___y_5217_);
return v_res_5220_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1(lean_object* v___y_5221_){
_start:
{
lean_object* v___f_5223_; lean_object* v___x_5224_; uint8_t v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
lean_inc(v___y_5221_);
v___f_5223_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_hasInterest___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5223_, 0, v___y_5221_);
v___x_5224_ = lean_unsigned_to_nat(0u);
v___x_5225_ = 0;
v___x_5226_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_5221_);
v___x_5227_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5224_, v___x_5225_, v___x_5226_, v___f_5223_);
return v___x_5227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_5228_);
lean_dec(v___y_5228_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object* v_stream_5232_){
_start:
{
lean_object* v___f_5234_; lean_object* v___x_5235_; 
v___f_5234_ = ((lean_object*)(l_Std_Http_Body_Stream_hasInterest___closed__0));
v___x_5235_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_5232_, v___f_5234_);
return v___x_5235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_hasInterest___boxed(lean_object* v_stream_5236_, lean_object* v_a_5237_){
_start:
{
lean_object* v_res_5238_; 
v_res_5238_ = l_Std_Http_Body_Stream_hasInterest(v_stream_5236_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(lean_object* v_lose_5239_, lean_object* v___y_5240_, uint8_t v___x_5241_, lean_object* v_promise_5242_, lean_object* v_x_5243_){
_start:
{
if (lean_obj_tag(v_x_5243_) == 0)
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5253_; 
lean_dec_ref(v_lose_5239_);
v_a_5245_ = lean_ctor_get(v_x_5243_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_x_5243_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5247_ = v_x_5243_;
v_isShared_5248_ = v_isSharedCheck_5253_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v_x_5243_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5253_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5245_);
v___x_5250_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
lean_object* v___x_5251_; 
v___x_5251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5250_);
return v___x_5251_;
}
}
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5267_; 
v_a_5254_ = lean_ctor_get(v_x_5243_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v_x_5243_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5256_ = v_x_5243_;
v_isShared_5257_ = v_isSharedCheck_5267_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v_x_5243_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5267_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
uint8_t v___x_5258_; 
v___x_5258_ = lean_unbox(v_a_5254_);
lean_dec(v_a_5254_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; 
lean_del_object(v___x_5256_);
lean_inc(v___y_5240_);
v___x_5259_ = lean_apply_2(v_lose_5239_, v___y_5240_, lean_box(0));
return v___x_5259_;
}
else
{
lean_object* v___x_5260_; lean_object* v___x_5262_; 
lean_dec_ref(v_lose_5239_);
v___x_5260_ = lean_box(v___x_5241_);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 0, v___x_5260_);
v___x_5262_ = v___x_5256_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5260_);
v___x_5262_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
v___x_5263_ = lean_io_promise_resolve(v___x_5262_, v_promise_5242_);
v___x_5264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5263_);
v___x_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5265_, 0, v___x_5264_);
return v___x_5265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(lean_object* v_lose_5268_, lean_object* v___y_5269_, lean_object* v___x_5270_, lean_object* v_promise_5271_, lean_object* v_x_5272_, lean_object* v___y_5273_){
_start:
{
uint8_t v___x_4294__boxed_5274_; lean_object* v_res_5275_; 
v___x_4294__boxed_5274_ = lean_unbox(v___x_5270_);
v_res_5275_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(v_lose_5268_, v___y_5269_, v___x_4294__boxed_5274_, v_promise_5271_, v_x_5272_);
lean_dec(v_promise_5271_);
lean_dec(v___y_5269_);
return v_res_5275_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(lean_object* v_w_5276_, lean_object* v_lose_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v_finished_5280_; lean_object* v_promise_5281_; uint8_t v___x_5282_; lean_object* v___x_5283_; lean_object* v___f_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; uint8_t v___y_5288_; uint8_t v___x_5296_; 
v_finished_5280_ = lean_ctor_get(v_w_5276_, 0);
lean_inc(v_finished_5280_);
v_promise_5281_ = lean_ctor_get(v_w_5276_, 1);
lean_inc(v_promise_5281_);
lean_dec_ref(v_w_5276_);
v___x_5282_ = 0;
v___x_5283_ = lean_box(v___x_5282_);
lean_inc(v___y_5278_);
v___f_5284_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5284_, 0, v_lose_5277_);
lean_closure_set(v___f_5284_, 1, v___y_5278_);
lean_closure_set(v___f_5284_, 2, v___x_5283_);
lean_closure_set(v___f_5284_, 3, v_promise_5281_);
v___x_5285_ = lean_unsigned_to_nat(0u);
v___x_5286_ = lean_st_ref_take(v_finished_5280_);
v___x_5296_ = lean_unbox(v___x_5286_);
lean_dec(v___x_5286_);
if (v___x_5296_ == 0)
{
uint8_t v___x_5297_; 
v___x_5297_ = 1;
v___y_5288_ = v___x_5297_;
goto v___jp_5287_;
}
else
{
v___y_5288_ = v___x_5282_;
goto v___jp_5287_;
}
v___jp_5287_:
{
uint8_t v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5289_ = 1;
v___x_5290_ = lean_box(v___x_5289_);
v___x_5291_ = lean_st_ref_put(v_finished_5280_, v___x_5290_);
lean_dec(v_finished_5280_);
v___x_5292_ = lean_box(v___y_5288_);
v___x_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
v___x_5294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
v___x_5295_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5285_, v___x_5282_, v___x_5294_, v___f_5284_);
return v___x_5295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(lean_object* v_w_5298_, lean_object* v_lose_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_){
_start:
{
lean_object* v_res_5302_; 
v_res_5302_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_w_5298_, v_lose_5299_, v___y_5300_);
lean_dec(v___y_5300_);
return v_res_5302_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(lean_object* v_w_5303_, lean_object* v_lose_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v_finished_5307_; lean_object* v_promise_5308_; uint8_t v___x_5309_; lean_object* v___x_5310_; lean_object* v___f_5311_; lean_object* v___x_5312_; uint8_t v___x_5313_; lean_object* v___x_5314_; uint8_t v___y_5316_; uint8_t v___x_5323_; 
v_finished_5307_ = lean_ctor_get(v_w_5303_, 0);
lean_inc(v_finished_5307_);
v_promise_5308_ = lean_ctor_get(v_w_5303_, 1);
lean_inc(v_promise_5308_);
lean_dec_ref(v_w_5303_);
v___x_5309_ = 1;
v___x_5310_ = lean_box(v___x_5309_);
lean_inc(v___y_5305_);
v___f_5311_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5311_, 0, v_lose_5304_);
lean_closure_set(v___f_5311_, 1, v___y_5305_);
lean_closure_set(v___f_5311_, 2, v___x_5310_);
lean_closure_set(v___f_5311_, 3, v_promise_5308_);
v___x_5312_ = lean_unsigned_to_nat(0u);
v___x_5313_ = 0;
v___x_5314_ = lean_st_ref_take(v_finished_5307_);
v___x_5323_ = lean_unbox(v___x_5314_);
lean_dec(v___x_5314_);
if (v___x_5323_ == 0)
{
v___y_5316_ = v___x_5309_;
goto v___jp_5315_;
}
else
{
v___y_5316_ = v___x_5313_;
goto v___jp_5315_;
}
v___jp_5315_:
{
lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
v___x_5317_ = lean_box(v___x_5309_);
v___x_5318_ = lean_st_ref_put(v_finished_5307_, v___x_5317_);
lean_dec(v_finished_5307_);
v___x_5319_ = lean_box(v___y_5316_);
v___x_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5320_, 0, v___x_5319_);
v___x_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5320_);
v___x_5322_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5312_, v___x_5313_, v___x_5321_, v___f_5311_);
return v___x_5322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(lean_object* v_w_5324_, lean_object* v_lose_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_w_5324_, v_lose_5325_, v___y_5326_);
lean_dec(v___y_5326_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0(lean_object* v_x_5345_){
_start:
{
if (lean_obj_tag(v_x_5345_) == 0)
{
lean_object* v_a_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5355_; 
v_a_5347_ = lean_ctor_get(v_x_5345_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v_x_5345_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5349_ = v_x_5345_;
v_isShared_5350_ = v_isSharedCheck_5355_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_a_5347_);
lean_dec(v_x_5345_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5355_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5352_; 
if (v_isShared_5350_ == 0)
{
v___x_5352_ = v___x_5349_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5347_);
v___x_5352_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
lean_object* v___x_5353_; 
v___x_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5352_);
return v___x_5353_;
}
}
}
else
{
lean_object* v_a_5356_; lean_object* v_pendingConsumer_5357_; 
v_a_5356_ = lean_ctor_get(v_x_5345_, 0);
lean_inc(v_a_5356_);
lean_dec_ref_known(v_x_5345_, 1);
v_pendingConsumer_5357_ = lean_ctor_get(v_a_5356_, 1);
if (lean_obj_tag(v_pendingConsumer_5357_) == 0)
{
lean_object* v_ended_5358_; 
v_ended_5358_ = lean_ctor_get(v_a_5356_, 3);
lean_inc(v_ended_5358_);
lean_dec(v_a_5356_);
if (lean_obj_tag(v_ended_5358_) == 0)
{
lean_object* v___x_5359_; 
v___x_5359_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0));
return v___x_5359_;
}
else
{
lean_object* v___x_5360_; 
lean_dec_ref_known(v_ended_5358_, 1);
v___x_5360_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3));
return v___x_5360_;
}
}
else
{
lean_object* v___x_5361_; 
lean_dec(v_a_5356_);
v___x_5361_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6));
return v___x_5361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(lean_object* v_x_5362_, lean_object* v___y_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_5362_);
return v_res_5364_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3(lean_object* v_waiter_5372_, lean_object* v___y_5373_, lean_object* v_x_5374_){
_start:
{
if (lean_obj_tag(v_x_5374_) == 0)
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5384_; 
lean_dec_ref(v_waiter_5372_);
v_a_5376_ = lean_ctor_get(v_x_5374_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v_x_5374_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5378_ = v_x_5374_;
v_isShared_5379_ = v_isSharedCheck_5384_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v_x_5374_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5384_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5376_);
v___x_5381_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
lean_object* v___x_5382_; 
v___x_5382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5382_, 0, v___x_5381_);
return v___x_5382_;
}
}
}
else
{
lean_object* v_a_5385_; lean_object* v_pendingConsumer_5386_; 
v_a_5385_ = lean_ctor_get(v_x_5374_, 0);
lean_inc(v_a_5385_);
lean_dec_ref_known(v_x_5374_, 1);
v_pendingConsumer_5386_ = lean_ctor_get(v_a_5385_, 1);
lean_inc(v_pendingConsumer_5386_);
if (lean_obj_tag(v_pendingConsumer_5386_) == 0)
{
lean_object* v_ended_5387_; 
v_ended_5387_ = lean_ctor_get(v_a_5385_, 3);
lean_inc(v_ended_5387_);
if (lean_obj_tag(v_ended_5387_) == 0)
{
lean_object* v_interestWaiter_5388_; 
v_interestWaiter_5388_ = lean_ctor_get(v_a_5385_, 2);
if (lean_obj_tag(v_interestWaiter_5388_) == 0)
{
lean_object* v_pendingProducer_5389_; lean_object* v_knownSize_5390_; lean_object* v_pendingIncomplete_5391_; uint8_t v_closeAfterProducer_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5402_; 
v_pendingProducer_5389_ = lean_ctor_get(v_a_5385_, 0);
v_knownSize_5390_ = lean_ctor_get(v_a_5385_, 4);
v_pendingIncomplete_5391_ = lean_ctor_get(v_a_5385_, 5);
v_closeAfterProducer_5392_ = lean_ctor_get_uint8(v_a_5385_, sizeof(void*)*6);
v_isSharedCheck_5402_ = !lean_is_exclusive(v_a_5385_);
if (v_isSharedCheck_5402_ == 0)
{
lean_object* v_unused_5403_; lean_object* v_unused_5404_; lean_object* v_unused_5405_; 
v_unused_5403_ = lean_ctor_get(v_a_5385_, 3);
lean_dec(v_unused_5403_);
v_unused_5404_ = lean_ctor_get(v_a_5385_, 2);
lean_dec(v_unused_5404_);
v_unused_5405_ = lean_ctor_get(v_a_5385_, 1);
lean_dec(v_unused_5405_);
v___x_5394_ = v_a_5385_;
v_isShared_5395_ = v_isSharedCheck_5402_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_pendingIncomplete_5391_);
lean_inc(v_knownSize_5390_);
lean_inc(v_pendingProducer_5389_);
lean_dec(v_a_5385_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5402_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v___x_5396_; lean_object* v___x_5398_; 
v___x_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5396_, 0, v_waiter_5372_);
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 2, v___x_5396_);
v___x_5398_ = v___x_5394_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_pendingProducer_5389_);
lean_ctor_set(v_reuseFailAlloc_5401_, 1, v_pendingConsumer_5386_);
lean_ctor_set(v_reuseFailAlloc_5401_, 2, v___x_5396_);
lean_ctor_set(v_reuseFailAlloc_5401_, 3, v_ended_5387_);
lean_ctor_set(v_reuseFailAlloc_5401_, 4, v_knownSize_5390_);
lean_ctor_set(v_reuseFailAlloc_5401_, 5, v_pendingIncomplete_5391_);
lean_ctor_set_uint8(v_reuseFailAlloc_5401_, sizeof(void*)*6, v_closeAfterProducer_5392_);
v___x_5398_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5399_ = lean_st_ref_swap(v___y_5373_, v___x_5398_);
lean_dec(v___x_5399_);
v___x_5400_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_5400_;
}
}
}
else
{
lean_object* v___x_5406_; 
lean_dec(v_a_5385_);
lean_dec_ref(v_waiter_5372_);
v___x_5406_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3));
return v___x_5406_;
}
}
else
{
lean_object* v___f_5407_; lean_object* v___x_5408_; 
lean_dec_ref_known(v_ended_5387_, 1);
lean_dec(v_a_5385_);
v___f_5407_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_5408_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_5372_, v___f_5407_, v___y_5373_);
return v___x_5408_;
}
}
else
{
lean_object* v___f_5409_; lean_object* v___x_5410_; 
lean_dec_ref_known(v_pendingConsumer_5386_, 1);
lean_dec(v_a_5385_);
v___f_5409_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0));
v___x_5410_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_5372_, v___f_5409_, v___y_5373_);
return v___x_5410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(lean_object* v_waiter_5411_, lean_object* v___y_5412_, lean_object* v_x_5413_, lean_object* v___y_5414_){
_start:
{
lean_object* v_res_5415_; 
v_res_5415_ = l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_5411_, v___y_5412_, v_x_5413_);
lean_dec(v___y_5412_);
return v_res_5415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1(lean_object* v___y_5416_, lean_object* v___f_5417_, lean_object* v_x_5418_){
_start:
{
if (lean_obj_tag(v_x_5418_) == 0)
{
lean_object* v___x_5420_; 
lean_dec_ref(v___f_5417_);
v___x_5420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5420_, 0, v_x_5418_);
return v___x_5420_;
}
else
{
lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5432_; 
v_isSharedCheck_5432_ = !lean_is_exclusive(v_x_5418_);
if (v_isSharedCheck_5432_ == 0)
{
lean_object* v_unused_5433_; 
v_unused_5433_ = lean_ctor_get(v_x_5418_, 0);
lean_dec(v_unused_5433_);
v___x_5422_ = v_x_5418_;
v_isShared_5423_ = v_isSharedCheck_5432_;
goto v_resetjp_5421_;
}
else
{
lean_dec(v_x_5418_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5432_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5424_; uint8_t v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5428_; 
v___x_5424_ = lean_unsigned_to_nat(0u);
v___x_5425_ = 0;
v___x_5426_ = lean_st_ref_get(v___y_5416_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 0, v___x_5426_);
v___x_5428_ = v___x_5422_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v___x_5426_);
v___x_5428_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5428_);
v___x_5430_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5424_, v___x_5425_, v___x_5429_, v___f_5417_);
return v___x_5430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(lean_object* v___y_5434_, lean_object* v___f_5435_, lean_object* v_x_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_5434_, v___f_5435_, v_x_5436_);
lean_dec(v___y_5434_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2(lean_object* v_waiter_5439_, lean_object* v___y_5440_){
_start:
{
lean_object* v___f_5442_; lean_object* v___f_5443_; lean_object* v___x_5444_; uint8_t v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; 
lean_inc_n(v___y_5440_, 2);
v___f_5442_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__3___boxed), 4, 2);
lean_closure_set(v___f_5442_, 0, v_waiter_5439_);
lean_closure_set(v___f_5442_, 1, v___y_5440_);
v___f_5443_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5443_, 0, v___y_5440_);
lean_closure_set(v___f_5443_, 1, v___f_5442_);
v___x_5444_ = lean_unsigned_to_nat(0u);
v___x_5445_ = 0;
v___x_5446_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_5440_);
v___x_5447_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5444_, v___x_5445_, v___x_5446_, v___f_5443_);
return v___x_5447_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(lean_object* v_waiter_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v_res_5451_; 
v_res_5451_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_5448_, v___y_5449_);
lean_dec(v___y_5449_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4(lean_object* v_stream_5452_, lean_object* v_waiter_5453_){
_start:
{
lean_object* v___f_5455_; lean_object* v___x_5456_; 
v___f_5455_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5455_, 0, v_waiter_5453_);
v___x_5456_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_5452_, v___f_5455_);
return v___x_5456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(lean_object* v_stream_5457_, lean_object* v_waiter_5458_, lean_object* v___y_5459_){
_start:
{
lean_object* v_res_5460_; 
v_res_5460_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_5457_, v_waiter_5458_);
return v_res_5460_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5(lean_object* v___y_5461_, lean_object* v___f_5462_, lean_object* v_x_5463_){
_start:
{
if (lean_obj_tag(v_x_5463_) == 0)
{
lean_object* v_a_5465_; lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5473_; 
lean_dec_ref(v___f_5462_);
v_a_5465_ = lean_ctor_get(v_x_5463_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v_x_5463_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5467_ = v_x_5463_;
v_isShared_5468_ = v_isSharedCheck_5473_;
goto v_resetjp_5466_;
}
else
{
lean_inc(v_a_5465_);
lean_dec(v_x_5463_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5473_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
lean_object* v___x_5470_; 
if (v_isShared_5468_ == 0)
{
v___x_5470_ = v___x_5467_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5465_);
v___x_5470_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
lean_object* v___x_5471_; 
v___x_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5471_, 0, v___x_5470_);
return v___x_5471_;
}
}
}
else
{
lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5485_; 
v_isSharedCheck_5485_ = !lean_is_exclusive(v_x_5463_);
if (v_isSharedCheck_5485_ == 0)
{
lean_object* v_unused_5486_; 
v_unused_5486_ = lean_ctor_get(v_x_5463_, 0);
lean_dec(v_unused_5486_);
v___x_5475_ = v_x_5463_;
v_isShared_5476_ = v_isSharedCheck_5485_;
goto v_resetjp_5474_;
}
else
{
lean_dec(v_x_5463_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5485_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5477_; uint8_t v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5481_; 
v___x_5477_ = lean_unsigned_to_nat(0u);
v___x_5478_ = 0;
v___x_5479_ = lean_st_ref_get(v___y_5461_);
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 0, v___x_5479_);
v___x_5481_ = v___x_5475_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5479_);
v___x_5481_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5481_);
v___x_5483_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5477_, v___x_5478_, v___x_5482_, v___f_5462_);
return v___x_5483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(lean_object* v___y_5487_, lean_object* v___f_5488_, lean_object* v_x_5489_, lean_object* v___y_5490_){
_start:
{
lean_object* v_res_5491_; 
v_res_5491_ = l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_5487_, v___f_5488_, v_x_5489_);
lean_dec(v___y_5487_);
return v_res_5491_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6(lean_object* v___f_5492_, lean_object* v___y_5493_){
_start:
{
lean_object* v___f_5495_; lean_object* v___x_5496_; uint8_t v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
lean_inc(v___y_5493_);
v___f_5495_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_5495_, 0, v___y_5493_);
lean_closure_set(v___f_5495_, 1, v___f_5492_);
v___x_5496_ = lean_unsigned_to_nat(0u);
v___x_5497_ = 0;
v___x_5498_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_5493_);
v___x_5499_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5496_, v___x_5497_, v___x_5498_, v___f_5495_);
return v___x_5499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(lean_object* v___f_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_5500_, v___y_5501_);
lean_dec(v___y_5501_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object* v_stream_5507_){
_start:
{
lean_object* v___f_5508_; lean_object* v___f_5509_; lean_object* v___f_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; 
v___f_5508_ = ((lean_object*)(l_Std_Http_Body_Stream_recvSelector___closed__0));
lean_inc_ref_n(v_stream_5507_, 2);
v___f_5509_ = lean_alloc_closure((void*)(l_Std_Http_Body_Stream_interestSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_5509_, 0, v_stream_5507_);
v___f_5510_ = ((lean_object*)(l_Std_Http_Body_Stream_interestSelector___closed__1));
v___x_5511_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_5511_, 0, lean_box(0));
lean_closure_set(v___x_5511_, 1, lean_box(0));
lean_closure_set(v___x_5511_, 2, v_stream_5507_);
lean_closure_set(v___x_5511_, 3, v___f_5510_);
v___x_5512_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed), 5, 4);
lean_closure_set(v___x_5512_, 0, lean_box(0));
lean_closure_set(v___x_5512_, 1, lean_box(0));
lean_closure_set(v___x_5512_, 2, v_stream_5507_);
lean_closure_set(v___x_5512_, 3, v___f_5508_);
v___x_5513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5513_, 0, v___x_5511_);
lean_ctor_set(v___x_5513_, 1, v___f_5509_);
lean_ctor_set(v___x_5513_, 2, v___x_5512_);
return v___x_5513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0(lean_object* v_x_5514_, lean_object* v_x_5515_){
_start:
{
if (lean_obj_tag(v_x_5515_) == 0)
{
lean_object* v_a_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5525_; 
lean_dec_ref(v_x_5514_);
v_a_5517_ = lean_ctor_get(v_x_5515_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v_x_5515_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5519_ = v_x_5515_;
v_isShared_5520_ = v_isSharedCheck_5525_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_a_5517_);
lean_dec(v_x_5515_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5525_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5522_; 
if (v_isShared_5520_ == 0)
{
v___x_5522_ = v___x_5519_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5517_);
v___x_5522_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
lean_object* v___x_5523_; 
v___x_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5523_, 0, v___x_5522_);
return v___x_5523_;
}
}
}
else
{
lean_object* v___x_5526_; 
lean_dec_ref_known(v_x_5515_, 1);
v___x_5526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5526_, 0, v_x_5514_);
return v___x_5526_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__0___boxed(lean_object* v_x_5527_, lean_object* v_x_5528_, lean_object* v___y_5529_){
_start:
{
lean_object* v_res_5530_; 
v_res_5530_ = l_Std_Http_Body_stream___lam__0(v_x_5527_, v_x_5528_);
return v_res_5530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1(lean_object* v_a_5531_, lean_object* v_x_5532_){
_start:
{
if (lean_obj_tag(v_x_5532_) == 0)
{
lean_object* v_a_5534_; lean_object* v___x_5535_; 
v_a_5534_ = lean_ctor_get(v_x_5532_, 0);
lean_inc(v_a_5534_);
lean_dec_ref_known(v_x_5532_, 1);
v___x_5535_ = l_Std_Http_Body_Stream_closeWithError(v_a_5531_, v_a_5534_);
return v___x_5535_;
}
else
{
lean_object* v___x_5536_; 
lean_dec_ref(v_a_5531_);
v___x_5536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5536_, 0, v_x_5532_);
return v___x_5536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__1___boxed(lean_object* v_a_5537_, lean_object* v_x_5538_, lean_object* v___y_5539_){
_start:
{
lean_object* v_res_5540_; 
v_res_5540_ = l_Std_Http_Body_stream___lam__1(v_a_5537_, v_x_5538_);
return v_res_5540_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2(lean_object* v_a_5541_, lean_object* v_x_5542_){
_start:
{
if (lean_obj_tag(v_x_5542_) == 0)
{
lean_object* v___x_5544_; 
lean_dec_ref(v_a_5541_);
v___x_5544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5544_, 0, v_x_5542_);
return v___x_5544_;
}
else
{
lean_object* v___x_5545_; 
lean_dec_ref_known(v_x_5542_, 1);
v___x_5545_ = l_Std_Http_Body_Stream_close(v_a_5541_);
return v___x_5545_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__2___boxed(lean_object* v_a_5546_, lean_object* v_x_5547_, lean_object* v___y_5548_){
_start:
{
lean_object* v_res_5549_; 
v_res_5549_ = l_Std_Http_Body_stream___lam__2(v_a_5546_, v_x_5547_);
return v_res_5549_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3(lean_object* v_gen_5550_, lean_object* v_a_5551_, lean_object* v___x_5552_, uint8_t v___x_5553_, lean_object* v___f_5554_, lean_object* v___f_5555_){
_start:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; 
v___x_5557_ = lean_apply_2(v_gen_5550_, v_a_5551_, lean_box(0));
lean_inc(v___x_5552_);
v___x_5558_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5552_, v___x_5553_, v___x_5557_, v___f_5554_);
v___x_5559_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5552_, v___x_5553_, v___x_5558_, v___f_5555_);
return v___x_5559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__3___boxed(lean_object* v_gen_5560_, lean_object* v_a_5561_, lean_object* v___x_5562_, lean_object* v___x_5563_, lean_object* v___f_5564_, lean_object* v___f_5565_, lean_object* v___y_5566_){
_start:
{
uint8_t v___x_1066__boxed_5567_; lean_object* v_res_5568_; 
v___x_1066__boxed_5567_ = lean_unbox(v___x_5563_);
v_res_5568_ = l_Std_Http_Body_stream___lam__3(v_gen_5560_, v_a_5561_, v___x_5562_, v___x_1066__boxed_5567_, v___f_5564_, v___f_5565_);
return v_res_5568_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4(lean_object* v_gen_5569_, lean_object* v_a_5570_, lean_object* v___f_5571_, lean_object* v___f_5572_, lean_object* v___f_5573_, lean_object* v_x_5574_){
_start:
{
if (lean_obj_tag(v_x_5574_) == 0)
{
lean_object* v_a_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5584_; 
lean_dec_ref(v___f_5573_);
lean_dec_ref(v___f_5572_);
lean_dec_ref(v___f_5571_);
lean_dec_ref(v_a_5570_);
lean_dec_ref(v_gen_5569_);
v_a_5576_ = lean_ctor_get(v_x_5574_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v_x_5574_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5578_ = v_x_5574_;
v_isShared_5579_ = v_isSharedCheck_5584_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_a_5576_);
lean_dec(v_x_5574_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5584_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5581_; 
if (v_isShared_5579_ == 0)
{
v___x_5581_ = v___x_5578_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_a_5576_);
v___x_5581_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
lean_object* v___x_5582_; 
v___x_5582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
return v___x_5582_;
}
}
}
else
{
lean_object* v___x_5585_; uint8_t v___x_5586_; lean_object* v___x_5587_; lean_object* v___f_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
lean_dec_ref_known(v_x_5574_, 1);
v___x_5585_ = lean_unsigned_to_nat(0u);
v___x_5586_ = 0;
v___x_5587_ = lean_box(v___x_5586_);
v___f_5588_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__3___boxed), 7, 6);
lean_closure_set(v___f_5588_, 0, v_gen_5569_);
lean_closure_set(v___f_5588_, 1, v_a_5570_);
lean_closure_set(v___f_5588_, 2, v___x_5585_);
lean_closure_set(v___f_5588_, 3, v___x_5587_);
lean_closure_set(v___f_5588_, 4, v___f_5571_);
lean_closure_set(v___f_5588_, 5, v___f_5572_);
v___x_5589_ = lean_io_as_task(v___f_5588_, v___x_5585_);
lean_dec_ref(v___x_5589_);
v___x_5590_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
v___x_5591_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5585_, v___x_5586_, v___x_5590_, v___f_5573_);
return v___x_5591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__4___boxed(lean_object* v_gen_5592_, lean_object* v_a_5593_, lean_object* v___f_5594_, lean_object* v___f_5595_, lean_object* v___f_5596_, lean_object* v_x_5597_, lean_object* v___y_5598_){
_start:
{
lean_object* v_res_5599_; 
v_res_5599_ = l_Std_Http_Body_stream___lam__4(v_gen_5592_, v_a_5593_, v___f_5594_, v___f_5595_, v___f_5596_, v_x_5597_);
return v_res_5599_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5(lean_object* v___x_5600_, lean_object* v___y_5601_){
_start:
{
lean_object* v___x_5603_; lean_object* v_pendingProducer_5604_; lean_object* v_pendingConsumer_5605_; lean_object* v_interestWaiter_5606_; lean_object* v_ended_5607_; lean_object* v_pendingIncomplete_5608_; uint8_t v_closeAfterProducer_5609_; lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5618_; 
v___x_5603_ = lean_st_ref_take(v___y_5601_);
v_pendingProducer_5604_ = lean_ctor_get(v___x_5603_, 0);
v_pendingConsumer_5605_ = lean_ctor_get(v___x_5603_, 1);
v_interestWaiter_5606_ = lean_ctor_get(v___x_5603_, 2);
v_ended_5607_ = lean_ctor_get(v___x_5603_, 3);
v_pendingIncomplete_5608_ = lean_ctor_get(v___x_5603_, 5);
v_closeAfterProducer_5609_ = lean_ctor_get_uint8(v___x_5603_, sizeof(void*)*6);
v_isSharedCheck_5618_ = !lean_is_exclusive(v___x_5603_);
if (v_isSharedCheck_5618_ == 0)
{
lean_object* v_unused_5619_; 
v_unused_5619_ = lean_ctor_get(v___x_5603_, 4);
lean_dec(v_unused_5619_);
v___x_5611_ = v___x_5603_;
v_isShared_5612_ = v_isSharedCheck_5618_;
goto v_resetjp_5610_;
}
else
{
lean_inc(v_pendingIncomplete_5608_);
lean_inc(v_ended_5607_);
lean_inc(v_interestWaiter_5606_);
lean_inc(v_pendingConsumer_5605_);
lean_inc(v_pendingProducer_5604_);
lean_dec(v___x_5603_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5618_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v___x_5614_; 
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 4, v___x_5600_);
v___x_5614_ = v___x_5611_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_pendingProducer_5604_);
lean_ctor_set(v_reuseFailAlloc_5617_, 1, v_pendingConsumer_5605_);
lean_ctor_set(v_reuseFailAlloc_5617_, 2, v_interestWaiter_5606_);
lean_ctor_set(v_reuseFailAlloc_5617_, 3, v_ended_5607_);
lean_ctor_set(v_reuseFailAlloc_5617_, 4, v___x_5600_);
lean_ctor_set(v_reuseFailAlloc_5617_, 5, v_pendingIncomplete_5608_);
lean_ctor_set_uint8(v_reuseFailAlloc_5617_, sizeof(void*)*6, v_closeAfterProducer_5609_);
v___x_5614_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
lean_object* v___x_5615_; lean_object* v___x_5616_; 
v___x_5615_ = lean_st_ref_put(v___y_5601_, v___x_5614_);
v___x_5616_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_5616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__5___boxed(lean_object* v___x_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_){
_start:
{
lean_object* v_res_5623_; 
v_res_5623_ = l_Std_Http_Body_stream___lam__5(v___x_5620_, v___y_5621_);
lean_dec(v___y_5621_);
return v_res_5623_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6(lean_object* v_gen_5628_, lean_object* v_x_5629_){
_start:
{
if (lean_obj_tag(v_x_5629_) == 0)
{
lean_object* v___x_5631_; 
lean_dec_ref(v_gen_5628_);
v___x_5631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5631_, 0, v_x_5629_);
return v___x_5631_;
}
else
{
lean_object* v_a_5632_; lean_object* v___f_5633_; lean_object* v___f_5634_; lean_object* v___f_5635_; lean_object* v___f_5636_; lean_object* v___f_5637_; lean_object* v___x_5638_; uint8_t v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; 
v_a_5632_ = lean_ctor_get(v_x_5629_, 0);
lean_inc_n(v_a_5632_, 4);
v___f_5633_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5633_, 0, v_x_5629_);
v___f_5634_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__1___boxed), 3, 1);
lean_closure_set(v___f_5634_, 0, v_a_5632_);
v___f_5635_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5635_, 0, v_a_5632_);
v___f_5636_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__4___boxed), 7, 5);
lean_closure_set(v___f_5636_, 0, v_gen_5628_);
lean_closure_set(v___f_5636_, 1, v_a_5632_);
lean_closure_set(v___f_5636_, 2, v___f_5635_);
lean_closure_set(v___f_5636_, 3, v___f_5634_);
lean_closure_set(v___f_5636_, 4, v___f_5633_);
v___f_5637_ = ((lean_object*)(l_Std_Http_Body_stream___lam__6___closed__1));
v___x_5638_ = lean_unsigned_to_nat(0u);
v___x_5639_ = 0;
v___x_5640_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_5632_, v___f_5637_);
v___x_5641_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5638_, v___x_5639_, v___x_5640_, v___f_5636_);
return v___x_5641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___lam__6___boxed(lean_object* v_gen_5642_, lean_object* v_x_5643_, lean_object* v___y_5644_){
_start:
{
lean_object* v_res_5645_; 
v_res_5645_ = l_Std_Http_Body_stream___lam__6(v_gen_5642_, v_x_5643_);
return v_res_5645_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream(lean_object* v_gen_5646_){
_start:
{
lean_object* v___f_5648_; lean_object* v___x_5649_; uint8_t v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; 
v___f_5648_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__6___boxed), 3, 1);
lean_closure_set(v___f_5648_, 0, v_gen_5646_);
v___x_5649_ = lean_unsigned_to_nat(0u);
v___x_5650_ = 0;
v___x_5651_ = l_Std_Http_Body_mkStream();
v___x_5652_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5649_, v___x_5650_, v___x_5651_, v___f_5648_);
return v___x_5652_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_stream___boxed(lean_object* v_gen_5653_, lean_object* v_a_5654_){
_start:
{
lean_object* v_res_5655_; 
v_res_5655_ = l_Std_Http_Body_stream(v_gen_5653_);
return v_res_5655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0(lean_object* v___x_5656_, lean_object* v_content_5657_, lean_object* v_s_5658_, lean_object* v_x_5659_){
_start:
{
if (lean_obj_tag(v_x_5659_) == 0)
{
lean_object* v___x_5661_; 
lean_dec_ref(v_s_5658_);
lean_dec_ref(v_content_5657_);
v___x_5661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5661_, 0, v_x_5659_);
return v___x_5661_;
}
else
{
lean_object* v___x_5662_; uint8_t v___x_5663_; 
lean_dec_ref_known(v_x_5659_, 1);
v___x_5662_ = lean_unsigned_to_nat(0u);
v___x_5663_ = lean_nat_dec_lt(v___x_5662_, v___x_5656_);
if (v___x_5663_ == 0)
{
lean_object* v___x_5664_; 
lean_dec_ref(v_s_5658_);
lean_dec_ref(v_content_5657_);
v___x_5664_ = ((lean_object*)(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___closed__1));
return v___x_5664_;
}
else
{
lean_object* v___x_5665_; uint8_t v___x_5666_; lean_object* v___x_5667_; 
v___x_5665_ = l_Std_Http_Chunk_ofByteArray(v_content_5657_);
v___x_5666_ = 0;
v___x_5667_ = l_Std_Http_Body_Stream_send(v_s_5658_, v___x_5665_, v___x_5666_);
return v___x_5667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__0___boxed(lean_object* v___x_5668_, lean_object* v_content_5669_, lean_object* v_s_5670_, lean_object* v_x_5671_, lean_object* v___y_5672_){
_start:
{
lean_object* v_res_5673_; 
v_res_5673_ = l_Std_Http_Body_fromBytes___lam__0(v___x_5668_, v_content_5669_, v_s_5670_, v_x_5671_);
lean_dec(v___x_5668_);
return v_res_5673_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2(lean_object* v_content_5674_, lean_object* v_s_5675_){
_start:
{
lean_object* v___x_5677_; lean_object* v___f_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___f_5681_; lean_object* v___x_5682_; uint8_t v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; 
v___x_5677_ = lean_byte_array_size(v_content_5674_);
lean_inc_ref(v_s_5675_);
v___f_5678_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__0___boxed), 5, 3);
lean_closure_set(v___f_5678_, 0, v___x_5677_);
lean_closure_set(v___f_5678_, 1, v_content_5674_);
lean_closure_set(v___f_5678_, 2, v_s_5675_);
v___x_5679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5677_);
v___x_5680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5679_);
v___f_5681_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__5___boxed), 3, 1);
lean_closure_set(v___f_5681_, 0, v___x_5680_);
v___x_5682_ = lean_unsigned_to_nat(0u);
v___x_5683_ = 0;
v___x_5684_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_s_5675_, v___f_5681_);
v___x_5685_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5682_, v___x_5683_, v___x_5684_, v___f_5678_);
return v___x_5685_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___lam__2___boxed(lean_object* v_content_5686_, lean_object* v_s_5687_, lean_object* v___y_5688_){
_start:
{
lean_object* v_res_5689_; 
v_res_5689_ = l_Std_Http_Body_fromBytes___lam__2(v_content_5686_, v_s_5687_);
return v_res_5689_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes(lean_object* v_content_5690_){
_start:
{
lean_object* v___f_5692_; lean_object* v___x_5693_; 
v___f_5692_ = lean_alloc_closure((void*)(l_Std_Http_Body_fromBytes___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5692_, 0, v_content_5690_);
v___x_5693_ = l_Std_Http_Body_stream(v___f_5692_);
return v___x_5693_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_fromBytes___boxed(lean_object* v_content_5694_, lean_object* v_a_5695_){
_start:
{
lean_object* v_res_5696_; 
v_res_5696_ = l_Std_Http_Body_fromBytes(v_content_5694_);
return v_res_5696_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1(lean_object* v_a_5697_, lean_object* v___f_5698_, lean_object* v_x_5699_){
_start:
{
if (lean_obj_tag(v_x_5699_) == 0)
{
lean_object* v_a_5701_; lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5709_; 
lean_dec_ref(v___f_5698_);
lean_dec_ref(v_a_5697_);
v_a_5701_ = lean_ctor_get(v_x_5699_, 0);
v_isSharedCheck_5709_ = !lean_is_exclusive(v_x_5699_);
if (v_isSharedCheck_5709_ == 0)
{
v___x_5703_ = v_x_5699_;
v_isShared_5704_ = v_isSharedCheck_5709_;
goto v_resetjp_5702_;
}
else
{
lean_inc(v_a_5701_);
lean_dec(v_x_5699_);
v___x_5703_ = lean_box(0);
v_isShared_5704_ = v_isSharedCheck_5709_;
goto v_resetjp_5702_;
}
v_resetjp_5702_:
{
lean_object* v___x_5706_; 
if (v_isShared_5704_ == 0)
{
v___x_5706_ = v___x_5703_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5708_; 
v_reuseFailAlloc_5708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_a_5701_);
v___x_5706_ = v_reuseFailAlloc_5708_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
lean_object* v___x_5707_; 
v___x_5707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5706_);
return v___x_5707_;
}
}
}
else
{
lean_object* v___x_5710_; uint8_t v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; 
lean_dec_ref_known(v_x_5699_, 1);
v___x_5710_ = lean_unsigned_to_nat(0u);
v___x_5711_ = 0;
v___x_5712_ = l_Std_Http_Body_Stream_close(v_a_5697_);
v___x_5713_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5710_, v___x_5711_, v___x_5712_, v___f_5698_);
return v___x_5713_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__1___boxed(lean_object* v_a_5714_, lean_object* v___f_5715_, lean_object* v_x_5716_, lean_object* v___y_5717_){
_start:
{
lean_object* v_res_5718_; 
v_res_5718_ = l_Std_Http_Body_empty___lam__1(v_a_5714_, v___f_5715_, v_x_5716_);
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2(lean_object* v_x_5725_){
_start:
{
if (lean_obj_tag(v_x_5725_) == 0)
{
lean_object* v___x_5727_; 
v___x_5727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5727_, 0, v_x_5725_);
return v___x_5727_;
}
else
{
lean_object* v_a_5728_; lean_object* v___f_5729_; lean_object* v___f_5730_; lean_object* v___x_5731_; lean_object* v___f_5732_; uint8_t v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; 
v_a_5728_ = lean_ctor_get(v_x_5725_, 0);
lean_inc_n(v_a_5728_, 2);
v___f_5729_ = lean_alloc_closure((void*)(l_Std_Http_Body_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5729_, 0, v_x_5725_);
v___f_5730_ = lean_alloc_closure((void*)(l_Std_Http_Body_empty___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5730_, 0, v_a_5728_);
lean_closure_set(v___f_5730_, 1, v___f_5729_);
v___x_5731_ = lean_unsigned_to_nat(0u);
v___f_5732_ = ((lean_object*)(l_Std_Http_Body_empty___lam__2___closed__2));
v___x_5733_ = 0;
v___x_5734_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_a_5728_, v___f_5732_);
v___x_5735_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5731_, v___x_5733_, v___x_5734_, v___f_5730_);
return v___x_5735_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___lam__2___boxed(lean_object* v_x_5736_, lean_object* v___y_5737_){
_start:
{
lean_object* v_res_5738_; 
v_res_5738_ = l_Std_Http_Body_empty___lam__2(v_x_5736_);
return v_res_5738_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty(){
_start:
{
lean_object* v___f_5741_; lean_object* v___x_5742_; uint8_t v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v___f_5741_ = ((lean_object*)(l_Std_Http_Body_empty___closed__0));
v___x_5742_ = lean_unsigned_to_nat(0u);
v___x_5743_ = 0;
v___x_5744_ = l_Std_Http_Body_mkStream();
v___x_5745_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5742_, v___x_5743_, v___x_5744_, v___f_5741_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_empty___boxed(lean_object* v_a_5746_){
_start:
{
lean_object* v_res_5747_; 
v_res_5747_ = l_Std_Http_Body_empty();
return v_res_5747_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseStreamAny___lam__0(lean_object* v___x_5770_, lean_object* v_f_5771_){
_start:
{
lean_object* v_line_5772_; lean_object* v_body_5773_; lean_object* v_extensions_5774_; lean_object* v___x_5776_; uint8_t v_isShared_5777_; uint8_t v_isSharedCheck_5782_; 
v_line_5772_ = lean_ctor_get(v_f_5771_, 0);
v_body_5773_ = lean_ctor_get(v_f_5771_, 1);
v_extensions_5774_ = lean_ctor_get(v_f_5771_, 2);
v_isSharedCheck_5782_ = !lean_is_exclusive(v_f_5771_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5776_ = v_f_5771_;
v_isShared_5777_ = v_isSharedCheck_5782_;
goto v_resetjp_5775_;
}
else
{
lean_inc(v_extensions_5774_);
lean_inc(v_body_5773_);
lean_inc(v_line_5772_);
lean_dec(v_f_5771_);
v___x_5776_ = lean_box(0);
v_isShared_5777_ = v_isSharedCheck_5782_;
goto v_resetjp_5775_;
}
v_resetjp_5775_:
{
lean_object* v___x_5778_; lean_object* v___x_5780_; 
v___x_5778_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_5770_, v_body_5773_);
if (v_isShared_5777_ == 0)
{
lean_ctor_set(v___x_5776_, 1, v___x_5778_);
v___x_5780_ = v___x_5776_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_line_5772_);
lean_ctor_set(v_reuseFailAlloc_5781_, 1, v___x_5778_);
lean_ctor_set(v_reuseFailAlloc_5781_, 2, v_extensions_5774_);
v___x_5780_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
return v___x_5780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(lean_object* v___x_5786_, lean_object* v_x_5787_){
_start:
{
if (lean_obj_tag(v_x_5787_) == 0)
{
lean_object* v_a_5789_; lean_object* v___x_5791_; uint8_t v_isShared_5792_; uint8_t v_isSharedCheck_5797_; 
lean_dec_ref(v___x_5786_);
v_a_5789_ = lean_ctor_get(v_x_5787_, 0);
v_isSharedCheck_5797_ = !lean_is_exclusive(v_x_5787_);
if (v_isSharedCheck_5797_ == 0)
{
v___x_5791_ = v_x_5787_;
v_isShared_5792_ = v_isSharedCheck_5797_;
goto v_resetjp_5790_;
}
else
{
lean_inc(v_a_5789_);
lean_dec(v_x_5787_);
v___x_5791_ = lean_box(0);
v_isShared_5792_ = v_isSharedCheck_5797_;
goto v_resetjp_5790_;
}
v_resetjp_5790_:
{
lean_object* v___x_5794_; 
if (v_isShared_5792_ == 0)
{
v___x_5794_ = v___x_5791_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v_a_5789_);
v___x_5794_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
lean_object* v___x_5795_; 
v___x_5795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5795_, 0, v___x_5794_);
return v___x_5795_;
}
}
}
else
{
lean_object* v_a_5798_; lean_object* v___x_5800_; uint8_t v_isShared_5801_; uint8_t v_isSharedCheck_5817_; 
v_a_5798_ = lean_ctor_get(v_x_5787_, 0);
v_isSharedCheck_5817_ = !lean_is_exclusive(v_x_5787_);
if (v_isSharedCheck_5817_ == 0)
{
v___x_5800_ = v_x_5787_;
v_isShared_5801_ = v_isSharedCheck_5817_;
goto v_resetjp_5799_;
}
else
{
lean_inc(v_a_5798_);
lean_dec(v_x_5787_);
v___x_5800_ = lean_box(0);
v_isShared_5801_ = v_isSharedCheck_5817_;
goto v_resetjp_5799_;
}
v_resetjp_5799_:
{
lean_object* v_line_5802_; lean_object* v_body_5803_; lean_object* v_extensions_5804_; lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5816_; 
v_line_5802_ = lean_ctor_get(v_a_5798_, 0);
v_body_5803_ = lean_ctor_get(v_a_5798_, 1);
v_extensions_5804_ = lean_ctor_get(v_a_5798_, 2);
v_isSharedCheck_5816_ = !lean_is_exclusive(v_a_5798_);
if (v_isSharedCheck_5816_ == 0)
{
v___x_5806_ = v_a_5798_;
v_isShared_5807_ = v_isSharedCheck_5816_;
goto v_resetjp_5805_;
}
else
{
lean_inc(v_extensions_5804_);
lean_inc(v_body_5803_);
lean_inc(v_line_5802_);
lean_dec(v_a_5798_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5816_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
lean_object* v___x_5808_; lean_object* v___x_5810_; 
v___x_5808_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_5786_, v_body_5803_);
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 1, v___x_5808_);
v___x_5810_ = v___x_5806_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5815_; 
v_reuseFailAlloc_5815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5815_, 0, v_line_5802_);
lean_ctor_set(v_reuseFailAlloc_5815_, 1, v___x_5808_);
lean_ctor_set(v_reuseFailAlloc_5815_, 2, v_extensions_5804_);
v___x_5810_ = v_reuseFailAlloc_5815_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
lean_object* v___x_5812_; 
if (v_isShared_5801_ == 0)
{
lean_ctor_set(v___x_5800_, 0, v___x_5810_);
v___x_5812_ = v___x_5800_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v___x_5810_);
v___x_5812_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
lean_object* v___x_5813_; 
v___x_5813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5813_, 0, v___x_5812_);
return v___x_5813_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(lean_object* v___x_5818_, lean_object* v_x_5819_, lean_object* v___y_5820_){
_start:
{
lean_object* v_res_5821_; 
v_res_5821_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_5818_, v_x_5819_);
return v_res_5821_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(lean_object* v___f_5822_, lean_object* v_action_5823_, lean_object* v___y_5824_){
_start:
{
lean_object* v___x_5826_; uint8_t v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_5826_ = lean_unsigned_to_nat(0u);
v___x_5827_ = 0;
lean_inc_ref(v___y_5824_);
v___x_5828_ = lean_apply_2(v_action_5823_, v___y_5824_, lean_box(0));
v___x_5829_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5826_, v___x_5827_, v___x_5828_, v___f_5822_);
return v___x_5829_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(lean_object* v___f_5830_, lean_object* v_action_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_){
_start:
{
lean_object* v_res_5834_; 
v_res_5834_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(v___f_5830_, v_action_5831_, v___y_5832_);
lean_dec_ref(v___y_5832_);
return v_res_5834_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(lean_object* v___f_5840_, lean_object* v_action_5841_, lean_object* v___y_5842_){
_start:
{
lean_object* v___x_5844_; uint8_t v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; 
v___x_5844_ = lean_unsigned_to_nat(0u);
v___x_5845_ = 0;
v___x_5846_ = lean_apply_1(v_action_5841_, lean_box(0));
v___x_5847_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5844_, v___x_5845_, v___x_5846_, v___f_5840_);
return v___x_5847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(lean_object* v___f_5848_, lean_object* v_action_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_){
_start:
{
lean_object* v_res_5852_; 
v_res_5852_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(v___f_5848_, v_action_5849_, v___y_5850_);
lean_dec_ref(v___y_5850_);
return v_res_5852_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0(lean_object* v_builder_5856_, lean_object* v_x_5857_){
_start:
{
if (lean_obj_tag(v_x_5857_) == 0)
{
lean_object* v_a_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5867_; 
v_a_5859_ = lean_ctor_get(v_x_5857_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v_x_5857_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5861_ = v_x_5857_;
v_isShared_5862_ = v_isSharedCheck_5867_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_a_5859_);
lean_dec(v_x_5857_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5867_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v___x_5864_; 
if (v_isShared_5862_ == 0)
{
v___x_5864_ = v___x_5861_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5859_);
v___x_5864_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
lean_object* v___x_5865_; 
v___x_5865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5864_);
return v___x_5865_;
}
}
}
else
{
lean_object* v_a_5868_; lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5877_; 
v_a_5868_ = lean_ctor_get(v_x_5857_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v_x_5857_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5870_ = v_x_5857_;
v_isShared_5871_ = v_isSharedCheck_5877_;
goto v_resetjp_5869_;
}
else
{
lean_inc(v_a_5868_);
lean_dec(v_x_5857_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5877_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
lean_object* v___x_5872_; lean_object* v___x_5874_; 
v___x_5872_ = l_Std_Http_Request_Builder_body___redArg(v_builder_5856_, v_a_5868_);
if (v_isShared_5871_ == 0)
{
lean_ctor_set(v___x_5870_, 0, v___x_5872_);
v___x_5874_ = v___x_5870_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v___x_5872_);
v___x_5874_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
lean_object* v___x_5875_; 
v___x_5875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5874_);
return v___x_5875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___lam__0___boxed(lean_object* v_builder_5878_, lean_object* v_x_5879_, lean_object* v___y_5880_){
_start:
{
lean_object* v_res_5881_; 
v_res_5881_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_5878_, v_x_5879_);
lean_dec_ref(v_builder_5878_);
return v_res_5881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream(lean_object* v_builder_5882_, lean_object* v_gen_5883_){
_start:
{
lean_object* v___f_5885_; lean_object* v___x_5886_; uint8_t v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; 
v___f_5885_ = lean_alloc_closure((void*)(l_Std_Http_Request_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5885_, 0, v_builder_5882_);
v___x_5886_ = lean_unsigned_to_nat(0u);
v___x_5887_ = 0;
v___x_5888_ = l_Std_Http_Body_stream(v_gen_5883_);
v___x_5889_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5886_, v___x_5887_, v___x_5888_, v___f_5885_);
return v___x_5889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_stream___boxed(lean_object* v_builder_5890_, lean_object* v_gen_5891_, lean_object* v_a_5892_){
_start:
{
lean_object* v_res_5893_; 
v_res_5893_ = l_Std_Http_Request_Builder_stream(v_builder_5890_, v_gen_5891_);
return v_res_5893_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0(lean_object* v_builder_5894_, lean_object* v_x_5895_){
_start:
{
if (lean_obj_tag(v_x_5895_) == 0)
{
lean_object* v_a_5897_; lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5905_; 
v_a_5897_ = lean_ctor_get(v_x_5895_, 0);
v_isSharedCheck_5905_ = !lean_is_exclusive(v_x_5895_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5899_ = v_x_5895_;
v_isShared_5900_ = v_isSharedCheck_5905_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v_x_5895_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5905_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5902_; 
if (v_isShared_5900_ == 0)
{
v___x_5902_ = v___x_5899_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_a_5897_);
v___x_5902_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
lean_object* v___x_5903_; 
v___x_5903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5902_);
return v___x_5903_;
}
}
}
else
{
lean_object* v_a_5906_; lean_object* v___x_5908_; uint8_t v_isShared_5909_; uint8_t v_isSharedCheck_5915_; 
v_a_5906_ = lean_ctor_get(v_x_5895_, 0);
v_isSharedCheck_5915_ = !lean_is_exclusive(v_x_5895_);
if (v_isSharedCheck_5915_ == 0)
{
v___x_5908_ = v_x_5895_;
v_isShared_5909_ = v_isSharedCheck_5915_;
goto v_resetjp_5907_;
}
else
{
lean_inc(v_a_5906_);
lean_dec(v_x_5895_);
v___x_5908_ = lean_box(0);
v_isShared_5909_ = v_isSharedCheck_5915_;
goto v_resetjp_5907_;
}
v_resetjp_5907_:
{
lean_object* v___x_5910_; lean_object* v___x_5912_; 
v___x_5910_ = l_Std_Http_Response_Builder_body___redArg(v_builder_5894_, v_a_5906_);
if (v_isShared_5909_ == 0)
{
lean_ctor_set(v___x_5908_, 0, v___x_5910_);
v___x_5912_ = v___x_5908_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v___x_5910_);
v___x_5912_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
lean_object* v___x_5913_; 
v___x_5913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5912_);
return v___x_5913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___lam__0___boxed(lean_object* v_builder_5916_, lean_object* v_x_5917_, lean_object* v___y_5918_){
_start:
{
lean_object* v_res_5919_; 
v_res_5919_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_5916_, v_x_5917_);
lean_dec_ref(v_builder_5916_);
return v_res_5919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream(lean_object* v_builder_5920_, lean_object* v_gen_5921_){
_start:
{
lean_object* v___f_5923_; lean_object* v___x_5924_; uint8_t v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; 
v___f_5923_ = lean_alloc_closure((void*)(l_Std_Http_Response_Builder_stream___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5923_, 0, v_builder_5920_);
v___x_5924_ = lean_unsigned_to_nat(0u);
v___x_5925_ = 0;
v___x_5926_ = l_Std_Http_Body_stream(v_gen_5921_);
v___x_5927_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5924_, v___x_5925_, v___x_5926_, v___f_5923_);
return v___x_5927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_stream___boxed(lean_object* v_builder_5928_, lean_object* v_gen_5929_, lean_object* v_a_5930_){
_start:
{
lean_object* v_res_5931_; 
v_res_5931_ = l_Std_Http_Response_Builder_stream(v_builder_5928_, v_gen_5929_);
return v_res_5931_;
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

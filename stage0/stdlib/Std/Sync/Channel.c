// Lean compiler output
// Module: Std.Sync.Channel
// Imports: public import Init.Data.Queue public import Std.Sync.Mutex public import Std.Async.IO import Init.Data.Vector.Basic import Init.Data.Option.BasicAux import Init.Omega
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
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* lean_task_pure(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_Queue_enqueue___redArg(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_wait(lean_object*);
lean_object* l_Std_Queue_empty___redArg();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Std_Queue_isEmpty___redArg(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Queue_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_mapError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_CloseableChannel_instReprError_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.CloseableChannel.Error.closed"};
static const lean_object* l_Std_CloseableChannel_instReprError_repr___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instReprError_repr___closed__0_value;
static const lean_ctor_object l_Std_CloseableChannel_instReprError_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instReprError_repr___closed__0_value)}};
static const lean_object* l_Std_CloseableChannel_instReprError_repr___closed__1 = (const lean_object*)&l_Std_CloseableChannel_instReprError_repr___closed__1_value;
static const lean_string_object l_Std_CloseableChannel_instReprError_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.CloseableChannel.Error.alreadyClosed"};
static const lean_object* l_Std_CloseableChannel_instReprError_repr___closed__2 = (const lean_object*)&l_Std_CloseableChannel_instReprError_repr___closed__2_value;
static const lean_ctor_object l_Std_CloseableChannel_instReprError_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instReprError_repr___closed__2_value)}};
static const lean_object* l_Std_CloseableChannel_instReprError_repr___closed__3 = (const lean_object*)&l_Std_CloseableChannel_instReprError_repr___closed__3_value;
static lean_once_cell_t l_Std_CloseableChannel_instReprError_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instReprError_repr___closed__4;
static lean_once_cell_t l_Std_CloseableChannel_instReprError_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instReprError_repr___closed__5;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instReprError_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instReprError_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instReprError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instReprError_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instReprError___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instReprError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_CloseableChannel_instReprError = (const lean_object*)&l_Std_CloseableChannel_instReprError___closed__0_value;
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Error_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_CloseableChannel_instDecidableEqError(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instDecidableEqError___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_CloseableChannel_instHashableError_hash(uint8_t);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instHashableError_hash___boxed(lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instHashableError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instHashableError_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instHashableError___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instHashableError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_CloseableChannel_instHashableError = (const lean_object*)&l_Std_CloseableChannel_instHashableError___closed__0_value;
static const lean_string_object l_Std_CloseableChannel_instToStringError___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "trying to send on an already closed channel"};
static const lean_object* l_Std_CloseableChannel_instToStringError___lam__0___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instToStringError___lam__0___closed__0_value;
static const lean_string_object l_Std_CloseableChannel_instToStringError___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "trying to close an already closed channel"};
static const lean_object* l_Std_CloseableChannel_instToStringError___lam__0___closed__1 = (const lean_object*)&l_Std_CloseableChannel_instToStringError___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instToStringError___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instToStringError___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instToStringError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instToStringError___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instToStringError___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instToStringError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_CloseableChannel_instToStringError = (const lean_object*)&l_Std_CloseableChannel_instToStringError___closed__0_value;
static const lean_ctor_object l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instToStringError___lam__0___closed__0_value)}};
static const lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0_value;
static const lean_ctor_object l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instToStringError___lam__0___closed__1_value)}};
static const lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1 = (const lean_object*)&l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instMonadLiftEIOErrorIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instMonadLiftEIOErrorIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO = (const lean_object*)&l_Std_CloseableChannel_instMonadLiftEIOErrorIO___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0_value;
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0;
static lean_once_cell_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0_value;
static lean_once_cell_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1;
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2_value;
static lean_once_cell_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0_value)} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1_value;
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__2_value;
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__2_value)}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__0_value;
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__0 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__0_value)}};
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1_value;
static const lean_closure_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0 = (const lean_object*)&l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value),((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1_value)} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0_value)} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value),((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0_value)} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0_value;
static const lean_array_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0 = (const lean_object*)&l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value)} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object*, lean_object*);
static lean_once_cell_t l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_recvSelector___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__1 = (const lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__1_value;
static const lean_ctor_object l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__0_value),((lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__1_value)}};
static const lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__2 = (const lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__0_value)} };
static const lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__1 = (const lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__1_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__1_value)} };
static const lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__2 = (const lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lean_mk_io_user_error, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instToStringError___closed__0_value)} };
static const lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__0_value)} };
static const lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1 = (const lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2 = (const lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2_value;
static lean_once_cell_t l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3;
static lean_once_cell_t l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4;
static lean_once_cell_t l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Std_Channel_send_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Std_Channel_send_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Channel_send___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Std.Sync.Channel"};
static const lean_object* l_Std_Channel_send___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Channel_send___redArg___lam__0___closed__0_value;
static const lean_string_object l_Std_Channel_send___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Std.Channel.send"};
static const lean_object* l_Std_Channel_send___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Channel_send___redArg___lam__0___closed__1_value;
static const lean_string_object l_Std_Channel_send___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Std_Channel_send___redArg___lam__0___closed__2 = (const lean_object*)&l_Std_Channel_send___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Std_Channel_send___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Channel_send___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Channel_send___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Channel_send___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Channel_send___redArg___closed__0 = (const lean_object*)&l_Std_Channel_send___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Channel_recv___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Std.Channel.recv"};
static const lean_object* l_Std_Channel_recv___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Channel_recv___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Std_Channel_recv___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Channel_recv___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Channel_recvSelector___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_Channel_recvSelector___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_Channel_recvSelector___redArg___lam__1___closed__0_value;
static const lean_string_object l_Std_Channel_recvSelector___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_Channel_recvSelector___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_Channel_recvSelector___redArg___lam__1___closed__1_value;
static const lean_string_object l_Std_Channel_recvSelector___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_Channel_recvSelector___redArg___lam__1___closed__2 = (const lean_object*)&l_Std_Channel_recvSelector___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Channel_recvSelector___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__0 = (const lean_object*)&l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__0_value)} };
static const lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1 = (const lean_object*)&l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__0 = (const lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__0_value)} };
static const lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__1 = (const lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__1_value;
static const lean_closure_object l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__1_value)} };
static const lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2 = (const lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2_value;
static lean_once_cell_t l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3;
static lean_once_cell_t l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4;
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Channel_instAsyncWriteOfInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Channel_instAsyncWriteOfInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_CloseableChannel_Error_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_CloseableChannel_Error_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_CloseableChannel_Error_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___redArg(lean_object* v_closed_22_){
_start:
{
lean_inc(v_closed_22_);
return v_closed_22_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___redArg___boxed(lean_object* v_closed_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_CloseableChannel_Error_closed_elim___redArg(v_closed_23_);
lean_dec(v_closed_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_closed_28_){
_start:
{
lean_inc(v_closed_28_);
return v_closed_28_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_closed_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_CloseableChannel_Error_closed_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_closed_32_);
lean_dec(v_closed_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg(lean_object* v_alreadyClosed_35_){
_start:
{
lean_inc(v_alreadyClosed_35_);
return v_alreadyClosed_35_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg___boxed(lean_object* v_alreadyClosed_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg(v_alreadyClosed_36_);
lean_dec(v_alreadyClosed_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_alreadyClosed_41_){
_start:
{
lean_inc(v_alreadyClosed_41_);
return v_alreadyClosed_41_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_alreadyClosed_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_CloseableChannel_Error_alreadyClosed_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_alreadyClosed_45_);
lean_dec(v_alreadyClosed_45_);
return v_res_47_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instReprError_repr___closed__4(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(2u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instReprError_repr___closed__5(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_nat_to_int(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instReprError_repr(uint8_t v_x_58_, lean_object* v_prec_59_){
_start:
{
lean_object* v___y_61_; lean_object* v___y_68_; 
if (v_x_58_ == 0)
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1024u);
v___x_75_ = lean_nat_dec_le(v___x_74_, v_prec_59_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__4, &l_Std_CloseableChannel_instReprError_repr___closed__4_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__4);
v___y_61_ = v___x_76_;
goto v___jp_60_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__5, &l_Std_CloseableChannel_instReprError_repr___closed__5_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__5);
v___y_61_ = v___x_77_;
goto v___jp_60_;
}
}
else
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_59_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__4, &l_Std_CloseableChannel_instReprError_repr___closed__4_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__4);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__5, &l_Std_CloseableChannel_instReprError_repr___closed__5_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__5);
v___y_68_ = v___x_81_;
goto v___jp_67_;
}
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_62_ = ((lean_object*)(l_Std_CloseableChannel_instReprError_repr___closed__1));
lean_inc(v___y_61_);
v___x_63_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_63_, 0, v___y_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = 0;
v___x_65_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*1, v___x_64_);
v___x_66_ = l_Repr_addAppParen(v___x_65_, v_prec_59_);
return v___x_66_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_69_ = ((lean_object*)(l_Std_CloseableChannel_instReprError_repr___closed__3));
lean_inc(v___y_68_);
v___x_70_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_70_, 0, v___y_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = 0;
v___x_72_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*1, v___x_71_);
v___x_73_ = l_Repr_addAppParen(v___x_72_, v_prec_59_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instReprError_repr___boxed(lean_object* v_x_82_, lean_object* v_prec_83_){
_start:
{
uint8_t v_x_117__boxed_84_; lean_object* v_res_85_; 
v_x_117__boxed_84_ = lean_unbox(v_x_82_);
v_res_85_ = l_Std_CloseableChannel_instReprError_repr(v_x_117__boxed_84_, v_prec_83_);
lean_dec(v_prec_83_);
return v_res_85_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Error_ofNat(lean_object* v_n_88_){
_start:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_nat_dec_le(v_n_88_, v___x_89_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ofNat___boxed(lean_object* v_n_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Std_CloseableChannel_Error_ofNat(v_n_93_);
lean_dec(v_n_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_instDecidableEqError(uint8_t v_x_96_, uint8_t v_y_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_98_ = lean_box(v_x_96_);
v___x_99_ = lean_obj_tag_nat(v___x_98_);
lean_dec(v___x_98_);
v___x_100_ = lean_box(v_y_97_);
v___x_101_ = lean_obj_tag_nat(v___x_100_);
lean_dec(v___x_100_);
v___x_102_ = lean_nat_dec_eq(v___x_99_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instDecidableEqError___boxed(lean_object* v_x_103_, lean_object* v_y_104_){
_start:
{
uint8_t v_x_23__boxed_105_; uint8_t v_y_24__boxed_106_; uint8_t v_res_107_; lean_object* v_r_108_; 
v_x_23__boxed_105_ = lean_unbox(v_x_103_);
v_y_24__boxed_106_ = lean_unbox(v_y_104_);
v_res_107_ = l_Std_CloseableChannel_instDecidableEqError(v_x_23__boxed_105_, v_y_24__boxed_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint64_t l_Std_CloseableChannel_instHashableError_hash(uint8_t v_x_109_){
_start:
{
if (v_x_109_ == 0)
{
uint64_t v___x_110_; 
v___x_110_ = 0ULL;
return v___x_110_;
}
else
{
uint64_t v___x_111_; 
v___x_111_ = 1ULL;
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instHashableError_hash___boxed(lean_object* v_x_112_){
_start:
{
uint8_t v_x_28__boxed_113_; uint64_t v_res_114_; lean_object* v_r_115_; 
v_x_28__boxed_113_ = lean_unbox(v_x_112_);
v_res_114_ = l_Std_CloseableChannel_instHashableError_hash(v_x_28__boxed_113_);
v_r_115_ = lean_box_uint64(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instToStringError___lam__0(uint8_t v_x_120_){
_start:
{
if (v_x_120_ == 0)
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Std_CloseableChannel_instToStringError___lam__0___closed__0));
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l_Std_CloseableChannel_instToStringError___lam__0___closed__1));
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instToStringError___lam__0___boxed(lean_object* v_x_123_){
_start:
{
uint8_t v_x_26__boxed_124_; lean_object* v_res_125_; 
v_x_26__boxed_124_ = lean_unbox(v_x_123_);
v_res_125_ = l_Std_CloseableChannel_instToStringError___lam__0(v_x_26__boxed_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(lean_object* v_00_u03b1_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_apply_1(v_x_133_, lean_box(0));
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_135_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_157_; 
v_a_144_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_157_ == 0)
{
v___x_146_ = v___x_135_;
v_isShared_147_ = v_isSharedCheck_157_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_135_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_157_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
uint8_t v___x_148_; 
v___x_148_ = lean_unbox(v_a_144_);
lean_dec(v_a_144_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = ((lean_object*)(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0));
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_149_);
v___x_151_ = v___x_146_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
else
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = ((lean_object*)(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1));
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_153_);
v___x_155_ = v___x_146_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___boxed(lean_object* v_00_u03b1_158_, lean_object* v_x_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(v_00_u03b1_158_, v_x_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___redArg(lean_object* v_x_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_tag_nat(v_x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___redArg___boxed(lean_object* v_x_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___redArg(v_x_166_);
lean_dec_ref(v_x_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl(lean_object* v_00_u03b1_168_, lean_object* v_x_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_tag_nat(v_x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___boxed(lean_object* v_00_u03b1_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl(v_00_u03b1_171_, v_x_172_);
lean_dec_ref(v_x_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(lean_object* v_t_174_, lean_object* v_k_175_){
_start:
{
if (lean_obj_tag(v_t_174_) == 0)
{
lean_object* v_promise_176_; lean_object* v___x_177_; 
v_promise_176_ = lean_ctor_get(v_t_174_, 0);
lean_inc(v_promise_176_);
lean_dec_ref_known(v_t_174_, 1);
v___x_177_ = lean_apply_1(v_k_175_, v_promise_176_);
return v___x_177_;
}
else
{
lean_object* v_finished_178_; lean_object* v___x_179_; 
v_finished_178_ = lean_ctor_get(v_t_174_, 0);
lean_inc_ref(v_finished_178_);
lean_dec_ref_known(v_t_174_, 1);
v___x_179_ = lean_apply_1(v_k_175_, v_finished_178_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(lean_object* v_00_u03b1_180_, lean_object* v_motive_181_, lean_object* v_ctorIdx_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_k_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_183_, v_k_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___boxed(lean_object* v_00_u03b1_187_, lean_object* v_motive_188_, lean_object* v_ctorIdx_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_k_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(v_00_u03b1_187_, v_motive_188_, v_ctorIdx_189_, v_t_190_, v_h_191_, v_k_192_);
lean_dec(v_ctorIdx_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim___redArg(lean_object* v_t_194_, lean_object* v_normal_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_194_, v_normal_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim(lean_object* v_00_u03b1_197_, lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_normal_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_199_, v_normal_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim___redArg(lean_object* v_t_203_, lean_object* v_select_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_203_, v_select_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim(lean_object* v_00_u03b1_206_, lean_object* v_motive_207_, lean_object* v_t_208_, lean_object* v_h_209_, lean_object* v_select_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_208_, v_select_210_);
return v___x_211_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(lean_object* v_x_212_, lean_object* v_w_213_, lean_object* v_lose_214_){
_start:
{
lean_object* v_finished_216_; lean_object* v_promise_217_; lean_object* v___x_218_; uint8_t v___y_220_; uint8_t v___x_228_; 
v_finished_216_ = lean_ctor_get(v_w_213_, 0);
v_promise_217_ = lean_ctor_get(v_w_213_, 1);
v___x_218_ = lean_st_ref_take(v_finished_216_);
v___x_228_ = lean_unbox(v___x_218_);
lean_dec(v___x_218_);
if (v___x_228_ == 0)
{
uint8_t v___x_229_; 
v___x_229_ = 1;
v___y_220_ = v___x_229_;
goto v___jp_219_;
}
else
{
uint8_t v___x_230_; 
v___x_230_ = 0;
v___y_220_ = v___x_230_;
goto v___jp_219_;
}
v___jp_219_:
{
uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = 1;
v___x_222_ = lean_box(v___x_221_);
v___x_223_ = lean_st_ref_put(v_finished_216_, v___x_222_);
if (v___y_220_ == 0)
{
lean_object* v___x_224_; uint8_t v___x_225_; 
lean_dec(v_x_212_);
v___x_224_ = lean_apply_1(v_lose_214_, lean_box(0));
v___x_225_ = lean_unbox(v___x_224_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec_ref(v_lose_214_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v_x_212_);
v___x_227_ = lean_io_promise_resolve(v___x_226_, v_promise_217_);
return v___y_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg___boxed(lean_object* v_x_231_, lean_object* v_w_232_, lean_object* v_lose_233_, lean_object* v___y_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_231_, v_w_232_, v_lose_233_);
lean_dec_ref(v_w_232_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(lean_object* v_00_u03b1_237_, lean_object* v_x_238_, lean_object* v_w_239_, lean_object* v_lose_240_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_238_, v_w_239_, v_lose_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___boxed(lean_object* v_00_u03b1_243_, lean_object* v_x_244_, lean_object* v_w_245_, lean_object* v_lose_246_, lean_object* v___y_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(v_00_u03b1_243_, v_x_244_, v_w_245_, v_lose_246_);
lean_dec_ref(v_w_245_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(uint8_t v___x_250_){
_start:
{
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0___boxed(lean_object* v___x_252_, lean_object* v___y_253_){
_start:
{
uint8_t v___x_372__boxed_254_; uint8_t v_res_255_; lean_object* v_r_256_; 
v___x_372__boxed_254_ = lean_unbox(v___x_252_);
v_res_255_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(v___x_372__boxed_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(lean_object* v_c_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_c_260_) == 0)
{
lean_object* v_promise_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_promise_263_ = lean_ctor_get(v_c_260_, 0);
v___x_264_ = lean_io_promise_resolve(v_x_261_, v_promise_263_);
v___x_265_ = 1;
return v___x_265_;
}
else
{
lean_object* v_finished_266_; lean_object* v_lose_267_; uint8_t v___x_268_; 
v_finished_266_ = lean_ctor_get(v_c_260_, 0);
v_lose_267_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0));
v___x_268_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_261_, v_finished_266_, v_lose_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___boxed(lean_object* v_c_269_, lean_object* v_x_270_, lean_object* v_a_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_c_269_, v_x_270_);
lean_dec_ref(v_c_269_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(lean_object* v_00_u03b1_274_, lean_object* v_c_275_, lean_object* v_x_276_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_c_275_, v_x_276_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___boxed(lean_object* v_00_u03b1_279_, lean_object* v_c_280_, lean_object* v_x_281_, lean_object* v_a_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(v_00_u03b1_279_, v_c_280_, v_x_281_);
lean_dec_ref(v_c_280_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_Queue_empty___redArg();
return v___x_285_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = 0;
v___x_287_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_288_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*2, v___x_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg(){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1);
v___x_291_ = l_Std_Mutex_new___redArg(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___boxed(lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(lean_object* v_00_u03b1_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___boxed(lean_object* v_00_u03b1_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(v_00_u03b1_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(lean_object* v_mutex_300_, lean_object* v_k_301_){
_start:
{
lean_object* v_ref_303_; lean_object* v_mutex_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_ref_303_ = lean_ctor_get(v_mutex_300_, 0);
lean_inc(v_ref_303_);
v_mutex_304_ = lean_ctor_get(v_mutex_300_, 1);
lean_inc(v_mutex_304_);
lean_dec_ref(v_mutex_300_);
v___x_305_ = lean_io_basemutex_lock(v_mutex_304_);
v___x_306_ = lean_apply_2(v_k_301_, v_ref_303_, lean_box(0));
v___x_307_ = lean_io_basemutex_unlock(v_mutex_304_);
lean_dec(v_mutex_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg___boxed(lean_object* v_mutex_308_, lean_object* v_k_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_308_, v_k_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(lean_object* v_00_u03b1_312_, lean_object* v_00_u03b2_313_, lean_object* v_mutex_314_, lean_object* v_k_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_314_, v_k_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___boxed(lean_object* v_00_u03b1_318_, lean_object* v_00_u03b2_319_, lean_object* v_mutex_320_, lean_object* v_k_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(v_00_u03b1_318_, v_00_u03b2_319_, v_mutex_320_, v_k_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(lean_object* v_v_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_values_329_; lean_object* v_consumers_330_; uint8_t v_closed_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_357_; 
v___x_327_ = lean_box(0);
v___x_328_ = lean_st_ref_get(v___y_325_);
v_values_329_ = lean_ctor_get(v___x_328_, 0);
v_consumers_330_ = lean_ctor_get(v___x_328_, 1);
v_closed_331_ = lean_ctor_get_uint8(v___x_328_, sizeof(void*)*2);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_357_ == 0)
{
v___x_333_ = v___x_328_;
v_isShared_334_ = v_isSharedCheck_357_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_consumers_330_);
lean_inc(v_values_329_);
lean_dec(v___x_328_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_357_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; 
lean_inc_ref(v_consumers_330_);
v___x_335_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_330_);
if (lean_obj_tag(v___x_335_) == 1)
{
lean_object* v_val_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v_consumers_330_);
v_val_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_351_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_351_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_val_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_351_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_fst_340_; lean_object* v_snd_341_; lean_object* v___x_343_; 
v_fst_340_ = lean_ctor_get(v_val_336_, 0);
lean_inc(v_fst_340_);
v_snd_341_ = lean_ctor_get(v_val_336_, 1);
lean_inc(v_snd_341_);
lean_dec(v_val_336_);
lean_inc(v_v_324_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v_v_324_);
v___x_343_ = v___x_338_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_v_324_);
v___x_343_ = v_reuseFailAlloc_350_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
uint8_t v___x_344_; lean_object* v___x_346_; 
v___x_344_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_340_, v___x_343_);
lean_dec(v_fst_340_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_snd_341_);
v___x_346_ = v___x_333_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_values_329_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_snd_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_349_, sizeof(void*)*2, v_closed_331_);
v___x_346_ = v_reuseFailAlloc_349_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; 
v___x_347_ = lean_st_ref_swap(v___y_325_, v___x_346_);
lean_dec(v___x_347_);
if (v___x_344_ == 0)
{
goto _start;
}
else
{
lean_dec(v_v_324_);
return v___x_327_;
}
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_354_; 
lean_dec(v___x_335_);
v___x_352_ = l_Std_Queue_enqueue___redArg(v_v_324_, v_values_329_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_352_);
v___x_354_ = v___x_333_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_consumers_330_);
lean_ctor_set_uint8(v_reuseFailAlloc_356_, sizeof(void*)*2, v_closed_331_);
v___x_354_ = v_reuseFailAlloc_356_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; 
v___x_355_ = lean_st_ref_swap(v___y_325_, v___x_354_);
lean_dec(v___x_355_);
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg___boxed(lean_object* v_v_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_358_, v___y_359_);
lean_dec(v___y_359_);
return v_res_361_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(lean_object* v_v_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; uint8_t v_closed_366_; 
v___x_365_ = lean_st_ref_get(v___y_363_);
v_closed_366_ = lean_ctor_get_uint8(v___x_365_, sizeof(void*)*2);
lean_dec(v___x_365_);
if (v_closed_366_ == 0)
{
uint8_t v___x_367_; lean_object* v___x_368_; 
v___x_367_ = 1;
v___x_368_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_362_, v___y_363_);
return v___x_367_;
}
else
{
uint8_t v___x_369_; 
lean_dec(v_v_362_);
v___x_369_ = 0;
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed(lean_object* v_v_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(v_v_370_, v___y_371_);
lean_dec(v___y_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(lean_object* v_ch_375_, lean_object* v_v_376_){
_start:
{
lean_object* v___f_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___f_378_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_378_, 0, v_v_376_);
v___x_379_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_375_, v___f_378_);
v___x_380_ = lean_unbox(v___x_379_);
lean_dec(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___boxed(lean_object* v_ch_381_, lean_object* v_v_382_, lean_object* v_a_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_381_, v_v_382_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(lean_object* v_00_u03b1_386_, lean_object* v_ch_387_, lean_object* v_v_388_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_387_, v_v_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___boxed(lean_object* v_00_u03b1_391_, lean_object* v_ch_392_, lean_object* v_v_393_, lean_object* v_a_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(v_00_u03b1_391_, v_ch_392_, v_v_393_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(lean_object* v_00_u03b1_397_, lean_object* v_v_398_, lean_object* v_inst_399_, lean_object* v_a_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_398_, v___y_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_404_, lean_object* v_v_405_, lean_object* v_inst_406_, lean_object* v_a_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(v_00_u03b1_404_, v_v_405_, v_inst_406_, v_a_407_, v___y_408_);
lean_dec(v___y_408_);
return v_res_410_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
v___x_415_ = lean_task_pure(v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
v___x_419_ = lean_task_pure(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(lean_object* v_ch_420_, lean_object* v_v_421_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_420_, v_v_421_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_424_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___boxed(lean_object* v_ch_426_, lean_object* v_v_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_426_, v_v_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(lean_object* v_00_u03b1_430_, lean_object* v_ch_431_, lean_object* v_v_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_431_, v_v_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___boxed(lean_object* v_00_u03b1_435_, lean_object* v_ch_436_, lean_object* v_v_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(v_00_u03b1_435_, v_ch_436_, v_v_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(lean_object* v_mutex_440_, lean_object* v_k_441_){
_start:
{
lean_object* v_ref_443_; lean_object* v_mutex_444_; lean_object* v___x_445_; lean_object* v_r_446_; 
v_ref_443_ = lean_ctor_get(v_mutex_440_, 0);
lean_inc(v_ref_443_);
v_mutex_444_ = lean_ctor_get(v_mutex_440_, 1);
lean_inc(v_mutex_444_);
lean_dec_ref(v_mutex_440_);
v___x_445_ = lean_io_basemutex_lock(v_mutex_444_);
v_r_446_ = lean_apply_2(v_k_441_, v_ref_443_, lean_box(0));
if (lean_obj_tag(v_r_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_a_447_ = lean_ctor_get(v_r_446_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_r_446_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v_r_446_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v_r_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_io_basemutex_unlock(v_mutex_444_);
lean_dec(v_mutex_444_);
if (v_isShared_450_ == 0)
{
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_447_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_a_456_ = lean_ctor_get(v_r_446_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_r_446_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v_r_446_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v_r_446_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_io_basemutex_unlock(v_mutex_444_);
lean_dec(v_mutex_444_);
if (v_isShared_459_ == 0)
{
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_456_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg___boxed(lean_object* v_mutex_465_, lean_object* v_k_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_465_, v_k_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_mutex_471_, lean_object* v_k_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_471_, v_k_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___boxed(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_mutex_477_, lean_object* v_k_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(v_00_u03b1_475_, v_00_u03b2_476_, v_mutex_477_, v_k_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(lean_object* v_as_481_, size_t v_sz_482_, size_t v_i_483_, lean_object* v_b_484_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = lean_usize_dec_lt(v_i_483_, v_sz_482_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_b_484_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v_a_489_; lean_object* v___x_490_; uint8_t v___x_491_; size_t v___x_492_; size_t v___x_493_; 
v___x_488_ = lean_box(0);
v_a_489_ = lean_array_uget_borrowed(v_as_481_, v_i_483_);
v___x_490_ = lean_box(0);
v___x_491_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_489_, v___x_490_);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_483_, v___x_492_);
v_i_483_ = v___x_493_;
v_b_484_ = v___x_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg___boxed(lean_object* v_as_495_, lean_object* v_sz_496_, lean_object* v_i_497_, lean_object* v_b_498_, lean_object* v___y_499_){
_start:
{
size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_sz_boxed_500_ = lean_unbox_usize(v_sz_496_);
lean_dec(v_sz_496_);
v_i_boxed_501_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_495_, v_sz_boxed_500_, v_i_boxed_501_, v_b_498_);
lean_dec_ref(v_as_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; uint8_t v_closed_506_; 
v___x_505_ = lean_st_ref_get(v___y_503_);
v_closed_506_ = lean_ctor_get_uint8(v___x_505_, sizeof(void*)*2);
if (v_closed_506_ == 0)
{
lean_object* v_values_507_; lean_object* v_consumers_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_531_; 
v_values_507_ = lean_ctor_get(v___x_505_, 0);
v_consumers_508_ = lean_ctor_get(v___x_505_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_531_ == 0)
{
v___x_510_ = v___x_505_;
v_isShared_511_ = v_isSharedCheck_531_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_consumers_508_);
lean_inc(v_values_507_);
lean_dec(v___x_505_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_531_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; size_t v_sz_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_512_ = l_Std_Queue_toArray___redArg(v_consumers_508_);
v___x_513_ = lean_box(0);
v_sz_514_ = lean_array_size(v___x_512_);
v___x_515_ = ((size_t)0ULL);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v___x_512_, v_sz_514_, v___x_515_, v___x_513_);
lean_dec_ref(v___x_512_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_529_; 
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v___x_516_, 0);
lean_dec(v_unused_530_);
v___x_518_ = v___x_516_;
v_isShared_519_ = v_isSharedCheck_529_;
goto v_resetjp_517_;
}
else
{
lean_dec(v___x_516_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_529_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_521_ = 1;
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_520_);
v___x_523_ = v___x_510_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_values_507_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_520_);
v___x_523_ = v_reuseFailAlloc_528_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*2, v___x_521_);
v___x_524_ = lean_st_ref_swap(v___y_503_, v___x_523_);
lean_dec(v___x_524_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_513_);
v___x_526_ = v___x_518_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_513_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_del_object(v___x_510_);
lean_dec_ref(v_values_507_);
return v___x_516_;
}
}
}
else
{
uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v___x_505_);
v___x_532_ = 1;
v___x_533_ = lean_box(v___x_532_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___boxed(lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(v___y_535_);
lean_dec(v___y_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(lean_object* v_ch_539_){
_start:
{
lean_object* v___f_541_; lean_object* v___x_542_; 
v___f_541_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0));
v___x_542_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_539_, v___f_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___boxed(lean_object* v_ch_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(lean_object* v_00_u03b1_546_, lean_object* v_ch_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___boxed(lean_object* v_00_u03b1_550_, lean_object* v_ch_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(v_00_u03b1_550_, v_ch_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(lean_object* v_00_u03b1_554_, lean_object* v_as_555_, size_t v_sz_556_, size_t v_i_557_, lean_object* v_b_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_555_, v_sz_556_, v_i_557_, v_b_558_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___boxed(lean_object* v_00_u03b1_562_, lean_object* v_as_563_, lean_object* v_sz_564_, lean_object* v_i_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
size_t v_sz_boxed_569_; size_t v_i_boxed_570_; lean_object* v_res_571_; 
v_sz_boxed_569_ = lean_unbox_usize(v_sz_564_);
lean_dec(v_sz_564_);
v_i_boxed_570_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(v_00_u03b1_562_, v_as_563_, v_sz_boxed_569_, v_i_boxed_570_, v_b_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v_as_563_);
return v_res_571_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; uint8_t v_closed_575_; 
v___x_574_ = lean_st_ref_get(v___y_572_);
v_closed_575_ = lean_ctor_get_uint8(v___x_574_, sizeof(void*)*2);
lean_dec(v___x_574_);
return v_closed_575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
uint8_t v_res_578_; lean_object* v_r_579_; 
v_res_578_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(v___y_576_);
lean_dec(v___y_576_);
v_r_579_ = lean_box(v_res_578_);
return v_r_579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(lean_object* v_ch_581_){
_start:
{
lean_object* v___f_583_; lean_object* v___x_584_; 
v___f_583_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0));
v___x_584_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_581_, v___f_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___boxed(lean_object* v_ch_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_585_);
return v_res_587_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(lean_object* v_00_u03b1_588_, lean_object* v_ch_589_){
_start:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_589_);
v___x_592_ = lean_unbox(v___x_591_);
lean_dec(v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___boxed(lean_object* v_00_u03b1_593_, lean_object* v_ch_594_, lean_object* v_a_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(v_00_u03b1_593_, v_ch_594_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_598_, lean_object* v_fst_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_toPure_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_toPure_601_ = lean_ctor_get(v_toApplicative_598_, 1);
lean_inc(v_toPure_601_);
lean_dec_ref(v_toApplicative_598_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_fst_599_);
v___x_603_ = lean_apply_2(v_toPure_601_, lean_box(0), v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_604_, lean_object* v_a_605_, lean_object* v_inst_606_, lean_object* v_toBind_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_values_609_; lean_object* v_consumers_610_; uint8_t v_closed_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_629_; 
v_values_609_ = lean_ctor_get(v_a_608_, 0);
v_consumers_610_ = lean_ctor_get(v_a_608_, 1);
v_closed_611_ = lean_ctor_get_uint8(v_a_608_, sizeof(void*)*2);
v_isSharedCheck_629_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_629_ == 0)
{
v___x_613_ = v_a_608_;
v_isShared_614_ = v_isSharedCheck_629_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_consumers_610_);
lean_inc(v_values_609_);
lean_dec(v_a_608_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_629_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_Queue_dequeue_x3f___redArg(v_values_609_);
if (lean_obj_tag(v___x_615_) == 1)
{
lean_object* v_val_616_; lean_object* v_fst_617_; lean_object* v_snd_618_; lean_object* v___f_619_; lean_object* v___x_621_; 
v_val_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_val_616_);
lean_dec_ref_known(v___x_615_, 1);
v_fst_617_ = lean_ctor_get(v_val_616_, 0);
lean_inc(v_fst_617_);
v_snd_618_ = lean_ctor_get(v_val_616_, 1);
lean_inc(v_snd_618_);
lean_dec(v_val_616_);
v___f_619_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_619_, 0, v_toApplicative_604_);
lean_closure_set(v___f_619_, 1, v_fst_617_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_snd_618_);
v___x_621_ = v___x_613_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_snd_618_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_consumers_610_);
lean_ctor_set_uint8(v_reuseFailAlloc_625_, sizeof(void*)*2, v_closed_611_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
lean_inc(v_a_605_);
v___x_622_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_622_, 0, lean_box(0));
lean_closure_set(v___x_622_, 1, lean_box(0));
lean_closure_set(v___x_622_, 2, v_a_605_);
lean_closure_set(v___x_622_, 3, v___x_621_);
v___x_623_ = lean_apply_2(v_inst_606_, lean_box(0), v___x_622_);
v___x_624_ = lean_apply_4(v_toBind_607_, lean_box(0), lean_box(0), v___x_623_, v___f_619_);
return v___x_624_;
}
}
else
{
lean_object* v_toPure_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___x_615_);
lean_del_object(v___x_613_);
lean_dec_ref(v_consumers_610_);
lean_dec(v_toBind_607_);
lean_dec(v_inst_606_);
v_toPure_626_ = lean_ctor_get(v_toApplicative_604_, 1);
lean_inc(v_toPure_626_);
lean_dec_ref(v_toApplicative_604_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_apply_2(v_toPure_626_, lean_box(0), v___x_627_);
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_630_, lean_object* v_a_631_, lean_object* v_inst_632_, lean_object* v_toBind_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(v_toApplicative_630_, v_a_631_, v_inst_632_, v_toBind_633_, v_a_634_);
lean_dec(v_a_631_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_toApplicative_639_; lean_object* v_toBind_640_; lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_toApplicative_639_ = lean_ctor_get(v_inst_636_, 0);
lean_inc_ref(v_toApplicative_639_);
v_toBind_640_ = lean_ctor_get(v_inst_636_, 1);
lean_inc_n(v_toBind_640_, 2);
lean_dec_ref(v_inst_636_);
lean_inc(v_inst_637_);
lean_inc_n(v_a_638_, 2);
v___f_641_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_641_, 0, v_toApplicative_639_);
lean_closure_set(v___f_641_, 1, v_a_638_);
lean_closure_set(v___f_641_, 2, v_inst_637_);
lean_closure_set(v___f_641_, 3, v_toBind_640_);
v___x_642_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_642_, 0, lean_box(0));
lean_closure_set(v___x_642_, 1, lean_box(0));
lean_closure_set(v___x_642_, 2, v_a_638_);
v___x_643_ = lean_apply_2(v_inst_637_, lean_box(0), v___x_642_);
v___x_644_ = lean_apply_4(v_toBind_640_, lean_box(0), lean_box(0), v___x_643_, v___f_641_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_645_, v_inst_646_, v_a_647_);
lean_dec(v_a_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(lean_object* v_m_649_, lean_object* v_00_u03b1_650_, lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_651_, v_inst_652_, v_a_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___boxed(lean_object* v_m_655_, lean_object* v_00_u03b1_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(v_m_655_, v_00_u03b1_656_, v_inst_657_, v_inst_658_, v_a_659_);
lean_dec(v_a_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(lean_object* v_a_661_){
_start:
{
lean_object* v___x_663_; lean_object* v_values_664_; lean_object* v_consumers_665_; uint8_t v_closed_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_686_; 
v___x_663_ = lean_st_ref_get(v_a_661_);
v_values_664_ = lean_ctor_get(v___x_663_, 0);
v_consumers_665_ = lean_ctor_get(v___x_663_, 1);
v_closed_666_ = lean_ctor_get_uint8(v___x_663_, sizeof(void*)*2);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_686_ == 0)
{
v___x_668_ = v___x_663_;
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_consumers_665_);
lean_inc(v_values_664_);
lean_dec(v___x_663_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_Queue_dequeue_x3f___redArg(v_values_664_);
if (lean_obj_tag(v___x_670_) == 1)
{
lean_object* v_val_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_684_; 
v_val_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_684_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_684_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_val_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_684_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_678_; 
v_fst_675_ = lean_ctor_get(v_val_671_, 0);
lean_inc(v_fst_675_);
v_snd_676_ = lean_ctor_get(v_val_671_, 1);
lean_inc(v_snd_676_);
lean_dec(v_val_671_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v_snd_676_);
v___x_678_ = v___x_668_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_snd_676_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_consumers_665_);
lean_ctor_set_uint8(v_reuseFailAlloc_683_, sizeof(void*)*2, v_closed_666_);
v___x_678_ = v_reuseFailAlloc_683_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = lean_st_ref_swap(v_a_661_, v___x_678_);
lean_dec(v___x_679_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_fst_675_);
v___x_681_ = v___x_673_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_fst_675_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_object* v___x_685_; 
lean_dec(v___x_670_);
lean_del_object(v___x_668_);
lean_dec_ref(v_consumers_665_);
v___x_685_ = lean_box(0);
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_687_);
lean_dec(v_a_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(lean_object* v_00_u03b1_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_694_, lean_object* v_a_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(v_00_u03b1_694_, v_a_695_);
lean_dec(v_a_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(lean_object* v_ch_699_){
_start:
{
lean_object* v___f_701_; lean_object* v___x_702_; 
v___f_701_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0));
v___x_702_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_699_, v___f_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___boxed(lean_object* v_ch_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(lean_object* v_00_u03b1_706_, lean_object* v_ch_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___boxed(lean_object* v_00_u03b1_710_, lean_object* v_ch_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(v_00_u03b1_710_, v_ch_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(lean_object* v_x_714_){
_start:
{
if (lean_obj_tag(v_x_714_) == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_box(0);
return v___x_715_;
}
else
{
lean_object* v_val_716_; 
v_val_716_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_val_716_);
return v_val_716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed(lean_object* v_x_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(v_x_717_);
lean_dec(v_x_717_);
return v_res_718_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_box(0);
v___x_720_ = lean_task_pure(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(lean_object* v___f_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v___y_722_);
if (lean_obj_tag(v___x_724_) == 1)
{
lean_object* v___x_725_; 
lean_dec_ref(v___f_721_);
v___x_725_ = lean_task_pure(v___x_724_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; uint8_t v_closed_727_; 
lean_dec(v___x_724_);
v___x_726_ = lean_st_ref_get(v___y_722_);
v_closed_727_ = lean_ctor_get_uint8(v___x_726_, sizeof(void*)*2);
lean_dec(v___x_726_);
if (v_closed_727_ == 0)
{
uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_values_731_; lean_object* v_consumers_732_; uint8_t v_closed_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_746_; 
v___x_728_ = 1;
v___x_729_ = lean_io_promise_new();
v___x_730_ = lean_st_ref_take(v___y_722_);
v_values_731_ = lean_ctor_get(v___x_730_, 0);
v_consumers_732_ = lean_ctor_get(v___x_730_, 1);
v_closed_733_ = lean_ctor_get_uint8(v___x_730_, sizeof(void*)*2);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_746_ == 0)
{
v___x_735_ = v___x_730_;
v_isShared_736_ = v_isSharedCheck_746_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_consumers_732_);
lean_inc(v_values_731_);
lean_dec(v___x_730_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_746_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
lean_inc(v___x_729_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_729_);
v___x_738_ = l_Std_Queue_enqueue___redArg(v___x_737_, v_consumers_732_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_738_);
v___x_740_ = v___x_735_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_values_731_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, sizeof(void*)*2, v_closed_733_);
v___x_740_ = v_reuseFailAlloc_745_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_741_ = lean_st_ref_put(v___y_722_, v___x_740_);
v___x_742_ = lean_io_promise_result_opt(v___x_729_);
lean_dec(v___x_729_);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_task_map(v___f_721_, v___x_742_, v___x_743_, v___x_728_);
return v___x_744_;
}
}
}
else
{
lean_object* v___x_747_; 
lean_dec_ref(v___f_721_);
v___x_747_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed(lean_object* v___f_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(v___f_748_, v___y_749_);
lean_dec(v___y_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(lean_object* v_ch_755_){
_start:
{
lean_object* v___f_757_; lean_object* v___x_758_; 
v___f_757_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1));
v___x_758_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_755_, v___f_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___boxed(lean_object* v_ch_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(lean_object* v_00_u03b1_762_, lean_object* v_ch_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___boxed(lean_object* v_00_u03b1_766_, lean_object* v_ch_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(v_00_u03b1_766_, v_ch_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_770_, lean_object* v_a_771_){
_start:
{
uint8_t v___y_773_; lean_object* v_values_777_; uint8_t v_closed_778_; uint8_t v___x_779_; 
v_values_777_ = lean_ctor_get(v_a_771_, 0);
v_closed_778_ = lean_ctor_get_uint8(v_a_771_, sizeof(void*)*2);
v___x_779_ = l_Std_Queue_isEmpty___redArg(v_values_777_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; 
v___x_780_ = 1;
v___y_773_ = v___x_780_;
goto v___jp_772_;
}
else
{
v___y_773_ = v_closed_778_;
goto v___jp_772_;
}
v___jp_772_:
{
lean_object* v_toPure_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_toPure_774_ = lean_ctor_get(v_toApplicative_770_, 1);
lean_inc(v_toPure_774_);
lean_dec_ref(v_toApplicative_770_);
v___x_775_ = lean_box(v___y_773_);
v___x_776_ = lean_apply_2(v_toPure_774_, lean_box(0), v___x_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(v_toApplicative_781_, v_a_782_);
lean_dec_ref(v_a_782_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_toApplicative_787_; lean_object* v_toBind_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_toApplicative_787_ = lean_ctor_get(v_inst_784_, 0);
lean_inc_ref(v_toApplicative_787_);
v_toBind_788_ = lean_ctor_get(v_inst_784_, 1);
lean_inc(v_toBind_788_);
lean_dec_ref(v_inst_784_);
v___f_789_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_789_, 0, v_toApplicative_787_);
lean_inc(v_a_786_);
v___x_790_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_790_, 0, lean_box(0));
lean_closure_set(v___x_790_, 1, lean_box(0));
lean_closure_set(v___x_790_, 2, v_a_786_);
v___x_791_ = lean_apply_2(v_inst_785_, lean_box(0), v___x_790_);
v___x_792_ = lean_apply_4(v_toBind_788_, lean_box(0), lean_box(0), v___x_791_, v___f_789_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___boxed(lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(v_inst_793_, v_inst_794_, v_a_795_);
lean_dec(v_a_795_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(lean_object* v_m_797_, lean_object* v_00_u03b1_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_toApplicative_802_; lean_object* v_toBind_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_toApplicative_802_ = lean_ctor_get(v_inst_799_, 0);
lean_inc_ref(v_toApplicative_802_);
v_toBind_803_ = lean_ctor_get(v_inst_799_, 1);
lean_inc(v_toBind_803_);
lean_dec_ref(v_inst_799_);
v___f_804_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_804_, 0, v_toApplicative_802_);
lean_inc(v_a_801_);
v___x_805_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_805_, 0, lean_box(0));
lean_closure_set(v___x_805_, 1, lean_box(0));
lean_closure_set(v___x_805_, 2, v_a_801_);
v___x_806_ = lean_apply_2(v_inst_800_, lean_box(0), v___x_805_);
v___x_807_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v___x_806_, v___f_804_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___boxed(lean_object* v_m_808_, lean_object* v_00_u03b1_809_, lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(v_m_808_, v_00_u03b1_809_, v_inst_810_, v_inst_811_, v_a_812_);
lean_dec(v_a_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_fst_814_, lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_fst_814_);
v_a_817_ = lean_ctor_get(v_x_815_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_x_815_);
if (v_isSharedCheck_825_ == 0)
{
v___x_819_ = v_x_815_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v_x_815_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_824_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; 
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
}
else
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_834_; 
v_isSharedCheck_834_ = !lean_is_exclusive(v_x_815_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v_x_815_, 0);
lean_dec(v_unused_835_);
v___x_827_ = v_x_815_;
v_isShared_828_ = v_isSharedCheck_834_;
goto v_resetjp_826_;
}
else
{
lean_dec(v_x_815_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_834_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v_fst_814_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_829_);
v___x_831_ = v___x_827_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_833_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; 
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_836_, lean_object* v_x_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(v_fst_836_, v_x_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_a_851_ = lean_ctor_get(v_x_849_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v_x_849_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v_x_849_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_858_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; 
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
}
}
else
{
lean_object* v_a_860_; lean_object* v_values_861_; lean_object* v_consumers_862_; uint8_t v_closed_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_881_; 
v_a_860_ = lean_ctor_get(v_x_849_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v_x_849_, 1);
v_values_861_ = lean_ctor_get(v_a_860_, 0);
v_consumers_862_ = lean_ctor_get(v_a_860_, 1);
v_closed_863_ = lean_ctor_get_uint8(v_a_860_, sizeof(void*)*2);
v_isSharedCheck_881_ = !lean_is_exclusive(v_a_860_);
if (v_isSharedCheck_881_ == 0)
{
v___x_865_ = v_a_860_;
v_isShared_866_ = v_isSharedCheck_881_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_consumers_862_);
lean_inc(v_values_861_);
lean_dec(v_a_860_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_881_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_Queue_dequeue_x3f___redArg(v_values_861_);
if (lean_obj_tag(v___x_867_) == 1)
{
lean_object* v_val_868_; lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v___f_871_; lean_object* v___x_873_; 
v_val_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v___x_867_, 1);
v_fst_869_ = lean_ctor_get(v_val_868_, 0);
lean_inc(v_fst_869_);
v_snd_870_ = lean_ctor_get(v_val_868_, 1);
lean_inc(v_snd_870_);
lean_dec(v_val_868_);
v___f_871_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_871_, 0, v_fst_869_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v_snd_870_);
v___x_873_ = v___x_865_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_snd_870_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_consumers_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*2, v_closed_863_);
v___x_873_ = v_reuseFailAlloc_879_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = 0;
v___x_876_ = lean_st_ref_swap(v_a_848_, v___x_873_);
lean_dec(v___x_876_);
v___x_877_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_878_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_874_, v___x_875_, v___x_877_, v___f_871_);
return v___x_878_;
}
}
else
{
lean_object* v___x_880_; 
lean_dec(v___x_867_);
lean_del_object(v___x_865_);
lean_dec_ref(v_consumers_862_);
v___x_880_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_882_, lean_object* v_x_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_882_, v_x_883_);
lean_dec(v_a_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(lean_object* v_a_886_){
_start:
{
lean_object* v___f_888_; lean_object* v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_inc(v_a_886_);
v___f_888_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_888_, 0, v_a_886_);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = 0;
v___x_891_ = lean_st_ref_get(v_a_886_);
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
v___x_894_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_889_, v___x_890_, v___x_893_, v___f_888_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_895_);
lean_dec(v_a_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_object* v_00_u03b1_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_902_, lean_object* v_a_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(v_00_u03b1_902_, v_a_903_);
lean_dec(v_a_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_promise_906_, lean_object* v_x_907_){
_start:
{
if (lean_obj_tag(v_x_907_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_917_; 
v_a_909_ = lean_ctor_get(v_x_907_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_x_907_);
if (v_isSharedCheck_917_ == 0)
{
v___x_911_ = v_x_907_;
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v_x_907_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_916_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = lean_io_promise_resolve(v_x_907_, v_promise_906_);
v___x_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_promise_921_, lean_object* v_x_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_921_, v_x_922_);
lean_dec(v_promise_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_925_, lean_object* v___y_926_, lean_object* v___f_927_, lean_object* v_x_928_){
_start:
{
if (lean_obj_tag(v_x_928_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v___f_927_);
lean_dec_ref(v_lose_925_);
v_a_930_ = lean_ctor_get(v_x_928_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_x_928_);
if (v_isSharedCheck_938_ == 0)
{
v___x_932_ = v_x_928_;
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v_x_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_937_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; 
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
}
}
else
{
lean_object* v_a_939_; uint8_t v___x_940_; 
v_a_939_ = lean_ctor_get(v_x_928_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v_x_928_, 1);
v___x_940_ = lean_unbox(v_a_939_);
lean_dec(v_a_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
lean_dec_ref(v___f_927_);
lean_inc(v___y_926_);
v___x_941_ = lean_apply_2(v_lose_925_, v___y_926_, lean_box(0));
return v___x_941_;
}
else
{
lean_object* v___x_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec_ref(v_lose_925_);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = 0;
v___x_944_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_926_);
v___x_945_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_942_, v___x_943_, v___x_944_, v___f_927_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_946_, lean_object* v___y_947_, lean_object* v___f_948_, lean_object* v_x_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_946_, v___y_947_, v___f_948_, v_x_949_);
lean_dec(v___y_947_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object* v_w_952_, lean_object* v_lose_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_finished_956_; lean_object* v_promise_957_; lean_object* v___f_958_; lean_object* v___f_959_; lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; uint8_t v___y_964_; uint8_t v___x_972_; 
v_finished_956_ = lean_ctor_get(v_w_952_, 0);
lean_inc(v_finished_956_);
v_promise_957_ = lean_ctor_get(v_w_952_, 1);
lean_inc(v_promise_957_);
lean_dec_ref(v_w_952_);
v___f_958_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_958_, 0, v_promise_957_);
lean_inc(v___y_954_);
v___f_959_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_959_, 0, v_lose_953_);
lean_closure_set(v___f_959_, 1, v___y_954_);
lean_closure_set(v___f_959_, 2, v___f_958_);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = 0;
v___x_962_ = lean_st_ref_take(v_finished_956_);
v___x_972_ = lean_unbox(v___x_962_);
lean_dec(v___x_962_);
if (v___x_972_ == 0)
{
uint8_t v___x_973_; 
v___x_973_ = 1;
v___y_964_ = v___x_973_;
goto v___jp_963_;
}
else
{
v___y_964_ = v___x_961_;
goto v___jp_963_;
}
v___jp_963_:
{
uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_965_ = 1;
v___x_966_ = lean_box(v___x_965_);
v___x_967_ = lean_st_ref_put(v_finished_956_, v___x_966_);
lean_dec(v_finished_956_);
v___x_968_ = lean_box(v___y_964_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___x_971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_960_, v___x_961_, v___x_970_, v___f_959_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object* v_w_974_, lean_object* v_lose_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_974_, v_lose_975_, v___y_976_);
lean_dec(v___y_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object* v_00_u03b1_979_, lean_object* v_w_980_, lean_object* v_lose_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_980_, v_lose_981_, v___y_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_985_, lean_object* v_w_986_, lean_object* v_lose_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(v_00_u03b1_985_, v_w_986_, v_lose_987_, v___y_988_);
lean_dec(v___y_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object* v___y_991_){
_start:
{
if (lean_obj_tag(v___y_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_a_992_ = lean_ctor_get(v___y_991_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___y_991_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___y_991_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___y_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1008_; 
v_a_1000_ = lean_ctor_get(v___y_991_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___y_991_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1002_ = v___y_991_;
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___y_991_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_fst_1004_; lean_object* v___x_1006_; 
v_fst_1004_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_fst_1004_);
lean_dec(v_a_1000_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_fst_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_fst_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object* v_mutex_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_io_basemutex_unlock(v_mutex_1009_);
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_1015_, lean_object* v_x_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_mutex_1015_, v_x_1016_);
lean_dec(v_x_1016_);
lean_dec(v_mutex_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object* v_k_1019_, lean_object* v_ref_1020_, lean_object* v_x_1021_){
_start:
{
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_ref_1020_);
lean_dec_ref(v_k_1019_);
v_a_1023_ = lean_ctor_get(v_x_1021_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_x_1021_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v_x_1021_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v_x_1021_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
}
else
{
lean_object* v___x_1032_; 
lean_dec_ref_known(v_x_1021_, 1);
v___x_1032_ = lean_apply_2(v_k_1019_, v_ref_1020_, lean_box(0));
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_k_1033_, lean_object* v_ref_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_k_1033_, v_ref_1034_, v_x_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object* v_mutex_1038_, lean_object* v___f_1039_){
_start:
{
lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = 0;
v___x_1043_ = lean_io_basemutex_lock(v_mutex_1038_);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
v___x_1046_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1041_, v___x_1042_, v___x_1045_, v___f_1039_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_1047_, lean_object* v___f_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(v_mutex_1047_, v___f_1048_);
lean_dec(v_mutex_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(lean_object* v_mutex_1052_, lean_object* v_k_1053_){
_start:
{
lean_object* v_ref_1055_; lean_object* v_mutex_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___y_1065_; 
v_ref_1055_ = lean_ctor_get(v_mutex_1052_, 0);
lean_inc(v_ref_1055_);
v_mutex_1056_ = lean_ctor_get(v_mutex_1052_, 1);
lean_inc_n(v_mutex_1056_, 2);
lean_dec_ref(v_mutex_1052_);
v___f_1057_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0));
v___f_1058_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1058_, 0, v_mutex_1056_);
v___f_1059_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1059_, 0, v_k_1053_);
lean_closure_set(v___f_1059_, 1, v_ref_1055_);
v___f_1060_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1060_, 0, v_mutex_1056_);
lean_closure_set(v___f_1060_, 1, v___f_1059_);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = 0;
v___x_1063_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1060_, v___f_1058_, v___x_1061_, v___x_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1067_; 
v_a_1067_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1063_, 1);
if (lean_obj_tag(v_a_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_a_1068_ = lean_ctor_get(v_a_1067_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_a_1067_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v_a_1067_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v_a_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
v___y_1065_ = v___x_1073_;
goto v___jp_1064_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_a_1076_ = lean_ctor_get(v_a_1067_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_a_1067_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1078_ = v_a_1067_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v_a_1067_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_fst_1080_; lean_object* v___x_1082_; 
v_fst_1080_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_fst_1080_);
lean_dec(v_a_1076_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v_fst_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_fst_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
v___y_1065_ = v___x_1082_;
goto v___jp_1064_;
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_a_1085_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1087_ = v___x_1063_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1063_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_task_map(v___f_1057_, v_a_1085_, v___x_1061_, v___x_1062_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
v___jp_1064_:
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___y_1065_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_1094_, lean_object* v_k_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1094_, v_k_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_object* v_00_u03b1_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_mutex_1100_, lean_object* v_k_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1100_, v_k_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_mutex_1106_, lean_object* v_k_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(v_00_u03b1_1104_, v_00_u03b2_1105_, v_mutex_1106_, v_k_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(lean_object* v_x_1110_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1120_; 
v_a_1112_ = lean_ctor_get(v_x_1110_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1110_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1114_ = v_x_1110_;
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v_x_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1130_; 
v_a_1121_ = lean_ctor_get(v_x_1110_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_x_1110_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1123_ = v_x_1110_;
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v_x_1110_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(lean_object* v_x_1134_){
_start:
{
uint8_t v___y_1137_; 
if (lean_obj_tag(v_x_1134_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1149_; 
v_a_1141_ = lean_ctor_get(v_x_1134_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1134_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1143_ = v_x_1134_;
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v_x_1134_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v_values_1151_; uint8_t v_closed_1152_; uint8_t v___x_1153_; 
v_a_1150_ = lean_ctor_get(v_x_1134_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v_x_1134_, 1);
v_values_1151_ = lean_ctor_get(v_a_1150_, 0);
lean_inc_ref(v_values_1151_);
v_closed_1152_ = lean_ctor_get_uint8(v_a_1150_, sizeof(void*)*2);
lean_dec(v_a_1150_);
v___x_1153_ = l_Std_Queue_isEmpty___redArg(v_values_1151_);
lean_dec_ref(v_values_1151_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; 
v___x_1154_ = 1;
v___y_1137_ = v___x_1154_;
goto v___jp_1136_;
}
else
{
v___y_1137_ = v_closed_1152_;
goto v___jp_1136_;
}
}
v___jp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_box(v___y_1137_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(lean_object* v_x_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(lean_object* v___x_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1158_);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_1163_, v___y_1164_);
lean_dec(v___y_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(lean_object* v___y_1169_, lean_object* v_waiter_1170_, lean_object* v_x_1171_){
_start:
{
if (lean_obj_tag(v_x_1171_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v_waiter_1170_);
v_a_1173_ = lean_ctor_get(v_x_1171_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1175_ = v_x_1171_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v_x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; uint8_t v___x_1183_; 
v_a_1182_ = lean_ctor_get(v_x_1171_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v_x_1171_, 1);
v___x_1183_ = lean_unbox(v_a_1182_);
lean_dec(v_a_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v_values_1185_; lean_object* v_consumers_1186_; uint8_t v_closed_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1198_; 
v___x_1184_ = lean_st_ref_take(v___y_1169_);
v_values_1185_ = lean_ctor_get(v___x_1184_, 0);
v_consumers_1186_ = lean_ctor_get(v___x_1184_, 1);
v_closed_1187_ = lean_ctor_get_uint8(v___x_1184_, sizeof(void*)*2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1189_ = v___x_1184_;
v_isShared_1190_ = v_isSharedCheck_1198_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_consumers_1186_);
lean_inc(v_values_1185_);
lean_dec(v___x_1184_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1198_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_waiter_1170_);
v___x_1192_ = l_Std_Queue_enqueue___redArg(v___x_1191_, v_consumers_1186_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1192_);
v___x_1194_ = v___x_1189_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_values_1185_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*2, v_closed_1187_);
v___x_1194_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_st_ref_put(v___y_1169_, v___x_1194_);
v___x_1196_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_1196_;
}
}
}
else
{
lean_object* v_lose_1199_; lean_object* v___x_1200_; 
v_lose_1199_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0));
v___x_1200_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_waiter_1170_, v_lose_1199_, v___y_1169_);
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(lean_object* v___y_1201_, lean_object* v_waiter_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_1201_, v_waiter_1202_, v_x_1203_);
lean_dec(v___y_1201_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(lean_object* v_waiter_1206_, lean_object* v___f_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___f_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_inc(v___y_1208_);
v___f_1210_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1210_, 0, v___y_1208_);
lean_closure_set(v___f_1210_, 1, v_waiter_1206_);
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = 0;
v___x_1213_ = lean_st_ref_get(v___y_1208_);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
v___x_1216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1211_, v___x_1212_, v___x_1215_, v___f_1207_);
v___x_1217_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1211_, v___x_1212_, v___x_1216_, v___f_1210_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(lean_object* v_waiter_1218_, lean_object* v___f_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v_waiter_1218_, v___f_1219_, v___y_1220_);
lean_dec(v___y_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(lean_object* v___f_1223_, lean_object* v_ch_1224_, lean_object* v_waiter_1225_){
_start:
{
lean_object* v___f_1227_; lean_object* v___x_1228_; 
v___f_1227_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1227_, 0, v_waiter_1225_);
lean_closure_set(v___f_1227_, 1, v___f_1223_);
v___x_1228_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_1224_, v___f_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(lean_object* v___f_1229_, lean_object* v_ch_1230_, lean_object* v_waiter_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_1229_, v_ch_1230_, v_waiter_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(lean_object* v___y_1238_, lean_object* v___f_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v___f_1239_);
v_a_1242_ = lean_ctor_get(v_x_1240_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_x_1240_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1244_ = v_x_1240_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v_x_1240_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1251_; uint8_t v___x_1252_; 
v_a_1251_ = lean_ctor_get(v_x_1240_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v_x_1240_, 1);
v___x_1252_ = lean_unbox(v_a_1251_);
lean_dec(v_a_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref(v___f_1239_);
v___x_1253_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = 0;
v___x_1256_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_1238_);
v___x_1257_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1254_, v___x_1255_, v___x_1256_, v___f_1239_);
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(lean_object* v___y_1258_, lean_object* v___f_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_1258_, v___f_1259_, v_x_1260_);
lean_dec(v___y_1258_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(lean_object* v___f_1263_, lean_object* v___f_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___f_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_inc(v___y_1265_);
v___f_1267_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1267_, 0, v___y_1265_);
lean_closure_set(v___f_1267_, 1, v___f_1263_);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = 0;
v___x_1270_ = lean_st_ref_get(v___y_1265_);
v___x_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
v___x_1273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1268_, v___x_1269_, v___x_1272_, v___f_1264_);
v___x_1274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1268_, v___x_1269_, v___x_1273_, v___f_1267_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(lean_object* v___f_1275_, lean_object* v___f_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_1275_, v___f_1276_, v___y_1277_);
lean_dec(v___y_1277_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(lean_object* v_values_1280_, uint8_t v_closed_1281_, lean_object* v___y_1282_, lean_object* v_x_1283_){
_start:
{
if (lean_obj_tag(v_x_1283_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_values_1280_);
v_a_1285_ = lean_ctor_get(v_x_1283_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_x_1283_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1287_ = v_x_1283_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v_x_1283_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_a_1294_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v_x_1283_, 1);
v___x_1295_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1295_, 0, v_values_1280_);
lean_ctor_set(v___x_1295_, 1, v_a_1294_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*2, v_closed_1281_);
v___x_1296_ = lean_st_ref_swap(v___y_1282_, v___x_1295_);
lean_dec(v___x_1296_);
v___x_1297_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed(lean_object* v_values_1298_, lean_object* v_closed_1299_, lean_object* v___y_1300_, lean_object* v_x_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v_closed_boxed_1303_; lean_object* v_res_1304_; 
v_closed_boxed_1303_ = lean_unbox(v_closed_1299_);
v_res_1304_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(v_values_1298_, v_closed_boxed_1303_, v___y_1300_, v_x_1301_);
lean_dec(v___y_1300_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_1305_){
_start:
{
if (lean_obj_tag(v_x_1305_) == 0)
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_x_1305_);
return v___x_1307_;
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1317_; 
v_a_1308_ = lean_ctor_get(v_x_1305_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_x_1305_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1310_ = v_x_1305_;
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v_x_1305_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = l_List_reverse___redArg(v_a_1308_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(v_x_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_1321_, lean_object* v___x_1322_, lean_object* v_x_1323_){
_start:
{
if (lean_obj_tag(v_x_1323_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v___x_1322_);
lean_dec(v_a_1321_);
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
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1350_; 
v_a_1334_ = lean_ctor_get(v_x_1323_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_x_1323_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1336_ = v_x_1323_;
v_isShared_1337_ = v_isSharedCheck_1350_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v_x_1323_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1350_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
uint8_t v___x_1338_; 
v___x_1338_ = l_List_isEmpty___redArg(v_a_1321_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_dec(v___x_1322_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_a_1334_);
lean_ctor_set(v___x_1339_, 1, v_a_1321_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1339_);
v___x_1341_ = v___x_1336_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
lean_dec(v_a_1321_);
v___x_1344_ = l_List_reverse___redArg(v_a_1334_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1322_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1345_);
v___x_1347_ = v___x_1336_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_1351_, lean_object* v___x_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(v_a_1351_, v___x_1352_, v_x_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(lean_object* v_x_1356_){
_start:
{
uint8_t v___y_1359_; 
if (lean_obj_tag(v_x_1356_) == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_x_1356_);
return v___x_1363_;
}
else
{
lean_object* v_a_1364_; uint8_t v___x_1365_; 
v_a_1364_ = lean_ctor_get(v_x_1356_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v_x_1356_, 1);
v___x_1365_ = lean_unbox(v_a_1364_);
lean_dec(v_a_1364_);
if (v___x_1365_ == 0)
{
uint8_t v___x_1366_; 
v___x_1366_ = 1;
v___y_1359_ = v___x_1366_;
goto v___jp_1358_;
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = 0;
v___y_1359_ = v___x_1367_;
goto v___jp_1358_;
}
}
v___jp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_box(v___y_1359_);
v___x_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(lean_object* v_x_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_tail_1371_, lean_object* v_x_1372_, lean_object* v_head_1373_, lean_object* v_x_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_1371_, v_x_1372_, v_head_1373_, v_x_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(lean_object* v_x_1383_, lean_object* v_x_1384_){
_start:
{
if (lean_obj_tag(v_x_1383_) == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1386_, 0, v_x_1384_);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
else
{
lean_object* v_head_1388_; lean_object* v_tail_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_head_1388_ = lean_ctor_get(v_x_1383_, 0);
lean_inc_n(v_head_1388_, 2);
v_tail_1389_ = lean_ctor_get(v_x_1383_, 1);
lean_inc(v_tail_1389_);
lean_dec_ref_known(v_x_1383_, 2);
v___f_1390_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1390_, 0, v_tail_1389_);
lean_closure_set(v___f_1390_, 1, v_x_1384_);
lean_closure_set(v___f_1390_, 2, v_head_1388_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = 0;
if (lean_obj_tag(v_head_1388_) == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec_ref_known(v_head_1388_, 1);
v___x_1393_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_1394_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1391_, v___x_1392_, v___x_1393_, v___f_1390_);
return v___x_1394_;
}
else
{
lean_object* v_finished_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1408_; 
v_finished_1395_ = lean_ctor_get(v_head_1388_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_head_1388_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1397_ = v_head_1388_;
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_finished_1395_);
lean_dec(v_head_1388_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_finished_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v_finished_1399_ = lean_ctor_get(v_finished_1395_, 0);
lean_inc(v_finished_1399_);
lean_dec_ref(v_finished_1395_);
v___f_1400_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_1401_ = lean_st_ref_get(v_finished_1399_);
lean_dec(v_finished_1399_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1401_);
v___x_1403_ = v___x_1397_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
v___x_1405_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1391_, v___x_1392_, v___x_1404_, v___f_1400_);
v___x_1406_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1391_, v___x_1392_, v___x_1405_, v___f_1390_);
return v___x_1406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object* v_tail_1409_, lean_object* v_x_1410_, lean_object* v_head_1411_, lean_object* v_x_1412_){
_start:
{
if (lean_obj_tag(v_x_1412_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v_head_1411_);
lean_dec(v_x_1410_);
lean_dec(v_tail_1409_);
v_a_1414_ = lean_ctor_get(v_x_1412_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_x_1412_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v_x_1412_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v_x_1412_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
}
else
{
lean_object* v_a_1423_; uint8_t v___x_1424_; 
v_a_1423_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v_x_1412_, 1);
v___x_1424_ = lean_unbox(v_a_1423_);
lean_dec(v_a_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; 
lean_dec_ref(v_head_1411_);
v___x_1425_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1409_, v_x_1410_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1426_, 0, v_head_1411_);
lean_ctor_set(v___x_1426_, 1, v_x_1410_);
v___x_1427_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1409_, v___x_1426_);
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1428_, v_x_1429_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object* v___x_1432_, lean_object* v_eList_1433_, lean_object* v___f_1434_, lean_object* v_x_1435_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v___f_1434_);
lean_dec(v_eList_1433_);
lean_dec(v___x_1432_);
v_a_1437_ = lean_ctor_get(v_x_1435_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_x_1435_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1439_ = v_x_1435_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v_x_1435_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___f_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1446_ = lean_ctor_get(v_x_1435_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v_x_1435_, 1);
lean_inc(v___x_1432_);
v___f_1447_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1447_, 0, v_a_1446_);
lean_closure_set(v___f_1447_, 1, v___x_1432_);
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = 0;
v___x_1450_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_1433_, v___x_1432_);
v___x_1451_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1448_, v___x_1449_, v___x_1450_, v___f_1434_);
v___x_1452_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1448_, v___x_1449_, v___x_1451_, v___f_1447_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v___x_1453_, lean_object* v_eList_1454_, lean_object* v___f_1455_, lean_object* v_x_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v___x_1453_, v_eList_1454_, v___f_1455_, v_x_1456_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object* v_q_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_eList_1463_; lean_object* v_dList_1464_; lean_object* v___f_1465_; lean_object* v___x_1466_; lean_object* v___f_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_eList_1463_ = lean_ctor_get(v_q_1460_, 0);
lean_inc(v_eList_1463_);
v_dList_1464_ = lean_ctor_get(v_q_1460_, 1);
lean_inc(v_dList_1464_);
lean_dec_ref(v_q_1460_);
v___f_1465_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_1466_ = lean_box(0);
v___f_1467_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1467_, 0, v___x_1466_);
lean_closure_set(v___f_1467_, 1, v_eList_1463_);
lean_closure_set(v___f_1467_, 2, v___f_1465_);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = 0;
v___x_1470_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_1464_, v___x_1466_);
v___x_1471_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1468_, v___x_1469_, v___x_1470_, v___f_1465_);
v___x_1472_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1468_, v___x_1469_, v___x_1471_, v___f_1467_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object* v_q_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1473_, v___y_1474_);
lean_dec(v___y_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object* v___y_1477_, lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1478_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1488_; 
v_a_1480_ = lean_ctor_get(v_x_1478_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_x_1478_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1482_ = v_x_1478_;
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v_x_1478_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v_values_1490_; lean_object* v_consumers_1491_; uint8_t v_closed_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_a_1489_ = lean_ctor_get(v_x_1478_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v_x_1478_, 1);
v_values_1490_ = lean_ctor_get(v_a_1489_, 0);
lean_inc_ref(v_values_1490_);
v_consumers_1491_ = lean_ctor_get(v_a_1489_, 1);
lean_inc_ref(v_consumers_1491_);
v_closed_1492_ = lean_ctor_get_uint8(v_a_1489_, sizeof(void*)*2);
lean_dec(v_a_1489_);
v___x_1493_ = lean_box(v_closed_1492_);
lean_inc(v___y_1477_);
v___f_1494_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1494_, 0, v_values_1490_);
lean_closure_set(v___f_1494_, 1, v___x_1493_);
lean_closure_set(v___f_1494_, 2, v___y_1477_);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = 0;
v___x_1497_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_1491_, v___y_1477_);
v___x_1498_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1495_, v___x_1496_, v___x_1497_, v___f_1494_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object* v___y_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1499_, v_x_1500_);
lean_dec(v___y_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object* v___y_1503_){
_start:
{
lean_object* v___f_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_inc(v___y_1503_);
v___f_1505_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1505_, 0, v___y_1503_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = 0;
v___x_1508_ = lean_st_ref_get(v___y_1503_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
v___x_1511_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1506_, v___x_1507_, v___x_1510_, v___f_1505_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1512_);
lean_dec(v___y_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object* v_ch_1521_){
_start:
{
lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___f_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___f_1522_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1));
lean_inc_ref_n(v_ch_1521_, 2);
v___f_1523_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1523_, 0, v___f_1522_);
lean_closure_set(v___f_1523_, 1, v_ch_1521_);
v___f_1524_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2));
v___f_1525_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3));
v___x_1526_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1526_, 0, lean_box(0));
lean_closure_set(v___x_1526_, 1, lean_box(0));
lean_closure_set(v___x_1526_, 2, v_ch_1521_);
lean_closure_set(v___x_1526_, 3, v___f_1524_);
v___x_1527_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1527_, 0, lean_box(0));
lean_closure_set(v___x_1527_, 1, lean_box(0));
lean_closure_set(v___x_1527_, 2, v_ch_1521_);
lean_closure_set(v___x_1527_, 3, v___f_1525_);
v___x_1528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___f_1523_);
lean_ctor_set(v___x_1528_, 2, v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object* v_00_u03b1_1529_, lean_object* v_ch_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object* v_00_u03b1_1532_, lean_object* v_q_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1533_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_q_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_1537_, v_q_1538_, v___y_1539_);
lean_dec(v___y_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object* v_00_u03b1_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1543_, v_x_1544_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_1548_, v_x_1549_, v_x_1550_, v___y_1551_);
lean_dec(v___y_1551_);
return v_res_1553_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0(void){
_start:
{
uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = 0;
v___x_1555_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_1556_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
lean_ctor_set_uint8(v___x_1556_, sizeof(void*)*2, v___x_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg(){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0);
v___x_1559_ = l_Std_Mutex_new___redArg(v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object* v_00_u03b1_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object* v_v_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_producers_1582_; lean_object* v_consumers_1583_; uint8_t v_closed_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1606_; 
v___x_1580_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0));
v___x_1581_ = lean_st_ref_get(v___y_1578_);
v_producers_1582_ = lean_ctor_get(v___x_1581_, 0);
v_consumers_1583_ = lean_ctor_get(v___x_1581_, 1);
v_closed_1584_ = lean_ctor_get_uint8(v___x_1581_, sizeof(void*)*2);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1586_ = v___x_1581_;
v_isShared_1587_ = v_isSharedCheck_1606_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_consumers_1583_);
lean_inc(v_producers_1582_);
lean_dec(v___x_1581_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1606_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_1583_);
if (lean_obj_tag(v___x_1588_) == 1)
{
lean_object* v_val_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1604_; 
v_val_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1604_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_val_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1604_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_fst_1593_; lean_object* v_snd_1594_; lean_object* v___x_1596_; 
v_fst_1593_ = lean_ctor_get(v_val_1589_, 0);
lean_inc(v_fst_1593_);
v_snd_1594_ = lean_ctor_get(v_val_1589_, 1);
lean_inc(v_snd_1594_);
lean_dec(v_val_1589_);
lean_inc(v_v_1577_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v_v_1577_);
v___x_1596_ = v___x_1591_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_v_1577_);
v___x_1596_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
uint8_t v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_1593_, v___x_1596_);
lean_dec(v_fst_1593_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v_snd_1594_);
v___x_1599_ = v___x_1586_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_producers_1582_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_snd_1594_);
lean_ctor_set_uint8(v_reuseFailAlloc_1602_, sizeof(void*)*2, v_closed_1584_);
v___x_1599_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_st_ref_swap(v___y_1578_, v___x_1599_);
lean_dec(v___x_1600_);
if (v___x_1597_ == 0)
{
goto _start;
}
else
{
lean_dec(v_v_1577_);
return v___x_1580_;
}
}
}
}
}
else
{
lean_object* v___x_1605_; 
lean_dec(v___x_1588_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_producers_1582_);
lean_dec(v_v_1577_);
v___x_1605_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2));
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object* v_v_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1607_, v___y_1608_);
lean_dec(v___y_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object* v_v_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v_fst_1615_; 
v___x_1614_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1611_, v_a_1612_);
v_fst_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_fst_1615_);
lean_dec_ref(v___x_1614_);
if (lean_obj_tag(v_fst_1615_) == 0)
{
uint8_t v___x_1616_; 
v___x_1616_ = 1;
return v___x_1616_;
}
else
{
lean_object* v_val_1617_; uint8_t v___x_1618_; 
v_val_1617_ = lean_ctor_get(v_fst_1615_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v_fst_1615_, 1);
v___x_1618_ = lean_unbox(v_val_1617_);
lean_dec(v_val_1617_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object* v_v_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
uint8_t v_res_1622_; lean_object* v_r_1623_; 
v_res_1622_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1619_, v_a_1620_);
lean_dec(v_a_1620_);
v_r_1623_ = lean_box(v_res_1622_);
return v_r_1623_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object* v_00_u03b1_1624_, lean_object* v_v_1625_, lean_object* v_a_1626_){
_start:
{
uint8_t v___x_1628_; 
v___x_1628_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1625_, v_a_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object* v_00_u03b1_1629_, lean_object* v_v_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
uint8_t v_res_1633_; lean_object* v_r_1634_; 
v_res_1633_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(v_00_u03b1_1629_, v_v_1630_, v_a_1631_);
lean_dec(v_a_1631_);
v_r_1634_ = lean_box(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object* v_00_u03b1_1635_, lean_object* v_v_1636_, lean_object* v_inst_1637_, lean_object* v_a_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1636_, v___y_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1642_, lean_object* v_v_1643_, lean_object* v_inst_1644_, lean_object* v_a_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_1642_, v_v_1643_, v_inst_1644_, v_a_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object* v_v_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; uint8_t v_closed_1653_; 
v___x_1652_ = lean_st_ref_get(v___y_1650_);
v_closed_1653_ = lean_ctor_get_uint8(v___x_1652_, sizeof(void*)*2);
lean_dec(v___x_1652_);
if (v_closed_1653_ == 0)
{
uint8_t v___x_1654_; 
v___x_1654_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1649_, v___y_1650_);
return v___x_1654_;
}
else
{
uint8_t v___x_1655_; 
lean_dec(v_v_1649_);
v___x_1655_ = 0;
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object* v_v_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_res_1659_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1656_, v___y_1657_);
lean_dec(v___y_1657_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object* v_ch_1661_, lean_object* v_v_1662_){
_start:
{
lean_object* v___f_1664_; lean_object* v___x_1665_; 
v___f_1664_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1664_, 0, v_v_1662_);
v___x_1665_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1661_, v___f_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object* v_ch_1666_, lean_object* v_v_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1666_, v_v_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object* v_00_u03b1_1670_, lean_object* v_ch_1671_, lean_object* v_v_1672_){
_start:
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1671_, v_v_1672_);
v___x_1675_ = lean_unbox(v___x_1674_);
lean_dec(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object* v_00_u03b1_1676_, lean_object* v_ch_1677_, lean_object* v_v_1678_, lean_object* v_a_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(v_00_u03b1_1676_, v_ch_1677_, v_v_1678_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 0)
{
goto v___jp_1683_;
}
else
{
lean_object* v_val_1685_; uint8_t v___x_1686_; 
v_val_1685_ = lean_ctor_get(v_x_1682_, 0);
v___x_1686_ = lean_unbox(v_val_1685_);
if (v___x_1686_ == 0)
{
goto v___jp_1683_;
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
return v___x_1687_;
}
}
v___jp_1683_:
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object* v_x_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_1688_);
lean_dec(v_x_1688_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object* v_v_1690_, lean_object* v___f_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; uint8_t v_closed_1695_; 
v___x_1694_ = lean_st_ref_get(v___y_1692_);
v_closed_1695_ = lean_ctor_get_uint8(v___x_1694_, sizeof(void*)*2);
lean_dec(v___x_1694_);
if (v_closed_1695_ == 0)
{
uint8_t v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = 1;
lean_inc(v_v_1690_);
v___x_1697_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1690_, v___y_1692_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_producers_1700_; lean_object* v_consumers_1701_; uint8_t v_closed_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1715_; 
v___x_1698_ = lean_io_promise_new();
v___x_1699_ = lean_st_ref_take(v___y_1692_);
v_producers_1700_ = lean_ctor_get(v___x_1699_, 0);
v_consumers_1701_ = lean_ctor_get(v___x_1699_, 1);
v_closed_1702_ = lean_ctor_get_uint8(v___x_1699_, sizeof(void*)*2);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1704_ = v___x_1699_;
v_isShared_1705_ = v_isSharedCheck_1715_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_consumers_1701_);
lean_inc(v_producers_1700_);
lean_dec(v___x_1699_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1715_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
lean_inc(v___x_1698_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_v_1690_);
lean_ctor_set(v___x_1706_, 1, v___x_1698_);
v___x_1707_ = l_Std_Queue_enqueue___redArg(v___x_1706_, v_producers_1700_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1707_);
v___x_1709_ = v___x_1704_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_consumers_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*2, v_closed_1702_);
v___x_1709_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1710_ = lean_st_ref_put(v___y_1692_, v___x_1709_);
v___x_1711_ = lean_io_promise_result_opt(v___x_1698_);
lean_dec(v___x_1698_);
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = lean_task_map(v___f_1691_, v___x_1711_, v___x_1712_, v___x_1696_);
return v___x_1713_;
}
}
}
else
{
lean_object* v___x_1716_; 
lean_dec_ref(v___f_1691_);
lean_dec(v_v_1690_);
v___x_1716_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_1716_;
}
}
else
{
lean_object* v___x_1717_; 
lean_dec_ref(v___f_1691_);
lean_dec(v_v_1690_);
v___x_1717_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_1717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object* v_v_1718_, lean_object* v___f_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1718_, v___f_1719_, v___y_1720_);
lean_dec(v___y_1720_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object* v_ch_1724_, lean_object* v_v_1725_){
_start:
{
lean_object* v___f_1727_; lean_object* v___f_1728_; lean_object* v___x_1729_; 
v___f_1727_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0));
v___f_1728_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1728_, 0, v_v_1725_);
lean_closure_set(v___f_1728_, 1, v___f_1727_);
v___x_1729_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1724_, v___f_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object* v_ch_1730_, lean_object* v_v_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1730_, v_v_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object* v_00_u03b1_1734_, lean_object* v_ch_1735_, lean_object* v_v_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1735_, v_v_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object* v_00_u03b1_1739_, lean_object* v_ch_1740_, lean_object* v_v_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(v_00_u03b1_1739_, v_ch_1740_, v_v_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object* v_as_1744_, size_t v_sz_1745_, size_t v_i_1746_, lean_object* v_b_1747_){
_start:
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_usize_dec_lt(v_i_1746_, v_sz_1745_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_b_1747_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; lean_object* v_a_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; size_t v___x_1755_; size_t v___x_1756_; 
v___x_1751_ = lean_box(0);
v_a_1752_ = lean_array_uget_borrowed(v_as_1744_, v_i_1746_);
v___x_1753_ = lean_box(0);
v___x_1754_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_1752_, v___x_1753_);
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1746_, v___x_1755_);
v_i_1746_ = v___x_1756_;
v_b_1747_ = v___x_1751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object* v_as_1758_, lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1758_, v_sz_boxed_1763_, v_i_boxed_1764_, v_b_1761_);
lean_dec_ref(v_as_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; uint8_t v_closed_1769_; 
v___x_1768_ = lean_st_ref_get(v___y_1766_);
v_closed_1769_ = lean_ctor_get_uint8(v___x_1768_, sizeof(void*)*2);
if (v_closed_1769_ == 0)
{
lean_object* v_producers_1770_; lean_object* v_consumers_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1794_; 
v_producers_1770_ = lean_ctor_get(v___x_1768_, 0);
v_consumers_1771_ = lean_ctor_get(v___x_1768_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1773_ = v___x_1768_;
v_isShared_1774_ = v_isSharedCheck_1794_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_consumers_1771_);
lean_inc(v_producers_1770_);
lean_dec(v___x_1768_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1794_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; size_t v_sz_1777_; size_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1775_ = l_Std_Queue_toArray___redArg(v_consumers_1771_);
v___x_1776_ = lean_box(0);
v_sz_1777_ = lean_array_size(v___x_1775_);
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_1775_, v_sz_1777_, v___x_1778_, v___x_1776_);
lean_dec_ref(v___x_1775_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1792_; 
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v___x_1779_, 0);
lean_dec(v_unused_1793_);
v___x_1781_ = v___x_1779_;
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
else
{
lean_dec(v___x_1779_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1786_; 
v___x_1783_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_1784_ = 1;
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1783_);
v___x_1786_ = v___x_1773_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_producers_1770_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___x_1783_);
v___x_1786_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*2, v___x_1784_);
v___x_1787_ = lean_st_ref_swap(v___y_1766_, v___x_1786_);
lean_dec(v___x_1787_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1776_);
v___x_1789_ = v___x_1781_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1776_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_del_object(v___x_1773_);
lean_dec_ref(v_producers_1770_);
return v___x_1779_;
}
}
}
else
{
uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v___x_1768_);
v___x_1795_ = 1;
v___x_1796_ = lean_box(v___x_1795_);
v___x_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1798_);
lean_dec(v___y_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object* v_ch_1802_){
_start:
{
lean_object* v___f_1804_; lean_object* v___x_1805_; 
v___f_1804_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0));
v___x_1805_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_1802_, v___f_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object* v_ch_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object* v_00_u03b1_1809_, lean_object* v_ch_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1810_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object* v_00_u03b1_1813_, lean_object* v_ch_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(v_00_u03b1_1813_, v_ch_1814_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object* v_00_u03b1_1817_, lean_object* v_as_1818_, size_t v_sz_1819_, size_t v_i_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1818_, v_sz_1819_, v_i_1820_, v_b_1821_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object* v_00_u03b1_1825_, lean_object* v_as_1826_, lean_object* v_sz_1827_, lean_object* v_i_1828_, lean_object* v_b_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
size_t v_sz_boxed_1832_; size_t v_i_boxed_1833_; lean_object* v_res_1834_; 
v_sz_boxed_1832_ = lean_unbox_usize(v_sz_1827_);
lean_dec(v_sz_1827_);
v_i_boxed_1833_ = lean_unbox_usize(v_i_1828_);
lean_dec(v_i_1828_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_1825_, v_as_1826_, v_sz_boxed_1832_, v_i_boxed_1833_, v_b_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v_as_1826_);
return v_res_1834_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; uint8_t v_closed_1838_; 
v___x_1837_ = lean_st_ref_get(v___y_1835_);
v_closed_1838_ = lean_ctor_get_uint8(v___x_1837_, sizeof(void*)*2);
lean_dec(v___x_1837_);
return v_closed_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v_res_1841_; lean_object* v_r_1842_; 
v_res_1841_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1839_);
lean_dec(v___y_1839_);
v_r_1842_ = lean_box(v_res_1841_);
return v_r_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object* v_ch_1844_){
_start:
{
lean_object* v___f_1846_; lean_object* v___x_1847_; 
v___f_1846_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0));
v___x_1847_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1844_, v___f_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object* v_ch_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object* v_00_u03b1_1851_, lean_object* v_ch_1852_){
_start:
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1852_);
v___x_1855_ = lean_unbox(v___x_1854_);
lean_dec(v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object* v_00_u03b1_1856_, lean_object* v_ch_1857_, lean_object* v_a_1858_){
_start:
{
uint8_t v_res_1859_; lean_object* v_r_1860_; 
v_res_1859_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(v_00_u03b1_1856_, v_ch_1857_);
v_r_1860_ = lean_box(v_res_1859_);
return v_r_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object* v_snd_1861_, lean_object* v_inst_1862_, lean_object* v_toBind_1863_, lean_object* v___f_1864_, lean_object* v_a_1865_){
_start:
{
uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1866_ = 1;
v___x_1867_ = lean_box(v___x_1866_);
v___x_1868_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1868_, 0, lean_box(0));
lean_closure_set(v___x_1868_, 1, v___x_1867_);
lean_closure_set(v___x_1868_, 2, v_snd_1861_);
v___x_1869_ = lean_apply_2(v_inst_1862_, lean_box(0), v___x_1868_);
v___x_1870_ = lean_apply_4(v_toBind_1863_, lean_box(0), lean_box(0), v___x_1869_, v___f_1864_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_1871_, lean_object* v_inst_1872_, lean_object* v_toBind_1873_, lean_object* v_a_1874_, lean_object* v_inst_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_producers_1877_; lean_object* v_consumers_1878_; uint8_t v_closed_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1900_; 
v_producers_1877_ = lean_ctor_get(v_a_1876_, 0);
v_consumers_1878_ = lean_ctor_get(v_a_1876_, 1);
v_closed_1879_ = lean_ctor_get_uint8(v_a_1876_, sizeof(void*)*2);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_a_1876_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1881_ = v_a_1876_;
v_isShared_1882_ = v_isSharedCheck_1900_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_consumers_1878_);
lean_inc(v_producers_1877_);
lean_dec(v_a_1876_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1900_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1877_);
if (lean_obj_tag(v___x_1883_) == 1)
{
lean_object* v_val_1884_; lean_object* v_fst_1885_; lean_object* v_snd_1886_; lean_object* v_fst_1887_; lean_object* v_snd_1888_; lean_object* v___f_1889_; lean_object* v___f_1890_; lean_object* v___x_1892_; 
v_val_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_val_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v_fst_1885_ = lean_ctor_get(v_val_1884_, 0);
lean_inc(v_fst_1885_);
v_snd_1886_ = lean_ctor_get(v_val_1884_, 1);
lean_inc(v_snd_1886_);
lean_dec(v_val_1884_);
v_fst_1887_ = lean_ctor_get(v_fst_1885_, 0);
lean_inc(v_fst_1887_);
v_snd_1888_ = lean_ctor_get(v_fst_1885_, 1);
lean_inc(v_snd_1888_);
lean_dec(v_fst_1885_);
v___f_1889_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1889_, 0, v_toApplicative_1871_);
lean_closure_set(v___f_1889_, 1, v_fst_1887_);
lean_inc(v_toBind_1873_);
v___f_1890_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1890_, 0, v_snd_1888_);
lean_closure_set(v___f_1890_, 1, v_inst_1872_);
lean_closure_set(v___f_1890_, 2, v_toBind_1873_);
lean_closure_set(v___f_1890_, 3, v___f_1889_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_snd_1886_);
v___x_1892_ = v___x_1881_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_snd_1886_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_consumers_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1896_, sizeof(void*)*2, v_closed_1879_);
v___x_1892_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_inc(v_a_1874_);
v___x_1893_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1893_, 0, lean_box(0));
lean_closure_set(v___x_1893_, 1, lean_box(0));
lean_closure_set(v___x_1893_, 2, v_a_1874_);
lean_closure_set(v___x_1893_, 3, v___x_1892_);
v___x_1894_ = lean_apply_2(v_inst_1875_, lean_box(0), v___x_1893_);
v___x_1895_ = lean_apply_4(v_toBind_1873_, lean_box(0), lean_box(0), v___x_1894_, v___f_1890_);
return v___x_1895_;
}
}
else
{
lean_object* v_toPure_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec(v___x_1883_);
lean_del_object(v___x_1881_);
lean_dec_ref(v_consumers_1878_);
lean_dec(v_inst_1875_);
lean_dec(v_toBind_1873_);
lean_dec(v_inst_1872_);
v_toPure_1897_ = lean_ctor_get(v_toApplicative_1871_, 1);
lean_inc(v_toPure_1897_);
lean_dec_ref(v_toApplicative_1871_);
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_apply_2(v_toPure_1897_, lean_box(0), v___x_1898_);
return v___x_1899_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_1901_, lean_object* v_inst_1902_, lean_object* v_toBind_1903_, lean_object* v_a_1904_, lean_object* v_inst_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(v_toApplicative_1901_, v_inst_1902_, v_toBind_1903_, v_a_1904_, v_inst_1905_, v_a_1906_);
lean_dec(v_a_1904_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v_toApplicative_1912_; lean_object* v_toBind_1913_; lean_object* v___f_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_toApplicative_1912_ = lean_ctor_get(v_inst_1908_, 0);
lean_inc_ref(v_toApplicative_1912_);
v_toBind_1913_ = lean_ctor_get(v_inst_1908_, 1);
lean_inc_n(v_toBind_1913_, 2);
lean_dec_ref(v_inst_1908_);
lean_inc(v_inst_1909_);
lean_inc_n(v_a_1911_, 2);
v___f_1914_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1914_, 0, v_toApplicative_1912_);
lean_closure_set(v___f_1914_, 1, v_inst_1910_);
lean_closure_set(v___f_1914_, 2, v_toBind_1913_);
lean_closure_set(v___f_1914_, 3, v_a_1911_);
lean_closure_set(v___f_1914_, 4, v_inst_1909_);
v___x_1915_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1915_, 0, lean_box(0));
lean_closure_set(v___x_1915_, 1, lean_box(0));
lean_closure_set(v___x_1915_, 2, v_a_1911_);
v___x_1916_ = lean_apply_2(v_inst_1909_, lean_box(0), v___x_1915_);
v___x_1917_ = lean_apply_4(v_toBind_1913_, lean_box(0), lean_box(0), v___x_1916_, v___f_1914_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1918_, v_inst_1919_, v_inst_1920_, v_a_1921_);
lean_dec(v_a_1921_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object* v_m_1923_, lean_object* v_00_u03b1_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_inst_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1925_, v_inst_1926_, v_inst_1927_, v_a_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(lean_object* v_m_1930_, lean_object* v_00_u03b1_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(v_m_1930_, v_00_u03b1_1931_, v_inst_1932_, v_inst_1933_, v_inst_1934_, v_a_1935_);
lean_dec(v_a_1935_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object* v_a_1937_){
_start:
{
lean_object* v___x_1939_; lean_object* v_producers_1940_; lean_object* v_consumers_1941_; uint8_t v_closed_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1967_; 
v___x_1939_ = lean_st_ref_get(v_a_1937_);
v_producers_1940_ = lean_ctor_get(v___x_1939_, 0);
v_consumers_1941_ = lean_ctor_get(v___x_1939_, 1);
v_closed_1942_ = lean_ctor_get_uint8(v___x_1939_, sizeof(void*)*2);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1944_ = v___x_1939_;
v_isShared_1945_ = v_isSharedCheck_1967_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_consumers_1941_);
lean_inc(v_producers_1940_);
lean_dec(v___x_1939_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1967_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1940_);
if (lean_obj_tag(v___x_1946_) == 1)
{
lean_object* v_val_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1965_; 
v_val_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1965_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_val_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1965_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_fst_1951_; lean_object* v_snd_1952_; lean_object* v_fst_1953_; lean_object* v_snd_1954_; lean_object* v___x_1956_; 
v_fst_1951_ = lean_ctor_get(v_val_1947_, 0);
lean_inc(v_fst_1951_);
v_snd_1952_ = lean_ctor_get(v_val_1947_, 1);
lean_inc(v_snd_1952_);
lean_dec(v_val_1947_);
v_fst_1953_ = lean_ctor_get(v_fst_1951_, 0);
lean_inc(v_fst_1953_);
v_snd_1954_ = lean_ctor_get(v_fst_1951_, 1);
lean_inc(v_snd_1954_);
lean_dec(v_fst_1951_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v_snd_1952_);
v___x_1956_ = v___x_1944_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_snd_1952_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_consumers_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*2, v_closed_1942_);
v___x_1956_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1957_ = lean_st_ref_swap(v_a_1937_, v___x_1956_);
lean_dec(v___x_1957_);
v___x_1958_ = 1;
v___x_1959_ = lean_box(v___x_1958_);
v___x_1960_ = lean_io_promise_resolve(v___x_1959_, v_snd_1954_);
lean_dec(v_snd_1954_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v_fst_1953_);
v___x_1962_ = v___x_1949_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_fst_1953_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v___x_1966_; 
lean_dec(v___x_1946_);
lean_del_object(v___x_1944_);
lean_dec_ref(v_consumers_1941_);
v___x_1966_ = lean_box(0);
return v___x_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object* v_a_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1968_);
lean_dec(v_a_1968_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object* v_00_u03b1_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_a_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_1975_, v_a_1976_);
lean_dec(v_a_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object* v_ch_1980_){
_start:
{
lean_object* v___f_1982_; lean_object* v___x_1983_; 
v___f_1982_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0));
v___x_1983_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1980_, v___f_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object* v_ch_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_1984_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object* v_00_u03b1_1987_, lean_object* v_ch_1988_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_1988_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object* v_00_u03b1_1991_, lean_object* v_ch_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(v_00_u03b1_1991_, v_ch_1992_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object* v___f_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_st_ref_get(v___y_1996_);
v___x_1999_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_1996_);
if (lean_obj_tag(v___x_1999_) == 1)
{
lean_object* v___x_2000_; 
lean_dec(v___x_1998_);
lean_dec_ref(v___f_1995_);
v___x_2000_ = lean_task_pure(v___x_1999_);
return v___x_2000_;
}
else
{
uint8_t v_closed_2001_; 
lean_dec(v___x_1999_);
v_closed_2001_ = lean_ctor_get_uint8(v___x_1998_, sizeof(void*)*2);
if (v_closed_2001_ == 0)
{
lean_object* v_producers_2002_; lean_object* v_consumers_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2018_; 
v_producers_2002_ = lean_ctor_get(v___x_1998_, 0);
v_consumers_2003_ = lean_ctor_get(v___x_1998_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2005_ = v___x_1998_;
v_isShared_2006_ = v_isSharedCheck_2018_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_consumers_2003_);
lean_inc(v_producers_2002_);
lean_dec(v___x_1998_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2018_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2007_ = 1;
v___x_2008_ = lean_io_promise_new();
lean_inc(v___x_2008_);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
v___x_2010_ = l_Std_Queue_enqueue___redArg(v___x_2009_, v_consumers_2003_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2010_);
v___x_2012_ = v___x_2005_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_producers_2002_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___x_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*2, v_closed_2001_);
v___x_2012_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2013_ = lean_st_ref_swap(v___y_1996_, v___x_2012_);
lean_dec(v___x_2013_);
v___x_2014_ = lean_io_promise_result_opt(v___x_2008_);
lean_dec(v___x_2008_);
v___x_2015_ = lean_unsigned_to_nat(0u);
v___x_2016_ = lean_task_map(v___f_1995_, v___x_2014_, v___x_2015_, v___x_2007_);
return v___x_2016_;
}
}
}
else
{
lean_object* v___x_2019_; 
lean_dec(v___x_1998_);
lean_dec_ref(v___f_1995_);
v___x_2019_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_2019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object* v___f_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2020_, v___y_2021_);
lean_dec(v___y_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object* v_ch_2026_){
_start:
{
lean_object* v___f_2028_; lean_object* v___x_2029_; 
v___f_2028_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0));
v___x_2029_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2026_, v___f_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object* v_ch_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object* v_00_u03b1_2033_, lean_object* v_ch_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object* v_00_u03b1_2037_, lean_object* v_ch_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(v_00_u03b1_2037_, v_ch_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_2041_, lean_object* v_a_2042_){
_start:
{
uint8_t v___y_2044_; lean_object* v_producers_2048_; uint8_t v_closed_2049_; uint8_t v___x_2050_; 
v_producers_2048_ = lean_ctor_get(v_a_2042_, 0);
v_closed_2049_ = lean_ctor_get_uint8(v_a_2042_, sizeof(void*)*2);
v___x_2050_ = l_Std_Queue_isEmpty___redArg(v_producers_2048_);
if (v___x_2050_ == 0)
{
uint8_t v___x_2051_; 
v___x_2051_ = 1;
v___y_2044_ = v___x_2051_;
goto v___jp_2043_;
}
else
{
v___y_2044_ = v_closed_2049_;
goto v___jp_2043_;
}
v___jp_2043_:
{
lean_object* v_toPure_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_toPure_2045_ = lean_ctor_get(v_toApplicative_2041_, 1);
lean_inc(v_toPure_2045_);
lean_dec_ref(v_toApplicative_2041_);
v___x_2046_ = lean_box(v___y_2044_);
v___x_2047_ = lean_apply_2(v_toPure_2045_, lean_box(0), v___x_2046_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(v_toApplicative_2052_, v_a_2053_);
lean_dec_ref(v_a_2053_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object* v_inst_2055_, lean_object* v_inst_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_toApplicative_2058_; lean_object* v_toBind_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v_toApplicative_2058_ = lean_ctor_get(v_inst_2055_, 0);
lean_inc_ref(v_toApplicative_2058_);
v_toBind_2059_ = lean_ctor_get(v_inst_2055_, 1);
lean_inc(v_toBind_2059_);
lean_dec_ref(v_inst_2055_);
v___f_2060_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2060_, 0, v_toApplicative_2058_);
lean_inc(v_a_2057_);
v___x_2061_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2061_, 0, lean_box(0));
lean_closure_set(v___x_2061_, 1, lean_box(0));
lean_closure_set(v___x_2061_, 2, v_a_2057_);
v___x_2062_ = lean_apply_2(v_inst_2056_, lean_box(0), v___x_2061_);
v___x_2063_ = lean_apply_4(v_toBind_2059_, lean_box(0), lean_box(0), v___x_2062_, v___f_2060_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(v_inst_2064_, v_inst_2065_, v_a_2066_);
lean_dec(v_a_2066_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object* v_m_2068_, lean_object* v_00_u03b1_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_toApplicative_2073_; lean_object* v_toBind_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v_toApplicative_2073_ = lean_ctor_get(v_inst_2070_, 0);
lean_inc_ref(v_toApplicative_2073_);
v_toBind_2074_ = lean_ctor_get(v_inst_2070_, 1);
lean_inc(v_toBind_2074_);
lean_dec_ref(v_inst_2070_);
v___f_2075_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2075_, 0, v_toApplicative_2073_);
lean_inc(v_a_2072_);
v___x_2076_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2076_, 0, lean_box(0));
lean_closure_set(v___x_2076_, 1, lean_box(0));
lean_closure_set(v___x_2076_, 2, v_a_2072_);
v___x_2077_ = lean_apply_2(v_inst_2071_, lean_box(0), v___x_2076_);
v___x_2078_ = lean_apply_4(v_toBind_2074_, lean_box(0), lean_box(0), v___x_2077_, v___f_2075_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(lean_object* v_m_2079_, lean_object* v_00_u03b1_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(v_m_2079_, v_00_u03b1_2080_, v_inst_2081_, v_inst_2082_, v_a_2083_);
lean_dec(v_a_2083_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object* v_snd_2085_, lean_object* v___f_2086_, lean_object* v_x_2087_){
_start:
{
if (lean_obj_tag(v_x_2087_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v___f_2086_);
v_a_2089_ = lean_ctor_get(v_x_2087_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_x_2087_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2091_ = v_x_2087_;
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v_x_2087_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
return v___x_2095_;
}
}
}
else
{
lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2111_; 
v_isSharedCheck_2111_ = !lean_is_exclusive(v_x_2087_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v_x_2087_, 0);
lean_dec(v_unused_2112_);
v___x_2099_ = v_x_2087_;
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
else
{
lean_dec(v_x_2087_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
uint8_t v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2101_ = 1;
v___x_2102_ = lean_unsigned_to_nat(0u);
v___x_2103_ = 0;
v___x_2104_ = lean_box(v___x_2101_);
v___x_2105_ = lean_io_promise_resolve(v___x_2104_, v_snd_2085_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2105_);
v___x_2107_ = v___x_2099_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
v___x_2109_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2102_, v___x_2103_, v___x_2108_, v___f_2086_);
return v___x_2109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_snd_2113_, lean_object* v___f_2114_, lean_object* v_x_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2113_, v___f_2114_, v_x_2115_);
lean_dec(v_snd_2113_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object* v_a_2118_, lean_object* v_x_2119_){
_start:
{
if (lean_obj_tag(v_x_2119_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2129_; 
v_a_2121_ = lean_ctor_get(v_x_2119_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_x_2119_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2123_ = v_x_2119_;
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v_x_2119_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v_producers_2131_; lean_object* v_consumers_2132_; uint8_t v_closed_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2154_; 
v_a_2130_ = lean_ctor_get(v_x_2119_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v_x_2119_, 1);
v_producers_2131_ = lean_ctor_get(v_a_2130_, 0);
v_consumers_2132_ = lean_ctor_get(v_a_2130_, 1);
v_closed_2133_ = lean_ctor_get_uint8(v_a_2130_, sizeof(void*)*2);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_a_2130_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2135_ = v_a_2130_;
v_isShared_2136_ = v_isSharedCheck_2154_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_consumers_2132_);
lean_inc(v_producers_2131_);
lean_dec(v_a_2130_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2154_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2131_);
if (lean_obj_tag(v___x_2137_) == 1)
{
lean_object* v_val_2138_; lean_object* v_fst_2139_; lean_object* v_snd_2140_; lean_object* v_fst_2141_; lean_object* v_snd_2142_; lean_object* v___f_2143_; lean_object* v___f_2144_; lean_object* v___x_2146_; 
v_val_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_val_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v_fst_2139_ = lean_ctor_get(v_val_2138_, 0);
lean_inc(v_fst_2139_);
v_snd_2140_ = lean_ctor_get(v_val_2138_, 1);
lean_inc(v_snd_2140_);
lean_dec(v_val_2138_);
v_fst_2141_ = lean_ctor_get(v_fst_2139_, 0);
lean_inc(v_fst_2141_);
v_snd_2142_ = lean_ctor_get(v_fst_2139_, 1);
lean_inc(v_snd_2142_);
lean_dec(v_fst_2139_);
v___f_2143_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2143_, 0, v_fst_2141_);
v___f_2144_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2144_, 0, v_snd_2142_);
lean_closure_set(v___f_2144_, 1, v___f_2143_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v_snd_2140_);
v___x_2146_ = v___x_2135_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_snd_2140_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_consumers_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2152_, sizeof(void*)*2, v_closed_2133_);
v___x_2146_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = 0;
v___x_2149_ = lean_st_ref_swap(v_a_2118_, v___x_2146_);
lean_dec(v___x_2149_);
v___x_2150_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_2151_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2147_, v___x_2148_, v___x_2150_, v___f_2144_);
return v___x_2151_;
}
}
else
{
lean_object* v___x_2153_; 
lean_dec(v___x_2137_);
lean_del_object(v___x_2135_);
lean_dec_ref(v_consumers_2132_);
v___x_2153_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_2153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_a_2155_, lean_object* v_x_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2155_, v_x_2156_);
lean_dec(v_a_2155_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object* v_a_2159_){
_start:
{
lean_object* v___f_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_inc(v_a_2159_);
v___f_2161_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2161_, 0, v_a_2159_);
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = 0;
v___x_2164_ = lean_st_ref_get(v_a_2159_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
v___x_2167_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2162_, v___x_2163_, v___x_2166_, v___f_2161_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object* v_a_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2168_);
lean_dec(v_a_2168_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object* v_00_u03b1_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_a_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_2175_, v_a_2176_);
lean_dec(v_a_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_2179_, lean_object* v___y_2180_, lean_object* v___f_2181_, lean_object* v_x_2182_){
_start:
{
if (lean_obj_tag(v_x_2182_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v___f_2181_);
lean_dec_ref(v_lose_2179_);
v_a_2184_ = lean_ctor_get(v_x_2182_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_x_2182_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2186_ = v_x_2182_;
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v_x_2182_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
}
}
else
{
lean_object* v_a_2193_; uint8_t v___x_2194_; 
v_a_2193_ = lean_ctor_get(v_x_2182_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v_x_2182_, 1);
v___x_2194_ = lean_unbox(v_a_2193_);
lean_dec(v_a_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
lean_dec_ref(v___f_2181_);
lean_inc(v___y_2180_);
v___x_2195_ = lean_apply_2(v_lose_2179_, v___y_2180_, lean_box(0));
return v___x_2195_;
}
else
{
lean_object* v___x_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec_ref(v_lose_2179_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = 0;
v___x_2198_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2180_);
v___x_2199_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2196_, v___x_2197_, v___x_2198_, v___f_2181_);
return v___x_2199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_2200_, lean_object* v___y_2201_, lean_object* v___f_2202_, lean_object* v_x_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2200_, v___y_2201_, v___f_2202_, v_x_2203_);
lean_dec(v___y_2201_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object* v_w_2206_, lean_object* v_lose_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_finished_2210_; lean_object* v_promise_2211_; lean_object* v___f_2212_; lean_object* v___f_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; uint8_t v___y_2218_; uint8_t v___x_2226_; 
v_finished_2210_ = lean_ctor_get(v_w_2206_, 0);
lean_inc(v_finished_2210_);
v_promise_2211_ = lean_ctor_get(v_w_2206_, 1);
lean_inc(v_promise_2211_);
lean_dec_ref(v_w_2206_);
v___f_2212_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2212_, 0, v_promise_2211_);
lean_inc(v___y_2208_);
v___f_2213_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2213_, 0, v_lose_2207_);
lean_closure_set(v___f_2213_, 1, v___y_2208_);
lean_closure_set(v___f_2213_, 2, v___f_2212_);
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = 0;
v___x_2216_ = lean_st_ref_take(v_finished_2210_);
v___x_2226_ = lean_unbox(v___x_2216_);
lean_dec(v___x_2216_);
if (v___x_2226_ == 0)
{
uint8_t v___x_2227_; 
v___x_2227_ = 1;
v___y_2218_ = v___x_2227_;
goto v___jp_2217_;
}
else
{
v___y_2218_ = v___x_2215_;
goto v___jp_2217_;
}
v___jp_2217_:
{
uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2219_ = 1;
v___x_2220_ = lean_box(v___x_2219_);
v___x_2221_ = lean_st_ref_put(v_finished_2210_, v___x_2220_);
lean_dec(v_finished_2210_);
v___x_2222_ = lean_box(v___y_2218_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
v___x_2225_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2214_, v___x_2215_, v___x_2224_, v___f_2213_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object* v_w_2228_, lean_object* v_lose_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2228_, v_lose_2229_, v___y_2230_);
lean_dec(v___y_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object* v_00_u03b1_2233_, lean_object* v_w_2234_, lean_object* v_lose_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2234_, v_lose_2235_, v___y_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_2239_, lean_object* v_w_2240_, lean_object* v_lose_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_2239_, v_w_2240_, v_lose_2241_, v___y_2242_);
lean_dec(v___y_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object* v_x_2245_){
_start:
{
uint8_t v___y_2248_; 
if (lean_obj_tag(v_x_2245_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2260_; 
v_a_2252_ = lean_ctor_get(v_x_2245_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_x_2245_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2254_ = v_x_2245_;
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v_x_2245_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v_producers_2262_; uint8_t v_closed_2263_; uint8_t v___x_2264_; 
v_a_2261_ = lean_ctor_get(v_x_2245_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v_x_2245_, 1);
v_producers_2262_ = lean_ctor_get(v_a_2261_, 0);
lean_inc_ref(v_producers_2262_);
v_closed_2263_ = lean_ctor_get_uint8(v_a_2261_, sizeof(void*)*2);
lean_dec(v_a_2261_);
v___x_2264_ = l_Std_Queue_isEmpty___redArg(v_producers_2262_);
lean_dec_ref(v_producers_2262_);
if (v___x_2264_ == 0)
{
uint8_t v___x_2265_; 
v___x_2265_ = 1;
v___y_2248_ = v___x_2265_;
goto v___jp_2247_;
}
else
{
v___y_2248_ = v_closed_2263_;
goto v___jp_2247_;
}
}
v___jp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = lean_box(v___y_2248_);
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object* v_x_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2266_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object* v___y_2269_, lean_object* v_waiter_2270_, lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2281_; 
lean_dec_ref(v_waiter_2270_);
v_a_2273_ = lean_ctor_get(v_x_2271_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_x_2271_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2275_ = v_x_2271_;
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v_x_2271_);
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
lean_object* v_a_2282_; uint8_t v___x_2283_; 
v_a_2282_ = lean_ctor_get(v_x_2271_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v_x_2271_, 1);
v___x_2283_ = lean_unbox(v_a_2282_);
lean_dec(v_a_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; lean_object* v_producers_2285_; lean_object* v_consumers_2286_; uint8_t v_closed_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2298_; 
v___x_2284_ = lean_st_ref_take(v___y_2269_);
v_producers_2285_ = lean_ctor_get(v___x_2284_, 0);
v_consumers_2286_ = lean_ctor_get(v___x_2284_, 1);
v_closed_2287_ = lean_ctor_get_uint8(v___x_2284_, sizeof(void*)*2);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2289_ = v___x_2284_;
v_isShared_2290_ = v_isSharedCheck_2298_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_consumers_2286_);
lean_inc(v_producers_2285_);
lean_dec(v___x_2284_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2298_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v_waiter_2270_);
v___x_2292_ = l_Std_Queue_enqueue___redArg(v___x_2291_, v_consumers_2286_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 1, v___x_2292_);
v___x_2294_ = v___x_2289_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_producers_2285_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2297_, sizeof(void*)*2, v_closed_2287_);
v___x_2294_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_st_ref_put(v___y_2269_, v___x_2294_);
v___x_2296_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2296_;
}
}
}
else
{
lean_object* v_lose_2299_; lean_object* v___x_2300_; 
v_lose_2299_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0));
v___x_2300_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_2270_, v_lose_2299_, v___y_2269_);
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object* v___y_2301_, lean_object* v_waiter_2302_, lean_object* v_x_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2301_, v_waiter_2302_, v_x_2303_);
lean_dec(v___y_2301_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object* v_waiter_2306_, lean_object* v___f_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___f_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_inc(v___y_2308_);
v___f_2310_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2310_, 0, v___y_2308_);
lean_closure_set(v___f_2310_, 1, v_waiter_2306_);
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = 0;
v___x_2313_ = lean_st_ref_get(v___y_2308_);
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
v___x_2316_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2311_, v___x_2312_, v___x_2315_, v___f_2307_);
v___x_2317_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2311_, v___x_2312_, v___x_2316_, v___f_2310_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object* v_waiter_2318_, lean_object* v___f_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v_waiter_2318_, v___f_2319_, v___y_2320_);
lean_dec(v___y_2320_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object* v___f_2323_, lean_object* v_ch_2324_, lean_object* v_waiter_2325_){
_start:
{
lean_object* v___f_2327_; lean_object* v___x_2328_; 
v___f_2327_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2327_, 0, v_waiter_2325_);
lean_closure_set(v___f_2327_, 1, v___f_2323_);
v___x_2328_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_2324_, v___f_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object* v___f_2329_, lean_object* v_ch_2330_, lean_object* v_waiter_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2329_, v_ch_2330_, v_waiter_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object* v___y_2334_, lean_object* v___f_2335_, lean_object* v_x_2336_){
_start:
{
if (lean_obj_tag(v_x_2336_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2346_; 
lean_dec_ref(v___f_2335_);
v_a_2338_ = lean_ctor_get(v_x_2336_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_x_2336_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2340_ = v_x_2336_;
v_isShared_2341_ = v_isSharedCheck_2346_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v_x_2336_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2346_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
}
}
else
{
lean_object* v_a_2347_; uint8_t v___x_2348_; 
v_a_2347_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v_x_2336_, 1);
v___x_2348_ = lean_unbox(v_a_2347_);
lean_dec(v_a_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
lean_dec_ref(v___f_2335_);
v___x_2349_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_2349_;
}
else
{
lean_object* v___x_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2350_ = lean_unsigned_to_nat(0u);
v___x_2351_ = 0;
v___x_2352_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2334_);
v___x_2353_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2350_, v___x_2351_, v___x_2352_, v___f_2335_);
return v___x_2353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object* v___y_2354_, lean_object* v___f_2355_, lean_object* v_x_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2354_, v___f_2355_, v_x_2356_);
lean_dec(v___y_2354_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object* v___f_2359_, lean_object* v___f_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___f_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_inc(v___y_2361_);
v___f_2363_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2363_, 0, v___y_2361_);
lean_closure_set(v___f_2363_, 1, v___f_2359_);
v___x_2364_ = lean_unsigned_to_nat(0u);
v___x_2365_ = 0;
v___x_2366_ = lean_st_ref_get(v___y_2361_);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
v___x_2369_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2364_, v___x_2365_, v___x_2368_, v___f_2360_);
v___x_2370_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2364_, v___x_2365_, v___x_2369_, v___f_2363_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object* v___f_2371_, lean_object* v___f_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2371_, v___f_2372_, v___y_2373_);
lean_dec(v___y_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object* v_producers_2376_, uint8_t v_closed_2377_, lean_object* v___y_2378_, lean_object* v_x_2379_){
_start:
{
if (lean_obj_tag(v_x_2379_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v_producers_2376_);
v_a_2381_ = lean_ctor_get(v_x_2379_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_x_2379_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2383_ = v_x_2379_;
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v_x_2379_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_a_2390_ = lean_ctor_get(v_x_2379_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v_x_2379_, 1);
v___x_2391_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2391_, 0, v_producers_2376_);
lean_ctor_set(v___x_2391_, 1, v_a_2390_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*2, v_closed_2377_);
v___x_2392_ = lean_st_ref_swap(v___y_2378_, v___x_2391_);
lean_dec(v___x_2392_);
v___x_2393_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object* v_producers_2394_, lean_object* v_closed_2395_, lean_object* v___y_2396_, lean_object* v_x_2397_, lean_object* v___y_2398_){
_start:
{
uint8_t v_closed_boxed_2399_; lean_object* v_res_2400_; 
v_closed_boxed_2399_ = lean_unbox(v_closed_2395_);
v_res_2400_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2394_, v_closed_boxed_2399_, v___y_2396_, v_x_2397_);
lean_dec(v___y_2396_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_2401_, lean_object* v_x_2402_, lean_object* v_head_2403_, lean_object* v_x_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2401_, v_x_2402_, v_head_2403_, v_x_2404_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object* v_x_2407_, lean_object* v_x_2408_){
_start:
{
if (lean_obj_tag(v_x_2407_) == 0)
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2410_, 0, v_x_2408_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
return v___x_2411_;
}
else
{
lean_object* v_head_2412_; lean_object* v_tail_2413_; lean_object* v___f_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v_head_2412_ = lean_ctor_get(v_x_2407_, 0);
lean_inc_n(v_head_2412_, 2);
v_tail_2413_ = lean_ctor_get(v_x_2407_, 1);
lean_inc(v_tail_2413_);
lean_dec_ref_known(v_x_2407_, 2);
v___f_2414_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2414_, 0, v_tail_2413_);
lean_closure_set(v___f_2414_, 1, v_x_2408_);
lean_closure_set(v___f_2414_, 2, v_head_2412_);
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = 0;
if (lean_obj_tag(v_head_2412_) == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec_ref_known(v_head_2412_, 1);
v___x_2417_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_2418_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2415_, v___x_2416_, v___x_2417_, v___f_2414_);
return v___x_2418_;
}
else
{
lean_object* v_finished_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2432_; 
v_finished_2419_ = lean_ctor_get(v_head_2412_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_head_2412_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2421_ = v_head_2412_;
v_isShared_2422_ = v_isSharedCheck_2432_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_finished_2419_);
lean_dec(v_head_2412_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2432_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_finished_2423_; lean_object* v___f_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v_finished_2423_ = lean_ctor_get(v_finished_2419_, 0);
lean_inc(v_finished_2423_);
lean_dec_ref(v_finished_2419_);
v___f_2424_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_2425_ = lean_st_ref_get(v_finished_2423_);
lean_dec(v_finished_2423_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2425_);
v___x_2427_ = v___x_2421_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
v___x_2429_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2415_, v___x_2416_, v___x_2428_, v___f_2424_);
v___x_2430_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2415_, v___x_2416_, v___x_2429_, v___f_2414_);
return v___x_2430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_2433_, lean_object* v_x_2434_, lean_object* v_head_2435_, lean_object* v_x_2436_){
_start:
{
if (lean_obj_tag(v_x_2436_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2446_; 
lean_dec_ref(v_head_2435_);
lean_dec(v_x_2434_);
lean_dec(v_tail_2433_);
v_a_2438_ = lean_ctor_get(v_x_2436_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_x_2436_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2440_ = v_x_2436_;
v_isShared_2441_ = v_isSharedCheck_2446_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v_x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2446_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
}
}
else
{
lean_object* v_a_2447_; uint8_t v___x_2448_; 
v_a_2447_ = lean_ctor_get(v_x_2436_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v_x_2436_, 1);
v___x_2448_ = lean_unbox(v_a_2447_);
lean_dec(v_a_2447_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; 
lean_dec_ref(v_head_2435_);
v___x_2449_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2433_, v_x_2434_);
return v___x_2449_;
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2450_, 0, v_head_2435_);
lean_ctor_set(v___x_2450_, 1, v_x_2434_);
v___x_2451_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2433_, v___x_2450_);
return v___x_2451_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object* v_x_2452_, lean_object* v_x_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2452_, v_x_2453_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object* v___x_2456_, lean_object* v_eList_2457_, lean_object* v___f_2458_, lean_object* v_x_2459_){
_start:
{
if (lean_obj_tag(v_x_2459_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v___f_2458_);
lean_dec(v_eList_2457_);
lean_dec(v___x_2456_);
v_a_2461_ = lean_ctor_get(v_x_2459_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2463_ = v_x_2459_;
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v_x_2459_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
return v___x_2467_;
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___f_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_a_2470_ = lean_ctor_get(v_x_2459_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v_x_2459_, 1);
lean_inc(v___x_2456_);
v___f_2471_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2471_, 0, v_a_2470_);
lean_closure_set(v___f_2471_, 1, v___x_2456_);
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = 0;
v___x_2474_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_2457_, v___x_2456_);
v___x_2475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2472_, v___x_2473_, v___x_2474_, v___f_2458_);
v___x_2476_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2472_, v___x_2473_, v___x_2475_, v___f_2471_);
return v___x_2476_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v___x_2477_, lean_object* v_eList_2478_, lean_object* v___f_2479_, lean_object* v_x_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v___x_2477_, v_eList_2478_, v___f_2479_, v_x_2480_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object* v_q_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_eList_2486_; lean_object* v_dList_2487_; lean_object* v___f_2488_; lean_object* v___x_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v_eList_2486_ = lean_ctor_get(v_q_2483_, 0);
lean_inc(v_eList_2486_);
v_dList_2487_ = lean_ctor_get(v_q_2483_, 1);
lean_inc(v_dList_2487_);
lean_dec_ref(v_q_2483_);
v___f_2488_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_2489_ = lean_box(0);
v___f_2490_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2490_, 0, v___x_2489_);
lean_closure_set(v___f_2490_, 1, v_eList_2486_);
lean_closure_set(v___f_2490_, 2, v___f_2488_);
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = 0;
v___x_2493_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_2487_, v___x_2489_);
v___x_2494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2491_, v___x_2492_, v___x_2493_, v___f_2488_);
v___x_2495_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2491_, v___x_2492_, v___x_2494_, v___f_2490_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object* v_q_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2496_, v___y_2497_);
lean_dec(v___y_2497_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object* v___y_2500_, lean_object* v_x_2501_){
_start:
{
if (lean_obj_tag(v_x_2501_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2511_; 
v_a_2503_ = lean_ctor_get(v_x_2501_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_x_2501_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2505_ = v_x_2501_;
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v_x_2501_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v_producers_2513_; lean_object* v_consumers_2514_; uint8_t v_closed_2515_; lean_object* v___x_2516_; lean_object* v___f_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_a_2512_ = lean_ctor_get(v_x_2501_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v_x_2501_, 1);
v_producers_2513_ = lean_ctor_get(v_a_2512_, 0);
lean_inc_ref(v_producers_2513_);
v_consumers_2514_ = lean_ctor_get(v_a_2512_, 1);
lean_inc_ref(v_consumers_2514_);
v_closed_2515_ = lean_ctor_get_uint8(v_a_2512_, sizeof(void*)*2);
lean_dec(v_a_2512_);
v___x_2516_ = lean_box(v_closed_2515_);
lean_inc(v___y_2500_);
v___f_2517_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2517_, 0, v_producers_2513_);
lean_closure_set(v___f_2517_, 1, v___x_2516_);
lean_closure_set(v___f_2517_, 2, v___y_2500_);
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = 0;
v___x_2520_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_2514_, v___y_2500_);
v___x_2521_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2518_, v___x_2519_, v___x_2520_, v___f_2517_);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object* v___y_2522_, lean_object* v_x_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2522_, v_x_2523_);
lean_dec(v___y_2522_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object* v___y_2526_){
_start:
{
lean_object* v___f_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_inc(v___y_2526_);
v___f_2528_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2528_, 0, v___y_2526_);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = 0;
v___x_2531_ = lean_st_ref_get(v___y_2526_);
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
v___x_2534_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2529_, v___x_2530_, v___x_2533_, v___f_2528_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2535_);
lean_dec(v___y_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object* v_ch_2543_){
_start:
{
lean_object* v___f_2544_; lean_object* v___f_2545_; lean_object* v___f_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___f_2544_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0));
lean_inc_ref_n(v_ch_2543_, 2);
v___f_2545_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2545_, 0, v___f_2544_);
lean_closure_set(v___f_2545_, 1, v_ch_2543_);
v___f_2546_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1));
v___f_2547_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2));
v___x_2548_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2548_, 0, lean_box(0));
lean_closure_set(v___x_2548_, 1, lean_box(0));
lean_closure_set(v___x_2548_, 2, v_ch_2543_);
lean_closure_set(v___x_2548_, 3, v___f_2546_);
v___x_2549_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2549_, 0, lean_box(0));
lean_closure_set(v___x_2549_, 1, lean_box(0));
lean_closure_set(v___x_2549_, 2, v_ch_2543_);
lean_closure_set(v___x_2549_, 3, v___f_2547_);
v___x_2550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___f_2545_);
lean_ctor_set(v___x_2550_, 2, v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object* v_00_u03b1_2551_, lean_object* v_ch_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object* v_00_u03b1_2554_, lean_object* v_q_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2555_, v___y_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_q_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_2559_, v_q_2560_, v___y_2561_);
lean_dec(v___y_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object* v_00_u03b1_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2565_, v_x_2566_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_2570_, v_x_2571_, v_x_2572_, v___y_2573_);
lean_dec(v___y_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object* v_c_2576_, uint8_t v_b_2577_){
_start:
{
lean_object* v_promise_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v_promise_2579_ = lean_ctor_get(v_c_2576_, 0);
v___x_2580_ = lean_box(v_b_2577_);
v___x_2581_ = lean_io_promise_resolve(v___x_2580_, v_promise_2579_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object* v_c_2582_, lean_object* v_b_2583_, lean_object* v_a_2584_){
_start:
{
uint8_t v_b_boxed_2585_; lean_object* v_res_2586_; 
v_b_boxed_2585_ = lean_unbox(v_b_2583_);
v_res_2586_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2582_, v_b_boxed_2585_);
lean_dec_ref(v_c_2582_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object* v_00_u03b1_2587_, lean_object* v_c_2588_, uint8_t v_b_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2588_, v_b_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object* v_00_u03b1_2592_, lean_object* v_c_2593_, lean_object* v_b_2594_, lean_object* v_a_2595_){
_start:
{
uint8_t v_b_boxed_2596_; lean_object* v_res_2597_; 
v_b_boxed_2596_ = lean_unbox(v_b_2594_);
v_res_2597_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(v_00_u03b1_2592_, v_c_2593_, v_b_boxed_2596_);
lean_dec_ref(v_c_2593_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object* v_x_2598_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_box(0);
v___x_2601_ = lean_st_mk_ref(v___x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2602_);
lean_dec(v_x_2602_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object* v_n_2605_, lean_object* v_f_2606_, lean_object* v_xs_2607_, lean_object* v_k_2608_, lean_object* v_acc_2609_){
_start:
{
uint8_t v___x_2611_; 
v___x_2611_ = lean_nat_dec_lt(v_k_2608_, v_n_2605_);
if (v___x_2611_ == 0)
{
lean_dec(v_k_2608_);
lean_dec_ref(v_f_2606_);
return v_acc_2609_;
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2612_ = lean_array_fget_borrowed(v_xs_2607_, v_k_2608_);
lean_inc_ref(v_f_2606_);
lean_inc(v___x_2612_);
v___x_2613_ = lean_apply_2(v_f_2606_, v___x_2612_, lean_box(0));
v___x_2614_ = lean_unsigned_to_nat(1u);
v___x_2615_ = lean_nat_add(v_k_2608_, v___x_2614_);
lean_dec(v_k_2608_);
v___x_2616_ = lean_array_push(v_acc_2609_, v___x_2613_);
v_k_2608_ = v___x_2615_;
v_acc_2609_ = v___x_2616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_2618_, lean_object* v_f_2619_, lean_object* v_xs_2620_, lean_object* v_k_2621_, lean_object* v_acc_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2618_, v_f_2619_, v_xs_2620_, v_k_2621_, v_acc_2622_);
lean_dec_ref(v_xs_2620_);
lean_dec(v_n_2618_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object* v_capacity_2628_){
_start:
{
lean_object* v___f_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___f_2630_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0));
lean_inc(v_capacity_2628_);
v___x_2631_ = l_Array_range(v_capacity_2628_);
v___x_2632_ = lean_unsigned_to_nat(0u);
v___x_2633_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1));
v___x_2634_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_2628_, v___f_2630_, v___x_2631_, v___x_2632_, v___x_2633_);
lean_dec_ref(v___x_2631_);
v___x_2635_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2636_ = 0;
v___x_2637_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2635_);
lean_ctor_set(v___x_2637_, 2, v_capacity_2628_);
lean_ctor_set(v___x_2637_, 3, v___x_2634_);
lean_ctor_set(v___x_2637_, 4, v___x_2632_);
lean_ctor_set(v___x_2637_, 5, v___x_2632_);
lean_ctor_set(v___x_2637_, 6, v___x_2632_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*7, v___x_2636_);
v___x_2638_ = l_Std_Mutex_new___redArg(v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object* v_capacity_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object* v_00_u03b1_2642_, lean_object* v_capacity_2643_, lean_object* v_hcap_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2643_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object* v_00_u03b1_2647_, lean_object* v_capacity_2648_, lean_object* v_hcap_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(v_00_u03b1_2647_, v_capacity_2648_, v_hcap_2649_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object* v_00_u03b1_2652_, lean_object* v_00_u03b2_2653_, lean_object* v_n_2654_, lean_object* v_f_2655_, lean_object* v_xs_2656_, lean_object* v_k_2657_, lean_object* v_h_2658_, lean_object* v_acc_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2654_, v_f_2655_, v_xs_2656_, v_k_2657_, v_acc_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_2662_, lean_object* v_00_u03b2_2663_, lean_object* v_n_2664_, lean_object* v_f_2665_, lean_object* v_xs_2666_, lean_object* v_k_2667_, lean_object* v_h_2668_, lean_object* v_acc_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_2662_, v_00_u03b2_2663_, v_n_2664_, v_f_2665_, v_xs_2666_, v_k_2667_, v_h_2668_, v_acc_2669_);
lean_dec_ref(v_xs_2666_);
lean_dec(v_n_2664_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object* v_idx_2672_, lean_object* v_cap_2673_){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2674_ = lean_unsigned_to_nat(1u);
v___x_2675_ = lean_nat_add(v_idx_2672_, v___x_2674_);
v___x_2676_ = lean_nat_dec_eq(v___x_2675_, v_cap_2673_);
if (v___x_2676_ == 0)
{
return v___x_2675_;
}
else
{
lean_object* v___x_2677_; 
lean_dec(v___x_2675_);
v___x_2677_ = lean_unsigned_to_nat(0u);
return v___x_2677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object* v_idx_2678_, lean_object* v_cap_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(v_idx_2678_, v_cap_2679_);
lean_dec(v_cap_2679_);
lean_dec(v_idx_2678_);
return v_res_2680_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object* v_v_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_st_2685_; lean_object* v___y_2686_; lean_object* v___x_2689_; lean_object* v_producers_2690_; lean_object* v_consumers_2691_; lean_object* v_capacity_2692_; lean_object* v_buf_2693_; lean_object* v_bufCount_2694_; lean_object* v_sendIdx_2695_; lean_object* v_recvIdx_2696_; uint8_t v_closed_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2723_; 
v___x_2689_ = lean_st_ref_get(v_a_2682_);
v_producers_2690_ = lean_ctor_get(v___x_2689_, 0);
v_consumers_2691_ = lean_ctor_get(v___x_2689_, 1);
v_capacity_2692_ = lean_ctor_get(v___x_2689_, 2);
v_buf_2693_ = lean_ctor_get(v___x_2689_, 3);
v_bufCount_2694_ = lean_ctor_get(v___x_2689_, 4);
v_sendIdx_2695_ = lean_ctor_get(v___x_2689_, 5);
v_recvIdx_2696_ = lean_ctor_get(v___x_2689_, 6);
v_closed_2697_ = lean_ctor_get_uint8(v___x_2689_, sizeof(void*)*7);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2699_ = v___x_2689_;
v_isShared_2700_ = v_isSharedCheck_2723_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_recvIdx_2696_);
lean_inc(v_sendIdx_2695_);
lean_inc(v_bufCount_2694_);
lean_inc(v_buf_2693_);
lean_inc(v_capacity_2692_);
lean_inc(v_consumers_2691_);
lean_inc(v_producers_2690_);
lean_dec(v___x_2689_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2723_;
goto v_resetjp_2698_;
}
v___jp_2684_:
{
lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = lean_st_ref_swap(v___y_2686_, v_st_2685_);
lean_dec(v___x_2687_);
v___x_2688_ = 1;
return v___x_2688_;
}
v_resetjp_2698_:
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_nat_dec_eq(v_bufCount_2694_, v_capacity_2692_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___y_2708_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2702_ = lean_array_fget_borrowed(v_buf_2693_, v_sendIdx_2695_);
v___x_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_v_2681_);
v___x_2704_ = lean_st_ref_swap(v___x_2702_, v___x_2703_);
lean_dec(v___x_2704_);
v___x_2705_ = lean_unsigned_to_nat(1u);
v___x_2706_ = lean_nat_add(v_bufCount_2694_, v___x_2705_);
lean_dec(v_bufCount_2694_);
v___x_2719_ = lean_nat_add(v_sendIdx_2695_, v___x_2705_);
lean_dec(v_sendIdx_2695_);
v___x_2720_ = lean_nat_dec_eq(v___x_2719_, v_capacity_2692_);
if (v___x_2720_ == 0)
{
v___y_2708_ = v___x_2719_;
goto v___jp_2707_;
}
else
{
lean_object* v___x_2721_; 
lean_dec(v___x_2719_);
v___x_2721_ = lean_unsigned_to_nat(0u);
v___y_2708_ = v___x_2721_;
goto v___jp_2707_;
}
v___jp_2707_:
{
lean_object* v___x_2710_; 
lean_inc(v_recvIdx_2696_);
lean_inc(v___y_2708_);
lean_inc(v___x_2706_);
lean_inc_ref(v_buf_2693_);
lean_inc(v_capacity_2692_);
lean_inc_ref(v_consumers_2691_);
lean_inc_ref(v_producers_2690_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 5, v___y_2708_);
lean_ctor_set(v___x_2699_, 4, v___x_2706_);
v___x_2710_ = v___x_2699_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_producers_2690_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_consumers_2691_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v_capacity_2692_);
lean_ctor_set(v_reuseFailAlloc_2718_, 3, v_buf_2693_);
lean_ctor_set(v_reuseFailAlloc_2718_, 4, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2718_, 5, v___y_2708_);
lean_ctor_set(v_reuseFailAlloc_2718_, 6, v_recvIdx_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, sizeof(void*)*7, v_closed_2697_);
v___x_2710_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_2691_);
if (lean_obj_tag(v___x_2711_) == 1)
{
lean_object* v_val_2712_; lean_object* v_fst_2713_; lean_object* v_snd_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec_ref(v___x_2710_);
v_val_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v_fst_2713_ = lean_ctor_get(v_val_2712_, 0);
lean_inc(v_fst_2713_);
v_snd_2714_ = lean_ctor_get(v_val_2712_, 1);
lean_inc(v_snd_2714_);
lean_dec(v_val_2712_);
v___x_2715_ = 1;
v___x_2716_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_2713_, v___x_2715_);
lean_dec(v_fst_2713_);
v___x_2717_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2717_, 0, v_producers_2690_);
lean_ctor_set(v___x_2717_, 1, v_snd_2714_);
lean_ctor_set(v___x_2717_, 2, v_capacity_2692_);
lean_ctor_set(v___x_2717_, 3, v_buf_2693_);
lean_ctor_set(v___x_2717_, 4, v___x_2706_);
lean_ctor_set(v___x_2717_, 5, v___y_2708_);
lean_ctor_set(v___x_2717_, 6, v_recvIdx_2696_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*7, v_closed_2697_);
v_st_2685_ = v___x_2717_;
v___y_2686_ = v_a_2682_;
goto v___jp_2684_;
}
else
{
lean_dec(v___x_2711_);
lean_dec(v___y_2708_);
lean_dec(v___x_2706_);
lean_dec(v_recvIdx_2696_);
lean_dec_ref(v_buf_2693_);
lean_dec(v_capacity_2692_);
lean_dec_ref(v_producers_2690_);
v_st_2685_ = v___x_2710_;
v___y_2686_ = v_a_2682_;
goto v___jp_2684_;
}
}
}
}
else
{
uint8_t v___x_2722_; 
lean_del_object(v___x_2699_);
lean_dec(v_recvIdx_2696_);
lean_dec(v_sendIdx_2695_);
lean_dec(v_bufCount_2694_);
lean_dec_ref(v_buf_2693_);
lean_dec(v_capacity_2692_);
lean_dec_ref(v_consumers_2691_);
lean_dec_ref(v_producers_2690_);
lean_dec(v_v_2681_);
v___x_2722_ = 0;
return v___x_2722_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
uint8_t v_res_2727_; lean_object* v_r_2728_; 
v_res_2727_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2724_, v_a_2725_);
lean_dec(v_a_2725_);
v_r_2728_ = lean_box(v_res_2727_);
return v_r_2728_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object* v_00_u03b1_2729_, lean_object* v_v_2730_, lean_object* v_a_2731_){
_start:
{
uint8_t v___x_2733_; 
v___x_2733_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2730_, v_a_2731_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_2734_, lean_object* v_v_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
uint8_t v_res_2738_; lean_object* v_r_2739_; 
v_res_2738_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(v_00_u03b1_2734_, v_v_2735_, v_a_2736_);
lean_dec(v_a_2736_);
v_r_2739_ = lean_box(v_res_2738_);
return v_r_2739_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object* v_v_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; uint8_t v_closed_2744_; 
v___x_2743_ = lean_st_ref_get(v___y_2741_);
v_closed_2744_ = lean_ctor_get_uint8(v___x_2743_, sizeof(void*)*7);
lean_dec(v___x_2743_);
if (v_closed_2744_ == 0)
{
uint8_t v___x_2745_; 
v___x_2745_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2740_, v___y_2741_);
return v___x_2745_;
}
else
{
uint8_t v___x_2746_; 
lean_dec(v_v_2740_);
v___x_2746_ = 0;
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v_res_2750_; lean_object* v_r_2751_; 
v_res_2750_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2747_, v___y_2748_);
lean_dec(v___y_2748_);
v_r_2751_ = lean_box(v_res_2750_);
return v_r_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object* v_ch_2752_, lean_object* v_v_2753_){
_start:
{
lean_object* v___f_2755_; lean_object* v___x_2756_; 
v___f_2755_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2755_, 0, v_v_2753_);
v___x_2756_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2752_, v___f_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object* v_ch_2757_, lean_object* v_v_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2757_, v_v_2758_);
return v_res_2760_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object* v_00_u03b1_2761_, lean_object* v_ch_2762_, lean_object* v_v_2763_){
_start:
{
lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2762_, v_v_2763_);
v___x_2766_ = lean_unbox(v___x_2765_);
lean_dec(v___x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_ch_2768_, lean_object* v_v_2769_, lean_object* v_a_2770_){
_start:
{
uint8_t v_res_2771_; lean_object* v_r_2772_; 
v_res_2771_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(v_00_u03b1_2767_, v_ch_2768_, v_v_2769_);
v_r_2772_ = lean_box(v_res_2771_);
return v_r_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(lean_object* v_v_2773_, lean_object* v___f_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v___x_2777_; uint8_t v_closed_2778_; 
v___x_2777_ = lean_st_ref_get(v___y_2775_);
v_closed_2778_ = lean_ctor_get_uint8(v___x_2777_, sizeof(void*)*7);
lean_dec(v___x_2777_);
if (v_closed_2778_ == 0)
{
uint8_t v___x_2779_; 
v___x_2779_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2773_, v___y_2775_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v_producers_2782_; lean_object* v_consumers_2783_; lean_object* v_capacity_2784_; lean_object* v_buf_2785_; lean_object* v_bufCount_2786_; lean_object* v_sendIdx_2787_; lean_object* v_recvIdx_2788_; uint8_t v_closed_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2801_; 
v___x_2780_ = lean_io_promise_new();
v___x_2781_ = lean_st_ref_take(v___y_2775_);
v_producers_2782_ = lean_ctor_get(v___x_2781_, 0);
v_consumers_2783_ = lean_ctor_get(v___x_2781_, 1);
v_capacity_2784_ = lean_ctor_get(v___x_2781_, 2);
v_buf_2785_ = lean_ctor_get(v___x_2781_, 3);
v_bufCount_2786_ = lean_ctor_get(v___x_2781_, 4);
v_sendIdx_2787_ = lean_ctor_get(v___x_2781_, 5);
v_recvIdx_2788_ = lean_ctor_get(v___x_2781_, 6);
v_closed_2789_ = lean_ctor_get_uint8(v___x_2781_, sizeof(void*)*7);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2791_ = v___x_2781_;
v_isShared_2792_ = v_isSharedCheck_2801_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_recvIdx_2788_);
lean_inc(v_sendIdx_2787_);
lean_inc(v_bufCount_2786_);
lean_inc(v_buf_2785_);
lean_inc(v_capacity_2784_);
lean_inc(v_consumers_2783_);
lean_inc(v_producers_2782_);
lean_dec(v___x_2781_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2801_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
lean_inc(v___x_2780_);
v___x_2793_ = l_Std_Queue_enqueue___redArg(v___x_2780_, v_producers_2782_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2793_);
v___x_2795_ = v___x_2791_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_consumers_2783_);
lean_ctor_set(v_reuseFailAlloc_2800_, 2, v_capacity_2784_);
lean_ctor_set(v_reuseFailAlloc_2800_, 3, v_buf_2785_);
lean_ctor_set(v_reuseFailAlloc_2800_, 4, v_bufCount_2786_);
lean_ctor_set(v_reuseFailAlloc_2800_, 5, v_sendIdx_2787_);
lean_ctor_set(v_reuseFailAlloc_2800_, 6, v_recvIdx_2788_);
lean_ctor_set_uint8(v_reuseFailAlloc_2800_, sizeof(void*)*7, v_closed_2789_);
v___x_2795_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2796_ = lean_st_ref_put(v___y_2775_, v___x_2795_);
v___x_2797_ = lean_io_promise_result_opt(v___x_2780_);
lean_dec(v___x_2780_);
v___x_2798_ = lean_unsigned_to_nat(0u);
v___x_2799_ = lean_io_bind_task(v___x_2797_, v___f_2774_, v___x_2798_, v___x_2779_);
return v___x_2799_;
}
}
}
else
{
lean_object* v___x_2802_; 
lean_dec_ref(v___f_2774_);
v___x_2802_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_2802_;
}
}
else
{
lean_object* v___x_2803_; 
lean_dec_ref(v___f_2774_);
lean_dec(v_v_2773_);
v___x_2803_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_2804_, lean_object* v___f_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(v_v_2804_, v___f_2805_, v___y_2806_);
lean_dec(v___y_2806_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(lean_object* v_ch_2809_, lean_object* v_v_2810_, lean_object* v_res_2811_){
_start:
{
if (lean_obj_tag(v_res_2811_) == 0)
{
lean_dec(v_v_2810_);
lean_dec_ref(v_ch_2809_);
goto v___jp_2813_;
}
else
{
lean_object* v_val_2815_; uint8_t v___x_2816_; 
v_val_2815_ = lean_ctor_get(v_res_2811_, 0);
v___x_2816_ = lean_unbox(v_val_2815_);
if (v___x_2816_ == 0)
{
lean_dec(v_v_2810_);
lean_dec_ref(v_ch_2809_);
goto v___jp_2813_;
}
else
{
lean_object* v___x_2817_; 
v___x_2817_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2809_, v_v_2810_);
return v___x_2817_;
}
}
v___jp_2813_:
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_2818_, lean_object* v_v_2819_, lean_object* v_res_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(v_ch_2818_, v_v_2819_, v_res_2820_);
lean_dec(v_res_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(lean_object* v_ch_2823_, lean_object* v_v_2824_){
_start:
{
lean_object* v___f_2826_; lean_object* v___f_2827_; lean_object* v___x_2828_; 
lean_inc(v_v_2824_);
lean_inc_ref(v_ch_2823_);
v___f_2826_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2826_, 0, v_ch_2823_);
lean_closure_set(v___f_2826_, 1, v_v_2824_);
v___f_2827_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2827_, 0, v_v_2824_);
lean_closure_set(v___f_2827_, 1, v___f_2826_);
v___x_2828_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2823_, v___f_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(lean_object* v_ch_2829_, lean_object* v_v_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2829_, v_v_2830_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_object* v_00_u03b1_2833_, lean_object* v_ch_2834_, lean_object* v_v_2835_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2834_, v_v_2835_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(lean_object* v_00_u03b1_2838_, lean_object* v_ch_2839_, lean_object* v_v_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(v_00_u03b1_2838_, v_ch_2839_, v_v_2840_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(uint8_t v___x_2843_, lean_object* v_as_2844_, size_t v_sz_2845_, size_t v_i_2846_, lean_object* v_b_2847_){
_start:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_usize_dec_lt(v_i_2846_, v_sz_2845_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; 
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v_b_2847_);
return v___x_2850_;
}
else
{
lean_object* v___x_2851_; lean_object* v_a_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; size_t v___x_2855_; size_t v___x_2856_; 
v___x_2851_ = lean_box(0);
v_a_2852_ = lean_array_uget_borrowed(v_as_2844_, v_i_2846_);
v___x_2853_ = lean_box(v___x_2843_);
v___x_2854_ = lean_io_promise_resolve(v___x_2853_, v_a_2852_);
v___x_2855_ = ((size_t)1ULL);
v___x_2856_ = lean_usize_add(v_i_2846_, v___x_2855_);
v_i_2846_ = v___x_2856_;
v_b_2847_ = v___x_2851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg___boxed(lean_object* v___x_2858_, lean_object* v_as_2859_, lean_object* v_sz_2860_, lean_object* v_i_2861_, lean_object* v_b_2862_, lean_object* v___y_2863_){
_start:
{
uint8_t v___x_1818__boxed_2864_; size_t v_sz_boxed_2865_; size_t v_i_boxed_2866_; lean_object* v_res_2867_; 
v___x_1818__boxed_2864_ = lean_unbox(v___x_2858_);
v_sz_boxed_2865_ = lean_unbox_usize(v_sz_2860_);
lean_dec(v_sz_2860_);
v_i_boxed_2866_ = lean_unbox_usize(v_i_2861_);
lean_dec(v_i_2861_);
v_res_2867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v___x_1818__boxed_2864_, v_as_2859_, v_sz_boxed_2865_, v_i_boxed_2866_, v_b_2862_);
lean_dec_ref(v_as_2859_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t v___x_2868_, lean_object* v_as_2869_, size_t v_sz_2870_, size_t v_i_2871_, lean_object* v_b_2872_){
_start:
{
uint8_t v___x_2874_; 
v___x_2874_ = lean_usize_dec_lt(v_i_2871_, v_sz_2870_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v_b_2872_);
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; lean_object* v_a_2877_; lean_object* v___x_2878_; size_t v___x_2879_; size_t v___x_2880_; 
v___x_2876_ = lean_box(0);
v_a_2877_ = lean_array_uget_borrowed(v_as_2869_, v_i_2871_);
v___x_2878_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_2877_, v___x_2868_);
v___x_2879_ = ((size_t)1ULL);
v___x_2880_ = lean_usize_add(v_i_2871_, v___x_2879_);
v_i_2871_ = v___x_2880_;
v_b_2872_ = v___x_2876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_2882_, lean_object* v_as_2883_, lean_object* v_sz_2884_, lean_object* v_i_2885_, lean_object* v_b_2886_, lean_object* v___y_2887_){
_start:
{
uint8_t v___x_1840__boxed_2888_; size_t v_sz_boxed_2889_; size_t v_i_boxed_2890_; lean_object* v_res_2891_; 
v___x_1840__boxed_2888_ = lean_unbox(v___x_2882_);
v_sz_boxed_2889_ = lean_unbox_usize(v_sz_2884_);
lean_dec(v_sz_2884_);
v_i_boxed_2890_ = lean_unbox_usize(v_i_2885_);
lean_dec(v_i_2885_);
v_res_2891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1840__boxed_2888_, v_as_2883_, v_sz_boxed_2889_, v_i_boxed_2890_, v_b_2886_);
lean_dec_ref(v_as_2883_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_2892_){
_start:
{
lean_object* v___x_2894_; uint8_t v_closed_2895_; 
v___x_2894_ = lean_st_ref_get(v___y_2892_);
v_closed_2895_ = lean_ctor_get_uint8(v___x_2894_, sizeof(void*)*7);
if (v_closed_2895_ == 0)
{
lean_object* v_producers_2896_; lean_object* v_consumers_2897_; lean_object* v_capacity_2898_; lean_object* v_buf_2899_; lean_object* v_bufCount_2900_; lean_object* v_sendIdx_2901_; lean_object* v_recvIdx_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2928_; 
v_producers_2896_ = lean_ctor_get(v___x_2894_, 0);
v_consumers_2897_ = lean_ctor_get(v___x_2894_, 1);
v_capacity_2898_ = lean_ctor_get(v___x_2894_, 2);
v_buf_2899_ = lean_ctor_get(v___x_2894_, 3);
v_bufCount_2900_ = lean_ctor_get(v___x_2894_, 4);
v_sendIdx_2901_ = lean_ctor_get(v___x_2894_, 5);
v_recvIdx_2902_ = lean_ctor_get(v___x_2894_, 6);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2904_ = v___x_2894_;
v_isShared_2905_ = v_isSharedCheck_2928_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_recvIdx_2902_);
lean_inc(v_sendIdx_2901_);
lean_inc(v_bufCount_2900_);
lean_inc(v_buf_2899_);
lean_inc(v_capacity_2898_);
lean_inc(v_consumers_2897_);
lean_inc(v_producers_2896_);
lean_dec(v___x_2894_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2928_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; size_t v_sz_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v___x_2906_ = l_Std_Queue_toArray___redArg(v_consumers_2897_);
v___x_2907_ = lean_box(0);
v_sz_2908_ = lean_array_size(v___x_2906_);
v___x_2909_ = ((size_t)0ULL);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_2895_, v___x_2906_, v_sz_2908_, v___x_2909_, v___x_2907_);
lean_dec_ref(v___x_2906_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v___x_2911_; size_t v_sz_2912_; lean_object* v___x_2913_; 
lean_dec_ref_known(v___x_2910_, 1);
v___x_2911_ = l_Std_Queue_toArray___redArg(v_producers_2896_);
v_sz_2912_ = lean_array_size(v___x_2911_);
v___x_2913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v_closed_2895_, v___x_2911_, v_sz_2912_, v___x_2909_, v___x_2907_);
lean_dec_ref(v___x_2911_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2926_; 
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v___x_2913_, 0);
lean_dec(v_unused_2927_);
v___x_2915_ = v___x_2913_;
v_isShared_2916_ = v_isSharedCheck_2926_;
goto v_resetjp_2914_;
}
else
{
lean_dec(v___x_2913_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2926_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; uint8_t v___x_2918_; lean_object* v___x_2920_; 
v___x_2917_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2918_ = 1;
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 1, v___x_2917_);
lean_ctor_set(v___x_2904_, 0, v___x_2917_);
v___x_2920_ = v___x_2904_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_capacity_2898_);
lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_buf_2899_);
lean_ctor_set(v_reuseFailAlloc_2925_, 4, v_bufCount_2900_);
lean_ctor_set(v_reuseFailAlloc_2925_, 5, v_sendIdx_2901_);
lean_ctor_set(v_reuseFailAlloc_2925_, 6, v_recvIdx_2902_);
v___x_2920_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2923_; 
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*7, v___x_2918_);
v___x_2921_ = lean_st_ref_swap(v___y_2892_, v___x_2920_);
lean_dec(v___x_2921_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v___x_2907_);
v___x_2923_ = v___x_2915_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2907_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_del_object(v___x_2904_);
lean_dec(v_recvIdx_2902_);
lean_dec(v_sendIdx_2901_);
lean_dec(v_bufCount_2900_);
lean_dec_ref(v_buf_2899_);
lean_dec(v_capacity_2898_);
return v___x_2913_;
}
}
else
{
lean_del_object(v___x_2904_);
lean_dec(v_recvIdx_2902_);
lean_dec(v_sendIdx_2901_);
lean_dec(v_bufCount_2900_);
lean_dec_ref(v_buf_2899_);
lean_dec(v_capacity_2898_);
lean_dec_ref(v_producers_2896_);
return v___x_2910_;
}
}
}
else
{
uint8_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v___x_2894_);
v___x_2929_ = 1;
v___x_2930_ = lean_box(v___x_2929_);
v___x_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_2932_);
lean_dec(v___y_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_2936_){
_start:
{
lean_object* v___f_2938_; lean_object* v___x_2939_; 
v___f_2938_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_2939_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_2936_, v___f_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_2943_, lean_object* v_ch_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_2947_, lean_object* v_ch_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_2947_, v_ch_2948_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_2951_, uint8_t v___x_2952_, lean_object* v_as_2953_, size_t v_sz_2954_, size_t v_i_2955_, lean_object* v_b_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_2952_, v_as_2953_, v_sz_2954_, v_i_2955_, v_b_2956_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_2960_, lean_object* v___x_2961_, lean_object* v_as_2962_, lean_object* v_sz_2963_, lean_object* v_i_2964_, lean_object* v_b_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
uint8_t v___x_1942__boxed_2968_; size_t v_sz_boxed_2969_; size_t v_i_boxed_2970_; lean_object* v_res_2971_; 
v___x_1942__boxed_2968_ = lean_unbox(v___x_2961_);
v_sz_boxed_2969_ = lean_unbox_usize(v_sz_2963_);
lean_dec(v_sz_2963_);
v_i_boxed_2970_ = lean_unbox_usize(v_i_2964_);
lean_dec(v_i_2964_);
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_2960_, v___x_1942__boxed_2968_, v_as_2962_, v_sz_boxed_2969_, v_i_boxed_2970_, v_b_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v_as_2962_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1(lean_object* v_00_u03b1_2972_, uint8_t v___x_2973_, lean_object* v_as_2974_, size_t v_sz_2975_, size_t v_i_2976_, lean_object* v_b_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v___x_2973_, v_as_2974_, v_sz_2975_, v_i_2976_, v_b_2977_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_2981_, lean_object* v___x_2982_, lean_object* v_as_2983_, lean_object* v_sz_2984_, lean_object* v_i_2985_, lean_object* v_b_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v___x_1953__boxed_2989_; size_t v_sz_boxed_2990_; size_t v_i_boxed_2991_; lean_object* v_res_2992_; 
v___x_1953__boxed_2989_ = lean_unbox(v___x_2982_);
v_sz_boxed_2990_ = lean_unbox_usize(v_sz_2984_);
lean_dec(v_sz_2984_);
v_i_boxed_2991_ = lean_unbox_usize(v_i_2985_);
lean_dec(v_i_2985_);
v_res_2992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1(v_00_u03b1_2981_, v___x_1953__boxed_2989_, v_as_2983_, v_sz_boxed_2990_, v_i_boxed_2991_, v_b_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v_as_2983_);
return v_res_2992_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; uint8_t v_closed_2996_; 
v___x_2995_ = lean_st_ref_get(v___y_2993_);
v_closed_2996_ = lean_ctor_get_uint8(v___x_2995_, sizeof(void*)*7);
lean_dec(v___x_2995_);
return v_closed_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
uint8_t v_res_2999_; lean_object* v_r_3000_; 
v_res_2999_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_2997_);
lean_dec(v___y_2997_);
v_r_3000_ = lean_box(v_res_2999_);
return v_r_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_3002_){
_start:
{
lean_object* v___f_3004_; lean_object* v___x_3005_; 
v___f_3004_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_3005_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3002_, v___f_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3006_);
return v_res_3008_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_3009_, lean_object* v_ch_3010_){
_start:
{
lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3010_);
v___x_3013_ = lean_unbox(v___x_3012_);
lean_dec(v___x_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_3014_, lean_object* v_ch_3015_, lean_object* v_a_3016_){
_start:
{
uint8_t v_res_3017_; lean_object* v_r_3018_; 
v_res_3017_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_3014_, v_ch_3015_);
v_r_3018_ = lean_box(v_res_3017_);
return v_r_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_toPure_3022_; lean_object* v___x_3023_; 
v_toPure_3022_ = lean_ctor_get(v_toApplicative_3019_, 1);
lean_inc(v_toPure_3022_);
lean_dec_ref(v_toApplicative_3019_);
v___x_3023_ = lean_apply_2(v_toPure_3022_, lean_box(0), v_a_3020_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_3024_, lean_object* v_toBind_3025_, lean_object* v___f_3026_, lean_object* v_____r_3027_, lean_object* v_st_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
lean_inc(v___y_3029_);
v___x_3030_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_3030_, 0, lean_box(0));
lean_closure_set(v___x_3030_, 1, lean_box(0));
lean_closure_set(v___x_3030_, 2, v___y_3029_);
lean_closure_set(v___x_3030_, 3, v_st_3028_);
v___x_3031_ = lean_apply_2(v_inst_3024_, lean_box(0), v___x_3030_);
v___x_3032_ = lean_apply_4(v_toBind_3025_, lean_box(0), lean_box(0), v___x_3031_, v___f_3026_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_inst_3033_, lean_object* v_toBind_3034_, lean_object* v___f_3035_, lean_object* v_____r_3036_, lean_object* v_st_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3033_, v_toBind_3034_, v___f_3035_, v_____r_3036_, v_st_3037_, v___y_3038_);
lean_dec(v___y_3038_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_3040_, lean_object* v_consumers_3041_, lean_object* v_capacity_3042_, lean_object* v_buf_3043_, lean_object* v___x_3044_, lean_object* v_sendIdx_3045_, lean_object* v___y_3046_, uint8_t v_closed_3047_, lean_object* v___f_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3051_, 0, v_snd_3040_);
lean_ctor_set(v___x_3051_, 1, v_consumers_3041_);
lean_ctor_set(v___x_3051_, 2, v_capacity_3042_);
lean_ctor_set(v___x_3051_, 3, v_buf_3043_);
lean_ctor_set(v___x_3051_, 4, v___x_3044_);
lean_ctor_set(v___x_3051_, 5, v_sendIdx_3045_);
lean_ctor_set(v___x_3051_, 6, v___y_3046_);
lean_ctor_set_uint8(v___x_3051_, sizeof(void*)*7, v_closed_3047_);
v___x_3052_ = lean_box(0);
lean_inc(v_a_3049_);
v___x_3053_ = lean_apply_3(v___f_3048_, v___x_3052_, v___x_3051_, v_a_3049_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_3054_, lean_object* v_consumers_3055_, lean_object* v_capacity_3056_, lean_object* v_buf_3057_, lean_object* v___x_3058_, lean_object* v_sendIdx_3059_, lean_object* v___y_3060_, lean_object* v_closed_3061_, lean_object* v___f_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
uint8_t v_closed_boxed_3065_; lean_object* v_res_3066_; 
v_closed_boxed_3065_ = lean_unbox(v_closed_3061_);
v_res_3066_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3054_, v_consumers_3055_, v_capacity_3056_, v_buf_3057_, v___x_3058_, v_sendIdx_3059_, v___y_3060_, v_closed_boxed_3065_, v___f_3062_, v_a_3063_, v_a_3064_);
lean_dec(v_a_3063_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3067_, lean_object* v_inst_3068_, lean_object* v_toBind_3069_, lean_object* v_bufCount_3070_, lean_object* v_producers_3071_, lean_object* v_consumers_3072_, lean_object* v_capacity_3073_, lean_object* v_buf_3074_, lean_object* v_sendIdx_3075_, uint8_t v_closed_3076_, lean_object* v_a_3077_, uint8_t v___x_3078_, lean_object* v_inst_3079_, lean_object* v_recvIdx_3080_, lean_object* v___x_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___y_3086_; lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___f_3083_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3083_, 0, v_toApplicative_3067_);
lean_closure_set(v___f_3083_, 1, v_a_3082_);
lean_inc_ref(v___f_3083_);
lean_inc(v_toBind_3069_);
lean_inc(v_inst_3068_);
v___f_3084_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3084_, 0, v_inst_3068_);
lean_closure_set(v___f_3084_, 1, v_toBind_3069_);
lean_closure_set(v___f_3084_, 2, v___f_3083_);
v___x_3102_ = lean_unsigned_to_nat(1u);
v___x_3103_ = lean_nat_add(v_recvIdx_3080_, v___x_3102_);
v___x_3104_ = lean_nat_dec_eq(v___x_3103_, v_capacity_3073_);
if (v___x_3104_ == 0)
{
lean_dec(v___x_3081_);
v___y_3086_ = v___x_3103_;
goto v___jp_3085_;
}
else
{
lean_dec(v___x_3103_);
v___y_3086_ = v___x_3081_;
goto v___jp_3085_;
}
v___jp_3085_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3087_ = lean_unsigned_to_nat(1u);
v___x_3088_ = lean_nat_sub(v_bufCount_3070_, v___x_3087_);
lean_inc(v___y_3086_);
lean_inc(v_sendIdx_3075_);
lean_inc(v___x_3088_);
lean_inc_ref(v_buf_3074_);
lean_inc(v_capacity_3073_);
lean_inc_ref(v_consumers_3072_);
lean_inc_ref(v_producers_3071_);
v___x_3089_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3089_, 0, v_producers_3071_);
lean_ctor_set(v___x_3089_, 1, v_consumers_3072_);
lean_ctor_set(v___x_3089_, 2, v_capacity_3073_);
lean_ctor_set(v___x_3089_, 3, v_buf_3074_);
lean_ctor_set(v___x_3089_, 4, v___x_3088_);
lean_ctor_set(v___x_3089_, 5, v_sendIdx_3075_);
lean_ctor_set(v___x_3089_, 6, v___y_3086_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*7, v_closed_3076_);
v___x_3090_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3071_);
if (lean_obj_tag(v___x_3090_) == 1)
{
lean_object* v_val_3091_; lean_object* v_fst_3092_; lean_object* v_snd_3093_; lean_object* v___x_3094_; lean_object* v___f_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref_known(v___x_3089_, 7);
lean_dec_ref(v___f_3083_);
lean_dec(v_inst_3068_);
v_val_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_val_3091_);
lean_dec_ref_known(v___x_3090_, 1);
v_fst_3092_ = lean_ctor_get(v_val_3091_, 0);
lean_inc(v_fst_3092_);
v_snd_3093_ = lean_ctor_get(v_val_3091_, 1);
lean_inc(v_snd_3093_);
lean_dec(v_val_3091_);
v___x_3094_ = lean_box(v_closed_3076_);
lean_inc(v_a_3077_);
v___f_3095_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3095_, 0, v_snd_3093_);
lean_closure_set(v___f_3095_, 1, v_consumers_3072_);
lean_closure_set(v___f_3095_, 2, v_capacity_3073_);
lean_closure_set(v___f_3095_, 3, v_buf_3074_);
lean_closure_set(v___f_3095_, 4, v___x_3088_);
lean_closure_set(v___f_3095_, 5, v_sendIdx_3075_);
lean_closure_set(v___f_3095_, 6, v___y_3086_);
lean_closure_set(v___f_3095_, 7, v___x_3094_);
lean_closure_set(v___f_3095_, 8, v___f_3084_);
lean_closure_set(v___f_3095_, 9, v_a_3077_);
v___x_3096_ = lean_box(v___x_3078_);
v___x_3097_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3097_, 0, lean_box(0));
lean_closure_set(v___x_3097_, 1, v___x_3096_);
lean_closure_set(v___x_3097_, 2, v_fst_3092_);
v___x_3098_ = lean_apply_2(v_inst_3079_, lean_box(0), v___x_3097_);
v___x_3099_ = lean_apply_4(v_toBind_3069_, lean_box(0), lean_box(0), v___x_3098_, v___f_3095_);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_dec(v___x_3090_);
lean_dec(v___x_3088_);
lean_dec(v___y_3086_);
lean_dec_ref(v___f_3084_);
lean_dec(v_inst_3079_);
lean_dec(v_sendIdx_3075_);
lean_dec_ref(v_buf_3074_);
lean_dec(v_capacity_3073_);
lean_dec_ref(v_consumers_3072_);
v___x_3100_ = lean_box(0);
v___x_3101_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3068_, v_toBind_3069_, v___f_3083_, v___x_3100_, v___x_3089_, v_a_3077_);
return v___x_3101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3105_, lean_object* v_inst_3106_, lean_object* v_toBind_3107_, lean_object* v_bufCount_3108_, lean_object* v_producers_3109_, lean_object* v_consumers_3110_, lean_object* v_capacity_3111_, lean_object* v_buf_3112_, lean_object* v_sendIdx_3113_, lean_object* v_closed_3114_, lean_object* v_a_3115_, lean_object* v___x_3116_, lean_object* v_inst_3117_, lean_object* v_recvIdx_3118_, lean_object* v___x_3119_, lean_object* v_a_3120_){
_start:
{
uint8_t v_closed_boxed_3121_; uint8_t v___x_543__boxed_3122_; lean_object* v_res_3123_; 
v_closed_boxed_3121_ = lean_unbox(v_closed_3114_);
v___x_543__boxed_3122_ = lean_unbox(v___x_3116_);
v_res_3123_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3105_, v_inst_3106_, v_toBind_3107_, v_bufCount_3108_, v_producers_3109_, v_consumers_3110_, v_capacity_3111_, v_buf_3112_, v_sendIdx_3113_, v_closed_boxed_3121_, v_a_3115_, v___x_543__boxed_3122_, v_inst_3117_, v_recvIdx_3118_, v___x_3119_, v_a_3120_);
lean_dec(v_recvIdx_3118_);
lean_dec(v_a_3115_);
lean_dec(v_bufCount_3108_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3124_, lean_object* v_inst_3125_, lean_object* v_toBind_3126_, lean_object* v_a_3127_, lean_object* v_inst_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v_producers_3130_; lean_object* v_consumers_3131_; lean_object* v_capacity_3132_; lean_object* v_buf_3133_; lean_object* v_bufCount_3134_; lean_object* v_sendIdx_3135_; lean_object* v_recvIdx_3136_; uint8_t v_closed_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v_producers_3130_ = lean_ctor_get(v_a_3129_, 0);
lean_inc_ref(v_producers_3130_);
v_consumers_3131_ = lean_ctor_get(v_a_3129_, 1);
lean_inc_ref(v_consumers_3131_);
v_capacity_3132_ = lean_ctor_get(v_a_3129_, 2);
lean_inc(v_capacity_3132_);
v_buf_3133_ = lean_ctor_get(v_a_3129_, 3);
lean_inc_ref(v_buf_3133_);
v_bufCount_3134_ = lean_ctor_get(v_a_3129_, 4);
lean_inc(v_bufCount_3134_);
v_sendIdx_3135_ = lean_ctor_get(v_a_3129_, 5);
lean_inc(v_sendIdx_3135_);
v_recvIdx_3136_ = lean_ctor_get(v_a_3129_, 6);
lean_inc(v_recvIdx_3136_);
v_closed_3137_ = lean_ctor_get_uint8(v_a_3129_, sizeof(void*)*7);
lean_dec_ref(v_a_3129_);
v___x_3138_ = lean_unsigned_to_nat(0u);
v___x_3139_ = lean_nat_dec_eq(v_bufCount_3134_, v___x_3138_);
if (v___x_3139_ == 0)
{
uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3140_ = 1;
v___x_3141_ = lean_box(v_closed_3137_);
v___x_3142_ = lean_box(v___x_3140_);
lean_inc(v_recvIdx_3136_);
lean_inc(v_a_3127_);
lean_inc_ref(v_buf_3133_);
lean_inc(v_toBind_3126_);
lean_inc(v_inst_3125_);
v___f_3143_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3143_, 0, v_toApplicative_3124_);
lean_closure_set(v___f_3143_, 1, v_inst_3125_);
lean_closure_set(v___f_3143_, 2, v_toBind_3126_);
lean_closure_set(v___f_3143_, 3, v_bufCount_3134_);
lean_closure_set(v___f_3143_, 4, v_producers_3130_);
lean_closure_set(v___f_3143_, 5, v_consumers_3131_);
lean_closure_set(v___f_3143_, 6, v_capacity_3132_);
lean_closure_set(v___f_3143_, 7, v_buf_3133_);
lean_closure_set(v___f_3143_, 8, v_sendIdx_3135_);
lean_closure_set(v___f_3143_, 9, v___x_3141_);
lean_closure_set(v___f_3143_, 10, v_a_3127_);
lean_closure_set(v___f_3143_, 11, v___x_3142_);
lean_closure_set(v___f_3143_, 12, v_inst_3128_);
lean_closure_set(v___f_3143_, 13, v_recvIdx_3136_);
lean_closure_set(v___f_3143_, 14, v___x_3138_);
v___x_3144_ = lean_array_fget(v_buf_3133_, v_recvIdx_3136_);
lean_dec(v_recvIdx_3136_);
lean_dec_ref(v_buf_3133_);
v___x_3145_ = lean_box(0);
v___x_3146_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3146_, 0, lean_box(0));
lean_closure_set(v___x_3146_, 1, lean_box(0));
lean_closure_set(v___x_3146_, 2, v___x_3144_);
lean_closure_set(v___x_3146_, 3, v___x_3145_);
v___x_3147_ = lean_apply_2(v_inst_3125_, lean_box(0), v___x_3146_);
v___x_3148_ = lean_apply_4(v_toBind_3126_, lean_box(0), lean_box(0), v___x_3147_, v___f_3143_);
return v___x_3148_;
}
else
{
lean_object* v_toPure_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec(v_recvIdx_3136_);
lean_dec(v_sendIdx_3135_);
lean_dec(v_bufCount_3134_);
lean_dec_ref(v_buf_3133_);
lean_dec(v_capacity_3132_);
lean_dec_ref(v_consumers_3131_);
lean_dec_ref(v_producers_3130_);
lean_dec(v_inst_3128_);
lean_dec(v_toBind_3126_);
lean_dec(v_inst_3125_);
v_toPure_3149_ = lean_ctor_get(v_toApplicative_3124_, 1);
lean_inc(v_toPure_3149_);
lean_dec_ref(v_toApplicative_3124_);
v___x_3150_ = lean_box(0);
v___x_3151_ = lean_apply_2(v_toPure_3149_, lean_box(0), v___x_3150_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_3152_, lean_object* v_inst_3153_, lean_object* v_toBind_3154_, lean_object* v_a_3155_, lean_object* v_inst_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(v_toApplicative_3152_, v_inst_3153_, v_toBind_3154_, v_a_3155_, v_inst_3156_, v_a_3157_);
lean_dec(v_a_3155_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3159_, lean_object* v_inst_3160_, lean_object* v_inst_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v_toApplicative_3163_; lean_object* v_toBind_3164_; lean_object* v___f_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v_toApplicative_3163_ = lean_ctor_get(v_inst_3159_, 0);
lean_inc_ref(v_toApplicative_3163_);
v_toBind_3164_ = lean_ctor_get(v_inst_3159_, 1);
lean_inc_n(v_toBind_3164_, 2);
lean_dec_ref(v_inst_3159_);
lean_inc_n(v_a_3162_, 2);
lean_inc(v_inst_3160_);
v___f_3165_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_3165_, 0, v_toApplicative_3163_);
lean_closure_set(v___f_3165_, 1, v_inst_3160_);
lean_closure_set(v___f_3165_, 2, v_toBind_3164_);
lean_closure_set(v___f_3165_, 3, v_a_3162_);
lean_closure_set(v___f_3165_, 4, v_inst_3161_);
v___x_3166_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3166_, 0, lean_box(0));
lean_closure_set(v___x_3166_, 1, lean_box(0));
lean_closure_set(v___x_3166_, 2, v_a_3162_);
v___x_3167_ = lean_apply_2(v_inst_3160_, lean_box(0), v___x_3166_);
v___x_3168_ = lean_apply_4(v_toBind_3164_, lean_box(0), lean_box(0), v___x_3167_, v___f_3165_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3169_, v_inst_3170_, v_inst_3171_, v_a_3172_);
lean_dec(v_a_3172_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3174_, lean_object* v_00_u03b1_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3176_, v_inst_3177_, v_inst_3178_, v_a_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object* v_m_3181_, lean_object* v_00_u03b1_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(v_m_3181_, v_00_u03b1_3182_, v_inst_3183_, v_inst_3184_, v_inst_3185_, v_a_3186_);
lean_dec(v_a_3186_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3188_){
_start:
{
lean_object* v___x_3190_; lean_object* v_producers_3191_; lean_object* v_consumers_3192_; lean_object* v_capacity_3193_; lean_object* v_buf_3194_; lean_object* v_bufCount_3195_; lean_object* v_sendIdx_3196_; lean_object* v_recvIdx_3197_; uint8_t v_closed_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3230_; 
v___x_3190_ = lean_st_ref_get(v_a_3188_);
v_producers_3191_ = lean_ctor_get(v___x_3190_, 0);
v_consumers_3192_ = lean_ctor_get(v___x_3190_, 1);
v_capacity_3193_ = lean_ctor_get(v___x_3190_, 2);
v_buf_3194_ = lean_ctor_get(v___x_3190_, 3);
v_bufCount_3195_ = lean_ctor_get(v___x_3190_, 4);
v_sendIdx_3196_ = lean_ctor_get(v___x_3190_, 5);
v_recvIdx_3197_ = lean_ctor_get(v___x_3190_, 6);
v_closed_3198_ = lean_ctor_get_uint8(v___x_3190_, sizeof(void*)*7);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3200_ = v___x_3190_;
v_isShared_3201_ = v_isSharedCheck_3230_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_recvIdx_3197_);
lean_inc(v_sendIdx_3196_);
lean_inc(v_bufCount_3195_);
lean_inc(v_buf_3194_);
lean_inc(v_capacity_3193_);
lean_inc(v_consumers_3192_);
lean_inc(v_producers_3191_);
lean_dec(v___x_3190_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3230_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; uint8_t v___x_3203_; 
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = lean_nat_dec_eq(v_bufCount_3195_, v___x_3202_);
if (v___x_3203_ == 0)
{
uint8_t v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v_st_3209_; lean_object* v___y_3210_; lean_object* v___y_3213_; lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3204_ = 1;
v___x_3205_ = lean_array_fget_borrowed(v_buf_3194_, v_recvIdx_3197_);
v___x_3206_ = lean_box(0);
v___x_3207_ = lean_st_ref_swap(v___x_3205_, v___x_3206_);
v___x_3226_ = lean_unsigned_to_nat(1u);
v___x_3227_ = lean_nat_add(v_recvIdx_3197_, v___x_3226_);
lean_dec(v_recvIdx_3197_);
v___x_3228_ = lean_nat_dec_eq(v___x_3227_, v_capacity_3193_);
if (v___x_3228_ == 0)
{
v___y_3213_ = v___x_3227_;
goto v___jp_3212_;
}
else
{
lean_dec(v___x_3227_);
v___y_3213_ = v___x_3202_;
goto v___jp_3212_;
}
v___jp_3208_:
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_st_ref_swap(v___y_3210_, v_st_3209_);
lean_dec(v___x_3211_);
return v___x_3207_;
}
v___jp_3212_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3214_ = lean_unsigned_to_nat(1u);
v___x_3215_ = lean_nat_sub(v_bufCount_3195_, v___x_3214_);
lean_dec(v_bufCount_3195_);
lean_inc(v___y_3213_);
lean_inc(v_sendIdx_3196_);
lean_inc(v___x_3215_);
lean_inc_ref(v_buf_3194_);
lean_inc(v_capacity_3193_);
lean_inc_ref(v_consumers_3192_);
lean_inc_ref(v_producers_3191_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 6, v___y_3213_);
lean_ctor_set(v___x_3200_, 4, v___x_3215_);
v___x_3217_ = v___x_3200_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_producers_3191_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_consumers_3192_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_capacity_3193_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_buf_3194_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3225_, 5, v_sendIdx_3196_);
lean_ctor_set(v_reuseFailAlloc_3225_, 6, v___y_3213_);
lean_ctor_set_uint8(v_reuseFailAlloc_3225_, sizeof(void*)*7, v_closed_3198_);
v___x_3217_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3191_);
if (lean_obj_tag(v___x_3218_) == 1)
{
lean_object* v_val_3219_; lean_object* v_fst_3220_; lean_object* v_snd_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
lean_dec_ref(v___x_3217_);
v_val_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_val_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v_fst_3220_ = lean_ctor_get(v_val_3219_, 0);
lean_inc(v_fst_3220_);
v_snd_3221_ = lean_ctor_get(v_val_3219_, 1);
lean_inc(v_snd_3221_);
lean_dec(v_val_3219_);
v___x_3222_ = lean_box(v___x_3204_);
v___x_3223_ = lean_io_promise_resolve(v___x_3222_, v_fst_3220_);
lean_dec(v_fst_3220_);
v___x_3224_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3224_, 0, v_snd_3221_);
lean_ctor_set(v___x_3224_, 1, v_consumers_3192_);
lean_ctor_set(v___x_3224_, 2, v_capacity_3193_);
lean_ctor_set(v___x_3224_, 3, v_buf_3194_);
lean_ctor_set(v___x_3224_, 4, v___x_3215_);
lean_ctor_set(v___x_3224_, 5, v_sendIdx_3196_);
lean_ctor_set(v___x_3224_, 6, v___y_3213_);
lean_ctor_set_uint8(v___x_3224_, sizeof(void*)*7, v_closed_3198_);
v_st_3209_ = v___x_3224_;
v___y_3210_ = v_a_3188_;
goto v___jp_3208_;
}
else
{
lean_dec(v___x_3218_);
lean_dec(v___x_3215_);
lean_dec(v___y_3213_);
lean_dec(v_sendIdx_3196_);
lean_dec_ref(v_buf_3194_);
lean_dec(v_capacity_3193_);
lean_dec_ref(v_consumers_3192_);
v_st_3209_ = v___x_3217_;
v___y_3210_ = v_a_3188_;
goto v___jp_3208_;
}
}
}
}
else
{
lean_object* v___x_3229_; 
lean_del_object(v___x_3200_);
lean_dec(v_recvIdx_3197_);
lean_dec(v_sendIdx_3196_);
lean_dec(v_bufCount_3195_);
lean_dec_ref(v_buf_3194_);
lean_dec(v_capacity_3193_);
lean_dec_ref(v_consumers_3192_);
lean_dec_ref(v_producers_3191_);
v___x_3229_ = lean_box(0);
return v___x_3229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3231_);
lean_dec(v_a_3231_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3238_, lean_object* v_a_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3238_, v_a_3239_);
lean_dec(v_a_3239_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3243_){
_start:
{
lean_object* v___f_3245_; lean_object* v___x_3246_; 
v___f_3245_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3246_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3243_, v___f_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3247_, lean_object* v_a_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3247_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3250_, lean_object* v_ch_3251_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3251_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3254_, lean_object* v_ch_3255_, lean_object* v_a_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3254_, v_ch_3255_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3259_);
if (lean_obj_tag(v___x_3261_) == 1)
{
lean_object* v___x_3262_; 
lean_dec_ref(v___f_3258_);
v___x_3262_ = lean_task_pure(v___x_3261_);
return v___x_3262_;
}
else
{
lean_object* v___x_3263_; uint8_t v_closed_3264_; 
lean_dec(v___x_3261_);
v___x_3263_ = lean_st_ref_get(v___y_3259_);
v_closed_3264_ = lean_ctor_get_uint8(v___x_3263_, sizeof(void*)*7);
lean_dec(v___x_3263_);
if (v_closed_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v_producers_3267_; lean_object* v_consumers_3268_; lean_object* v_capacity_3269_; lean_object* v_buf_3270_; lean_object* v_bufCount_3271_; lean_object* v_sendIdx_3272_; lean_object* v_recvIdx_3273_; uint8_t v_closed_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3288_; 
v___x_3265_ = lean_io_promise_new();
v___x_3266_ = lean_st_ref_take(v___y_3259_);
v_producers_3267_ = lean_ctor_get(v___x_3266_, 0);
v_consumers_3268_ = lean_ctor_get(v___x_3266_, 1);
v_capacity_3269_ = lean_ctor_get(v___x_3266_, 2);
v_buf_3270_ = lean_ctor_get(v___x_3266_, 3);
v_bufCount_3271_ = lean_ctor_get(v___x_3266_, 4);
v_sendIdx_3272_ = lean_ctor_get(v___x_3266_, 5);
v_recvIdx_3273_ = lean_ctor_get(v___x_3266_, 6);
v_closed_3274_ = lean_ctor_get_uint8(v___x_3266_, sizeof(void*)*7);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3276_ = v___x_3266_;
v_isShared_3277_ = v_isSharedCheck_3288_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_recvIdx_3273_);
lean_inc(v_sendIdx_3272_);
lean_inc(v_bufCount_3271_);
lean_inc(v_buf_3270_);
lean_inc(v_capacity_3269_);
lean_inc(v_consumers_3268_);
lean_inc(v_producers_3267_);
lean_dec(v___x_3266_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3288_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3278_ = lean_box(0);
lean_inc(v___x_3265_);
v___x_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3265_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = l_Std_Queue_enqueue___redArg(v___x_3279_, v_consumers_3268_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 1, v___x_3280_);
v___x_3282_ = v___x_3276_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_producers_3267_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3287_, 2, v_capacity_3269_);
lean_ctor_set(v_reuseFailAlloc_3287_, 3, v_buf_3270_);
lean_ctor_set(v_reuseFailAlloc_3287_, 4, v_bufCount_3271_);
lean_ctor_set(v_reuseFailAlloc_3287_, 5, v_sendIdx_3272_);
lean_ctor_set(v_reuseFailAlloc_3287_, 6, v_recvIdx_3273_);
lean_ctor_set_uint8(v_reuseFailAlloc_3287_, sizeof(void*)*7, v_closed_3274_);
v___x_3282_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3283_ = lean_st_ref_put(v___y_3259_, v___x_3282_);
v___x_3284_ = lean_io_promise_result_opt(v___x_3265_);
lean_dec(v___x_3265_);
v___x_3285_ = lean_unsigned_to_nat(0u);
v___x_3286_ = lean_io_bind_task(v___x_3284_, v___f_3258_, v___x_3285_, v_closed_3264_);
return v___x_3286_;
}
}
}
else
{
lean_object* v___x_3289_; 
lean_dec_ref(v___f_3258_);
v___x_3289_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3290_, v___y_3291_);
lean_dec(v___y_3291_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3294_, lean_object* v_res_3295_){
_start:
{
if (lean_obj_tag(v_res_3295_) == 0)
{
lean_dec_ref(v_ch_3294_);
goto v___jp_3297_;
}
else
{
lean_object* v_val_3299_; uint8_t v___x_3300_; 
v_val_3299_ = lean_ctor_get(v_res_3295_, 0);
v___x_3300_ = lean_unbox(v_val_3299_);
if (v___x_3300_ == 0)
{
lean_dec_ref(v_ch_3294_);
goto v___jp_3297_;
}
else
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3294_);
return v___x_3301_;
}
}
v___jp_3297_:
{
lean_object* v___x_3298_; 
v___x_3298_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3302_, lean_object* v_res_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3302_, v_res_3303_);
lean_dec(v_res_3303_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3306_){
_start:
{
lean_object* v___f_3308_; lean_object* v___f_3309_; lean_object* v___x_3310_; 
lean_inc_ref(v_ch_3306_);
v___f_3308_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3308_, 0, v_ch_3306_);
v___f_3309_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3309_, 0, v___f_3308_);
v___x_3310_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3306_, v___f_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3311_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3314_, lean_object* v_ch_3315_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3315_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3318_, lean_object* v_ch_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3318_, v_ch_3319_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3322_, lean_object* v_a_3323_){
_start:
{
uint8_t v___y_3325_; lean_object* v_bufCount_3329_; uint8_t v_closed_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
v_bufCount_3329_ = lean_ctor_get(v_a_3323_, 4);
v_closed_3330_ = lean_ctor_get_uint8(v_a_3323_, sizeof(void*)*7);
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = lean_nat_dec_eq(v_bufCount_3329_, v___x_3331_);
if (v___x_3332_ == 0)
{
uint8_t v___x_3333_; 
v___x_3333_ = 1;
v___y_3325_ = v___x_3333_;
goto v___jp_3324_;
}
else
{
v___y_3325_ = v_closed_3330_;
goto v___jp_3324_;
}
v___jp_3324_:
{
lean_object* v_toPure_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v_toPure_3326_ = lean_ctor_get(v_toApplicative_3322_, 1);
lean_inc(v_toPure_3326_);
lean_dec_ref(v_toApplicative_3322_);
v___x_3327_ = lean_box(v___y_3325_);
v___x_3328_ = lean_apply_2(v_toPure_3326_, lean_box(0), v___x_3327_);
return v___x_3328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3334_, v_a_3335_);
lean_dec_ref(v_a_3335_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_toApplicative_3340_; lean_object* v_toBind_3341_; lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v_toApplicative_3340_ = lean_ctor_get(v_inst_3337_, 0);
lean_inc_ref(v_toApplicative_3340_);
v_toBind_3341_ = lean_ctor_get(v_inst_3337_, 1);
lean_inc(v_toBind_3341_);
lean_dec_ref(v_inst_3337_);
v___f_3342_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3342_, 0, v_toApplicative_3340_);
lean_inc(v_a_3339_);
v___x_3343_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3343_, 0, lean_box(0));
lean_closure_set(v___x_3343_, 1, lean_box(0));
lean_closure_set(v___x_3343_, 2, v_a_3339_);
v___x_3344_ = lean_apply_2(v_inst_3338_, lean_box(0), v___x_3343_);
v___x_3345_ = lean_apply_4(v_toBind_3341_, lean_box(0), lean_box(0), v___x_3344_, v___f_3342_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object* v_inst_3346_, lean_object* v_inst_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(v_inst_3346_, v_inst_3347_, v_a_3348_);
lean_dec(v_a_3348_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3350_, lean_object* v_00_u03b1_3351_, lean_object* v_inst_3352_, lean_object* v_inst_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v_toApplicative_3355_; lean_object* v_toBind_3356_; lean_object* v___f_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_toApplicative_3355_ = lean_ctor_get(v_inst_3352_, 0);
lean_inc_ref(v_toApplicative_3355_);
v_toBind_3356_ = lean_ctor_get(v_inst_3352_, 1);
lean_inc(v_toBind_3356_);
lean_dec_ref(v_inst_3352_);
v___f_3357_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3357_, 0, v_toApplicative_3355_);
lean_inc(v_a_3354_);
v___x_3358_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3358_, 0, lean_box(0));
lean_closure_set(v___x_3358_, 1, lean_box(0));
lean_closure_set(v___x_3358_, 2, v_a_3354_);
v___x_3359_ = lean_apply_2(v_inst_3353_, lean_box(0), v___x_3358_);
v___x_3360_ = lean_apply_4(v_toBind_3356_, lean_box(0), lean_box(0), v___x_3359_, v___f_3357_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object* v_m_3361_, lean_object* v_00_u03b1_3362_, lean_object* v_inst_3363_, lean_object* v_inst_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(v_m_3361_, v_00_u03b1_3362_, v_inst_3363_, v_inst_3364_, v_a_3365_);
lean_dec(v_a_3365_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3367_){
_start:
{
lean_object* v___x_3369_; lean_object* v_producers_3370_; lean_object* v_consumers_3371_; lean_object* v_capacity_3372_; lean_object* v_buf_3373_; lean_object* v_bufCount_3374_; lean_object* v_sendIdx_3375_; lean_object* v_recvIdx_3376_; uint8_t v_closed_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3411_; 
v___x_3369_ = lean_st_ref_get(v_a_3367_);
v_producers_3370_ = lean_ctor_get(v___x_3369_, 0);
v_consumers_3371_ = lean_ctor_get(v___x_3369_, 1);
v_capacity_3372_ = lean_ctor_get(v___x_3369_, 2);
v_buf_3373_ = lean_ctor_get(v___x_3369_, 3);
v_bufCount_3374_ = lean_ctor_get(v___x_3369_, 4);
v_sendIdx_3375_ = lean_ctor_get(v___x_3369_, 5);
v_recvIdx_3376_ = lean_ctor_get(v___x_3369_, 6);
v_closed_3377_ = lean_ctor_get_uint8(v___x_3369_, sizeof(void*)*7);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3379_ = v___x_3369_;
v_isShared_3380_ = v_isSharedCheck_3411_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_recvIdx_3376_);
lean_inc(v_sendIdx_3375_);
lean_inc(v_bufCount_3374_);
lean_inc(v_buf_3373_);
lean_inc(v_capacity_3372_);
lean_inc(v_consumers_3371_);
lean_inc(v_producers_3370_);
lean_dec(v___x_3369_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3411_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = lean_nat_dec_eq(v_bufCount_3374_, v___x_3381_);
if (v___x_3382_ == 0)
{
uint8_t v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v_st_3388_; lean_object* v___y_3389_; lean_object* v___y_3393_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3383_ = 1;
v___x_3384_ = lean_array_fget_borrowed(v_buf_3373_, v_recvIdx_3376_);
v___x_3385_ = lean_box(0);
v___x_3386_ = lean_st_ref_swap(v___x_3384_, v___x_3385_);
v___x_3406_ = lean_unsigned_to_nat(1u);
v___x_3407_ = lean_nat_add(v_recvIdx_3376_, v___x_3406_);
lean_dec(v_recvIdx_3376_);
v___x_3408_ = lean_nat_dec_eq(v___x_3407_, v_capacity_3372_);
if (v___x_3408_ == 0)
{
v___y_3393_ = v___x_3407_;
goto v___jp_3392_;
}
else
{
lean_dec(v___x_3407_);
v___y_3393_ = v___x_3381_;
goto v___jp_3392_;
}
v___jp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_st_ref_swap(v___y_3389_, v_st_3388_);
lean_dec(v___x_3390_);
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3386_);
return v___x_3391_;
}
v___jp_3392_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
v___x_3394_ = lean_unsigned_to_nat(1u);
v___x_3395_ = lean_nat_sub(v_bufCount_3374_, v___x_3394_);
lean_dec(v_bufCount_3374_);
lean_inc(v___y_3393_);
lean_inc(v_sendIdx_3375_);
lean_inc(v___x_3395_);
lean_inc_ref(v_buf_3373_);
lean_inc(v_capacity_3372_);
lean_inc_ref(v_consumers_3371_);
lean_inc_ref(v_producers_3370_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 6, v___y_3393_);
lean_ctor_set(v___x_3379_, 4, v___x_3395_);
v___x_3397_ = v___x_3379_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_producers_3370_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_consumers_3371_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v_capacity_3372_);
lean_ctor_set(v_reuseFailAlloc_3405_, 3, v_buf_3373_);
lean_ctor_set(v_reuseFailAlloc_3405_, 4, v___x_3395_);
lean_ctor_set(v_reuseFailAlloc_3405_, 5, v_sendIdx_3375_);
lean_ctor_set(v_reuseFailAlloc_3405_, 6, v___y_3393_);
lean_ctor_set_uint8(v_reuseFailAlloc_3405_, sizeof(void*)*7, v_closed_3377_);
v___x_3397_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3370_);
if (lean_obj_tag(v___x_3398_) == 1)
{
lean_object* v_val_3399_; lean_object* v_fst_3400_; lean_object* v_snd_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec_ref(v___x_3397_);
v_val_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_val_3399_);
lean_dec_ref_known(v___x_3398_, 1);
v_fst_3400_ = lean_ctor_get(v_val_3399_, 0);
lean_inc(v_fst_3400_);
v_snd_3401_ = lean_ctor_get(v_val_3399_, 1);
lean_inc(v_snd_3401_);
lean_dec(v_val_3399_);
v___x_3402_ = lean_box(v___x_3383_);
v___x_3403_ = lean_io_promise_resolve(v___x_3402_, v_fst_3400_);
lean_dec(v_fst_3400_);
v___x_3404_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3404_, 0, v_snd_3401_);
lean_ctor_set(v___x_3404_, 1, v_consumers_3371_);
lean_ctor_set(v___x_3404_, 2, v_capacity_3372_);
lean_ctor_set(v___x_3404_, 3, v_buf_3373_);
lean_ctor_set(v___x_3404_, 4, v___x_3395_);
lean_ctor_set(v___x_3404_, 5, v_sendIdx_3375_);
lean_ctor_set(v___x_3404_, 6, v___y_3393_);
lean_ctor_set_uint8(v___x_3404_, sizeof(void*)*7, v_closed_3377_);
v_st_3388_ = v___x_3404_;
v___y_3389_ = v_a_3367_;
goto v___jp_3387_;
}
else
{
lean_dec(v___x_3398_);
lean_dec(v___x_3395_);
lean_dec(v___y_3393_);
lean_dec(v_sendIdx_3375_);
lean_dec_ref(v_buf_3373_);
lean_dec(v_capacity_3372_);
lean_dec_ref(v_consumers_3371_);
v_st_3388_ = v___x_3397_;
v___y_3389_ = v_a_3367_;
goto v___jp_3387_;
}
}
}
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_del_object(v___x_3379_);
lean_dec(v_recvIdx_3376_);
lean_dec(v_sendIdx_3375_);
lean_dec(v_bufCount_3374_);
lean_dec_ref(v_buf_3373_);
lean_dec(v_capacity_3372_);
lean_dec_ref(v_consumers_3371_);
lean_dec_ref(v_producers_3370_);
v___x_3409_ = lean_box(0);
v___x_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3412_);
lean_dec(v_a_3412_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3416_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3419_, lean_object* v_a_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3419_, v_a_3420_);
lean_dec(v_a_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3423_, lean_object* v_lose_3424_){
_start:
{
lean_object* v_finished_3426_; lean_object* v_promise_3427_; lean_object* v___x_3428_; uint8_t v___y_3430_; uint8_t v___x_3438_; 
v_finished_3426_ = lean_ctor_get(v_w_3423_, 0);
v_promise_3427_ = lean_ctor_get(v_w_3423_, 1);
v___x_3428_ = lean_st_ref_take(v_finished_3426_);
v___x_3438_ = lean_unbox(v___x_3428_);
lean_dec(v___x_3428_);
if (v___x_3438_ == 0)
{
uint8_t v___x_3439_; 
v___x_3439_ = 1;
v___y_3430_ = v___x_3439_;
goto v___jp_3429_;
}
else
{
uint8_t v___x_3440_; 
v___x_3440_ = 0;
v___y_3430_ = v___x_3440_;
goto v___jp_3429_;
}
v___jp_3429_:
{
uint8_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3431_ = 1;
v___x_3432_ = lean_box(v___x_3431_);
v___x_3433_ = lean_st_ref_put(v_finished_3426_, v___x_3432_);
if (v___y_3430_ == 0)
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_apply_1(v_lose_3424_, lean_box(0));
return v___x_3434_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_dec_ref(v_lose_3424_);
v___x_3435_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__2));
v___x_3436_ = lean_io_promise_resolve(v___x_3435_, v_promise_3427_);
v___x_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
return v___x_3437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3441_, lean_object* v_lose_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3441_, v_lose_3442_);
lean_dec_ref(v_w_3441_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3445_, lean_object* v_w_3446_, lean_object* v_lose_3447_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3446_, v_lose_3447_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3450_, lean_object* v_w_3451_, lean_object* v_lose_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3450_, v_w_3451_, v_lose_3452_);
lean_dec_ref(v_w_3451_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3455_, lean_object* v_lose_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_finished_3459_; lean_object* v_promise_3460_; lean_object* v___x_3461_; uint8_t v___y_3463_; uint8_t v___x_3479_; 
v_finished_3459_ = lean_ctor_get(v_w_3455_, 0);
v_promise_3460_ = lean_ctor_get(v_w_3455_, 1);
v___x_3461_ = lean_st_ref_take(v_finished_3459_);
v___x_3479_ = lean_unbox(v___x_3461_);
lean_dec(v___x_3461_);
if (v___x_3479_ == 0)
{
uint8_t v___x_3480_; 
v___x_3480_ = 1;
v___y_3463_ = v___x_3480_;
goto v___jp_3462_;
}
else
{
uint8_t v___x_3481_; 
v___x_3481_ = 0;
v___y_3463_ = v___x_3481_;
goto v___jp_3462_;
}
v___jp_3462_:
{
uint8_t v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = 1;
v___x_3465_ = lean_box(v___x_3464_);
v___x_3466_ = lean_st_ref_put(v_finished_3459_, v___x_3465_);
if (v___y_3463_ == 0)
{
lean_object* v___x_3467_; 
lean_inc(v___y_3457_);
v___x_3467_ = lean_apply_2(v_lose_3456_, v___y_3457_, lean_box(0));
return v___x_3467_;
}
else
{
lean_object* v___x_3468_; lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref(v_lose_3456_);
v___x_3468_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3457_);
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3478_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3478_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v_a_3469_);
v___x_3474_ = lean_io_promise_resolve(v___x_3473_, v_promise_3460_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3474_);
v___x_3476_ = v___x_3471_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3482_, lean_object* v_lose_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3482_, v_lose_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v_w_3482_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3487_, lean_object* v_w_3488_, lean_object* v_lose_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3488_, v_lose_3489_, v___y_3490_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3493_, lean_object* v_w_3494_, lean_object* v_lose_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3493_, v_w_3494_, v_lose_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v_w_3494_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3499_, lean_object* v_k_3500_){
_start:
{
lean_object* v_ref_3502_; lean_object* v_mutex_3503_; lean_object* v___x_3504_; lean_object* v_r_3505_; 
v_ref_3502_ = lean_ctor_get(v_mutex_3499_, 0);
lean_inc(v_ref_3502_);
v_mutex_3503_ = lean_ctor_get(v_mutex_3499_, 1);
lean_inc(v_mutex_3503_);
lean_dec_ref(v_mutex_3499_);
v___x_3504_ = lean_io_basemutex_lock(v_mutex_3503_);
v_r_3505_ = lean_apply_2(v_k_3500_, v_ref_3502_, lean_box(0));
if (lean_obj_tag(v_r_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3514_; 
v_a_3506_ = lean_ctor_get(v_r_3505_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_r_3505_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3508_ = v_r_3505_;
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v_r_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
v___x_3510_ = lean_io_basemutex_unlock(v_mutex_3503_);
lean_dec(v_mutex_3503_);
if (v_isShared_3509_ == 0)
{
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3506_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3523_; 
v_a_3515_ = lean_ctor_get(v_r_3505_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_r_3505_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3517_ = v_r_3505_;
v_isShared_3518_ = v_isSharedCheck_3523_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v_r_3505_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3523_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3519_; lean_object* v___x_3521_; 
v___x_3519_ = lean_io_basemutex_unlock(v_mutex_3503_);
lean_dec(v_mutex_3503_);
if (v_isShared_3518_ == 0)
{
v___x_3521_ = v___x_3517_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3515_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3524_, lean_object* v_k_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3524_, v_k_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3528_, lean_object* v_00_u03b2_3529_, lean_object* v_mutex_3530_, lean_object* v_k_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3530_, v_k_3531_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3534_, lean_object* v_00_u03b2_3535_, lean_object* v_mutex_3536_, lean_object* v_k_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3534_, v_00_u03b2_3535_, v_mutex_3536_, v_k_3537_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3540_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3540_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3543_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3549_; lean_object* v_producers_3550_; lean_object* v_consumers_3551_; lean_object* v_capacity_3552_; lean_object* v_buf_3553_; lean_object* v_bufCount_3554_; lean_object* v_sendIdx_3555_; lean_object* v_recvIdx_3556_; uint8_t v_closed_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3580_; 
v___x_3549_ = lean_st_ref_get(v___y_3547_);
v_producers_3550_ = lean_ctor_get(v___x_3549_, 0);
v_consumers_3551_ = lean_ctor_get(v___x_3549_, 1);
v_capacity_3552_ = lean_ctor_get(v___x_3549_, 2);
v_buf_3553_ = lean_ctor_get(v___x_3549_, 3);
v_bufCount_3554_ = lean_ctor_get(v___x_3549_, 4);
v_sendIdx_3555_ = lean_ctor_get(v___x_3549_, 5);
v_recvIdx_3556_ = lean_ctor_get(v___x_3549_, 6);
v_closed_3557_ = lean_ctor_get_uint8(v___x_3549_, sizeof(void*)*7);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3559_ = v___x_3549_;
v_isShared_3560_ = v_isSharedCheck_3580_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_recvIdx_3556_);
lean_inc(v_sendIdx_3555_);
lean_inc(v_bufCount_3554_);
lean_inc(v_buf_3553_);
lean_inc(v_capacity_3552_);
lean_inc(v_consumers_3551_);
lean_inc(v_producers_3550_);
lean_dec(v___x_3549_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3580_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; 
v___x_3561_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3551_);
if (lean_obj_tag(v___x_3561_) == 1)
{
lean_object* v_val_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3577_; 
v_val_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3577_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_val_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3577_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v_fst_3566_; lean_object* v_snd_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v_fst_3566_ = lean_ctor_get(v_val_3562_, 0);
lean_inc(v_fst_3566_);
v_snd_3567_ = lean_ctor_get(v_val_3562_, 1);
lean_inc(v_snd_3567_);
lean_dec(v_val_3562_);
v___x_3568_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3566_, v_____do__lift_3546_);
lean_dec(v_fst_3566_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v_snd_3567_);
v___x_3570_ = v___x_3559_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_producers_3550_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_snd_3567_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v_capacity_3552_);
lean_ctor_set(v_reuseFailAlloc_3576_, 3, v_buf_3553_);
lean_ctor_set(v_reuseFailAlloc_3576_, 4, v_bufCount_3554_);
lean_ctor_set(v_reuseFailAlloc_3576_, 5, v_sendIdx_3555_);
lean_ctor_set(v_reuseFailAlloc_3576_, 6, v_recvIdx_3556_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*7, v_closed_3557_);
v___x_3570_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3571_ = lean_box(0);
v___x_3572_ = lean_st_ref_swap(v___y_3547_, v___x_3570_);
lean_dec(v___x_3572_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set_tag(v___x_3564_, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3571_);
v___x_3574_ = v___x_3564_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3571_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
lean_dec(v___x_3561_);
lean_del_object(v___x_3559_);
lean_dec(v_recvIdx_3556_);
lean_dec(v_sendIdx_3555_);
lean_dec(v_bufCount_3554_);
lean_dec_ref(v_buf_3553_);
lean_dec(v_capacity_3552_);
lean_dec_ref(v_producers_3550_);
v___x_3578_ = lean_box(0);
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
uint8_t v_____do__lift_3555__boxed_3584_; lean_object* v_res_3585_; 
v_____do__lift_3555__boxed_3584_ = lean_unbox(v_____do__lift_3581_);
v_res_3585_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3555__boxed_3584_, v___y_3582_);
lean_dec(v___y_3582_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3586_, lean_object* v___f_3587_, uint8_t v_____do__lift_3588_, lean_object* v___y_3589_){
_start:
{
if (v_____do__lift_3588_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v_producers_3593_; lean_object* v_consumers_3594_; lean_object* v_capacity_3595_; lean_object* v_buf_3596_; lean_object* v_bufCount_3597_; lean_object* v_sendIdx_3598_; lean_object* v_recvIdx_3599_; uint8_t v_closed_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3614_; 
v___x_3591_ = lean_io_promise_new();
v___x_3592_ = lean_st_ref_take(v___y_3589_);
v_producers_3593_ = lean_ctor_get(v___x_3592_, 0);
v_consumers_3594_ = lean_ctor_get(v___x_3592_, 1);
v_capacity_3595_ = lean_ctor_get(v___x_3592_, 2);
v_buf_3596_ = lean_ctor_get(v___x_3592_, 3);
v_bufCount_3597_ = lean_ctor_get(v___x_3592_, 4);
v_sendIdx_3598_ = lean_ctor_get(v___x_3592_, 5);
v_recvIdx_3599_ = lean_ctor_get(v___x_3592_, 6);
v_closed_3600_ = lean_ctor_get_uint8(v___x_3592_, sizeof(void*)*7);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3602_ = v___x_3592_;
v_isShared_3603_ = v_isSharedCheck_3614_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_recvIdx_3599_);
lean_inc(v_sendIdx_3598_);
lean_inc(v_bufCount_3597_);
lean_inc(v_buf_3596_);
lean_inc(v_capacity_3595_);
lean_inc(v_consumers_3594_);
lean_inc(v_producers_3593_);
lean_dec(v___x_3592_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3614_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3604_, 0, v_waiter_3586_);
lean_inc(v___x_3591_);
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3591_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = l_Std_Queue_enqueue___redArg(v___x_3605_, v_consumers_3594_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 1, v___x_3606_);
v___x_3608_ = v___x_3602_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_producers_3593_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_capacity_3595_);
lean_ctor_set(v_reuseFailAlloc_3613_, 3, v_buf_3596_);
lean_ctor_set(v_reuseFailAlloc_3613_, 4, v_bufCount_3597_);
lean_ctor_set(v_reuseFailAlloc_3613_, 5, v_sendIdx_3598_);
lean_ctor_set(v_reuseFailAlloc_3613_, 6, v_recvIdx_3599_);
lean_ctor_set_uint8(v_reuseFailAlloc_3613_, sizeof(void*)*7, v_closed_3600_);
v___x_3608_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3609_ = lean_st_ref_put(v___y_3589_, v___x_3608_);
v___x_3610_ = lean_io_promise_result_opt(v___x_3591_);
lean_dec(v___x_3591_);
v___x_3611_ = lean_unsigned_to_nat(0u);
v___x_3612_ = l_EIO_chainTask___redArg(v___x_3610_, v___f_3587_, v___x_3611_, v_____do__lift_3588_);
return v___x_3612_;
}
}
}
else
{
lean_object* v___x_3615_; lean_object* v_lose_3616_; lean_object* v___x_3617_; 
lean_dec_ref(v___f_3587_);
v___x_3615_ = lean_box(v_____do__lift_3588_);
v_lose_3616_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3616_, 0, v___x_3615_);
v___x_3617_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3586_, v_lose_3616_, v___y_3589_);
lean_dec_ref(v_waiter_3586_);
return v___x_3617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3618_, lean_object* v___f_3619_, lean_object* v_____do__lift_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
uint8_t v_____do__lift_3613__boxed_3623_; lean_object* v_res_3624_; 
v_____do__lift_3613__boxed_3623_ = lean_unbox(v_____do__lift_3620_);
v_res_3624_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3618_, v___f_3619_, v_____do__lift_3613__boxed_3623_, v___y_3621_);
lean_dec(v___y_3621_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; lean_object* v_bufCount_3629_; uint8_t v_closed_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v___x_3628_ = lean_st_ref_get(v___y_3626_);
v_bufCount_3629_ = lean_ctor_get(v___x_3628_, 4);
lean_inc(v_bufCount_3629_);
v_closed_3630_ = lean_ctor_get_uint8(v___x_3628_, sizeof(void*)*7);
lean_dec(v___x_3628_);
v___x_3631_ = lean_unsigned_to_nat(0u);
v___x_3632_ = lean_nat_dec_eq(v_bufCount_3629_, v___x_3631_);
lean_dec(v_bufCount_3629_);
if (v___x_3632_ == 0)
{
uint8_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = 1;
v___x_3634_ = lean_box(v___x_3633_);
lean_inc(v___y_3626_);
v___x_3635_ = lean_apply_3(v___f_3625_, v___x_3634_, v___y_3626_, lean_box(0));
return v___x_3635_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = lean_box(v_closed_3630_);
lean_inc(v___y_3626_);
v___x_3637_ = lean_apply_3(v___f_3625_, v___x_3636_, v___y_3626_, lean_box(0));
return v___x_3637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3638_, v___y_3639_);
lean_dec(v___y_3639_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3644_, lean_object* v_ch_3645_, lean_object* v_x_3646_){
_start:
{
if (lean_obj_tag(v_x_3646_) == 0)
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_dec_ref(v_ch_3645_);
lean_dec_ref(v_waiter_3644_);
v___x_3648_ = lean_box(0);
v___x_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
return v___x_3649_;
}
else
{
lean_object* v_val_3650_; uint8_t v___x_3651_; 
v_val_3650_ = lean_ctor_get(v_x_3646_, 0);
v___x_3651_ = lean_unbox(v_val_3650_);
if (v___x_3651_ == 0)
{
lean_object* v___f_3652_; lean_object* v___x_3653_; 
lean_dec_ref(v_ch_3645_);
v___f_3652_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3653_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3644_, v___f_3652_);
lean_dec_ref(v_waiter_3644_);
return v___x_3653_;
}
else
{
lean_object* v___x_3654_; 
v___x_3654_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3645_, v_waiter_3644_);
return v___x_3654_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3655_, lean_object* v_ch_3656_, lean_object* v_x_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3655_, v_ch_3656_, v_x_3657_);
lean_dec(v_x_3657_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3660_, lean_object* v_waiter_3661_){
_start:
{
lean_object* v___f_3663_; lean_object* v___f_3664_; lean_object* v___f_3665_; lean_object* v___x_3666_; 
lean_inc_ref(v_ch_3660_);
lean_inc_ref(v_waiter_3661_);
v___f_3663_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3663_, 0, v_waiter_3661_);
lean_closure_set(v___f_3663_, 1, v_ch_3660_);
v___f_3664_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3664_, 0, v_waiter_3661_);
lean_closure_set(v___f_3664_, 1, v___f_3663_);
v___f_3665_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3665_, 0, v___f_3664_);
v___x_3666_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3660_, v___f_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3667_, lean_object* v_waiter_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3667_, v_waiter_3668_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3671_, lean_object* v_ch_3672_, lean_object* v_waiter_3673_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3672_, v_waiter_3673_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3676_, lean_object* v_ch_3677_, lean_object* v_waiter_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3676_, v_ch_3677_, v_waiter_3678_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3681_, lean_object* v_x_3682_){
_start:
{
if (lean_obj_tag(v_x_3682_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3692_; 
lean_dec_ref(v_x_3681_);
v_a_3684_ = lean_ctor_get(v_x_3682_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_x_3682_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3686_ = v_x_3682_;
v_isShared_3687_ = v_isSharedCheck_3692_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v_x_3682_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3692_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
return v___x_3690_;
}
}
}
else
{
lean_object* v___x_3693_; 
lean_dec_ref_known(v_x_3682_, 1);
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v_x_3681_);
return v___x_3693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3694_, lean_object* v_x_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3694_, v_x_3695_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3698_, uint8_t v___x_3699_, lean_object* v___f_3700_, lean_object* v_____r_3701_, lean_object* v_st_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_st_ref_swap(v___y_3703_, v_st_3702_);
lean_dec(v___x_3705_);
v___x_3706_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_3707_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3698_, v___x_3699_, v___x_3706_, v___f_3700_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3708_, lean_object* v___x_3709_, lean_object* v___f_3710_, lean_object* v_____r_3711_, lean_object* v_st_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
uint8_t v___x_6366__boxed_3715_; lean_object* v_res_3716_; 
v___x_6366__boxed_3715_ = lean_unbox(v___x_3709_);
v_res_3716_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3708_, v___x_6366__boxed_3715_, v___f_3710_, v_____r_3711_, v_st_3712_, v___y_3713_);
lean_dec(v___y_3713_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3717_, lean_object* v_consumers_3718_, lean_object* v_capacity_3719_, lean_object* v_buf_3720_, lean_object* v___x_3721_, lean_object* v_sendIdx_3722_, lean_object* v___y_3723_, uint8_t v_closed_3724_, lean_object* v___f_3725_, lean_object* v_a_3726_, lean_object* v_x_3727_){
_start:
{
if (lean_obj_tag(v_x_3727_) == 0)
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v___f_3725_);
lean_dec(v___y_3723_);
lean_dec(v_sendIdx_3722_);
lean_dec(v___x_3721_);
lean_dec_ref(v_buf_3720_);
lean_dec(v_capacity_3719_);
lean_dec_ref(v_consumers_3718_);
lean_dec_ref(v_snd_3717_);
v_a_3729_ = lean_ctor_get(v_x_3727_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_x_3727_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3731_ = v_x_3727_;
v_isShared_3732_ = v_isSharedCheck_3737_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v_x_3727_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3737_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
return v___x_3735_;
}
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_dec_ref_known(v_x_3727_, 1);
v___x_3738_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3738_, 0, v_snd_3717_);
lean_ctor_set(v___x_3738_, 1, v_consumers_3718_);
lean_ctor_set(v___x_3738_, 2, v_capacity_3719_);
lean_ctor_set(v___x_3738_, 3, v_buf_3720_);
lean_ctor_set(v___x_3738_, 4, v___x_3721_);
lean_ctor_set(v___x_3738_, 5, v_sendIdx_3722_);
lean_ctor_set(v___x_3738_, 6, v___y_3723_);
lean_ctor_set_uint8(v___x_3738_, sizeof(void*)*7, v_closed_3724_);
v___x_3739_ = lean_box(0);
lean_inc(v_a_3726_);
v___x_3740_ = lean_apply_4(v___f_3725_, v___x_3739_, v___x_3738_, v_a_3726_, lean_box(0));
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3741_, lean_object* v_consumers_3742_, lean_object* v_capacity_3743_, lean_object* v_buf_3744_, lean_object* v___x_3745_, lean_object* v_sendIdx_3746_, lean_object* v___y_3747_, lean_object* v_closed_3748_, lean_object* v___f_3749_, lean_object* v_a_3750_, lean_object* v_x_3751_, lean_object* v___y_3752_){
_start:
{
uint8_t v_closed_boxed_3753_; lean_object* v_res_3754_; 
v_closed_boxed_3753_ = lean_unbox(v_closed_3748_);
v_res_3754_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3741_, v_consumers_3742_, v_capacity_3743_, v_buf_3744_, v___x_3745_, v_sendIdx_3746_, v___y_3747_, v_closed_boxed_3753_, v___f_3749_, v_a_3750_, v_x_3751_);
lean_dec(v_a_3750_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3755_, uint8_t v___x_3756_, lean_object* v_bufCount_3757_, lean_object* v_producers_3758_, lean_object* v_consumers_3759_, lean_object* v_capacity_3760_, lean_object* v_buf_3761_, lean_object* v_sendIdx_3762_, uint8_t v_closed_3763_, lean_object* v_a_3764_, uint8_t v___x_3765_, lean_object* v_recvIdx_3766_, lean_object* v_x_3767_){
_start:
{
if (lean_obj_tag(v_x_3767_) == 0)
{
lean_object* v___x_3769_; 
lean_dec(v_sendIdx_3762_);
lean_dec_ref(v_buf_3761_);
lean_dec(v_capacity_3760_);
lean_dec_ref(v_consumers_3759_);
lean_dec_ref(v_producers_3758_);
lean_dec(v___x_3755_);
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v_x_3767_);
return v___x_3769_;
}
else
{
lean_object* v___f_3770_; lean_object* v___x_3771_; lean_object* v___f_3772_; lean_object* v___y_3774_; lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___x_3799_; 
v___f_3770_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3770_, 0, v_x_3767_);
v___x_3771_ = lean_box(v___x_3756_);
lean_inc_ref(v___f_3770_);
lean_inc(v___x_3755_);
v___f_3772_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3772_, 0, v___x_3755_);
lean_closure_set(v___f_3772_, 1, v___x_3771_);
lean_closure_set(v___f_3772_, 2, v___f_3770_);
v___x_3797_ = lean_unsigned_to_nat(1u);
v___x_3798_ = lean_nat_add(v_recvIdx_3766_, v___x_3797_);
v___x_3799_ = lean_nat_dec_eq(v___x_3798_, v_capacity_3760_);
if (v___x_3799_ == 0)
{
v___y_3774_ = v___x_3798_;
goto v___jp_3773_;
}
else
{
lean_dec(v___x_3798_);
lean_inc(v___x_3755_);
v___y_3774_ = v___x_3755_;
goto v___jp_3773_;
}
v___jp_3773_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_nat_sub(v_bufCount_3757_, v___x_3775_);
lean_inc(v___y_3774_);
lean_inc(v_sendIdx_3762_);
lean_inc(v___x_3776_);
lean_inc_ref(v_buf_3761_);
lean_inc(v_capacity_3760_);
lean_inc_ref(v_consumers_3759_);
lean_inc_ref(v_producers_3758_);
v___x_3777_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3777_, 0, v_producers_3758_);
lean_ctor_set(v___x_3777_, 1, v_consumers_3759_);
lean_ctor_set(v___x_3777_, 2, v_capacity_3760_);
lean_ctor_set(v___x_3777_, 3, v_buf_3761_);
lean_ctor_set(v___x_3777_, 4, v___x_3776_);
lean_ctor_set(v___x_3777_, 5, v_sendIdx_3762_);
lean_ctor_set(v___x_3777_, 6, v___y_3774_);
lean_ctor_set_uint8(v___x_3777_, sizeof(void*)*7, v_closed_3763_);
v___x_3778_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3758_);
if (lean_obj_tag(v___x_3778_) == 1)
{
lean_object* v_val_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref_known(v___x_3777_, 7);
lean_dec_ref(v___f_3770_);
v_val_3779_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3781_ = v___x_3778_;
v_isShared_3782_ = v_isSharedCheck_3794_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_val_3779_);
lean_dec(v___x_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3794_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v_fst_3783_; lean_object* v_snd_3784_; lean_object* v___x_3785_; lean_object* v___f_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3790_; 
v_fst_3783_ = lean_ctor_get(v_val_3779_, 0);
lean_inc(v_fst_3783_);
v_snd_3784_ = lean_ctor_get(v_val_3779_, 1);
lean_inc(v_snd_3784_);
lean_dec(v_val_3779_);
v___x_3785_ = lean_box(v_closed_3763_);
lean_inc(v_a_3764_);
v___f_3786_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3786_, 0, v_snd_3784_);
lean_closure_set(v___f_3786_, 1, v_consumers_3759_);
lean_closure_set(v___f_3786_, 2, v_capacity_3760_);
lean_closure_set(v___f_3786_, 3, v_buf_3761_);
lean_closure_set(v___f_3786_, 4, v___x_3776_);
lean_closure_set(v___f_3786_, 5, v_sendIdx_3762_);
lean_closure_set(v___f_3786_, 6, v___y_3774_);
lean_closure_set(v___f_3786_, 7, v___x_3785_);
lean_closure_set(v___f_3786_, 8, v___f_3772_);
lean_closure_set(v___f_3786_, 9, v_a_3764_);
v___x_3787_ = lean_box(v___x_3765_);
v___x_3788_ = lean_io_promise_resolve(v___x_3787_, v_fst_3783_);
lean_dec(v_fst_3783_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v___x_3788_);
v___x_3790_ = v___x_3781_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
v___x_3792_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3755_, v___x_3756_, v___x_3791_, v___f_3786_);
return v___x_3792_;
}
}
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
lean_dec(v___x_3778_);
lean_dec(v___x_3776_);
lean_dec(v___y_3774_);
lean_dec_ref(v___f_3772_);
lean_dec(v_sendIdx_3762_);
lean_dec_ref(v_buf_3761_);
lean_dec(v_capacity_3760_);
lean_dec_ref(v_consumers_3759_);
v___x_3795_ = lean_box(0);
v___x_3796_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3755_, v___x_3756_, v___f_3770_, v___x_3795_, v___x_3777_, v_a_3764_);
return v___x_3796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3800_, lean_object* v___x_3801_, lean_object* v_bufCount_3802_, lean_object* v_producers_3803_, lean_object* v_consumers_3804_, lean_object* v_capacity_3805_, lean_object* v_buf_3806_, lean_object* v_sendIdx_3807_, lean_object* v_closed_3808_, lean_object* v_a_3809_, lean_object* v___x_3810_, lean_object* v_recvIdx_3811_, lean_object* v_x_3812_, lean_object* v___y_3813_){
_start:
{
uint8_t v___x_6435__boxed_3814_; uint8_t v_closed_boxed_3815_; uint8_t v___x_6436__boxed_3816_; lean_object* v_res_3817_; 
v___x_6435__boxed_3814_ = lean_unbox(v___x_3801_);
v_closed_boxed_3815_ = lean_unbox(v_closed_3808_);
v___x_6436__boxed_3816_ = lean_unbox(v___x_3810_);
v_res_3817_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3800_, v___x_6435__boxed_3814_, v_bufCount_3802_, v_producers_3803_, v_consumers_3804_, v_capacity_3805_, v_buf_3806_, v_sendIdx_3807_, v_closed_boxed_3815_, v_a_3809_, v___x_6436__boxed_3816_, v_recvIdx_3811_, v_x_3812_);
lean_dec(v_recvIdx_3811_);
lean_dec(v_a_3809_);
lean_dec(v_bufCount_3802_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3818_, lean_object* v_x_3819_){
_start:
{
if (lean_obj_tag(v_x_3819_) == 0)
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3829_; 
v_a_3821_ = lean_ctor_get(v_x_3819_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_x_3819_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3823_ = v_x_3819_;
v_isShared_3824_ = v_isSharedCheck_3829_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v_x_3819_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3829_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
return v___x_3827_;
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3858_; 
v_a_3830_ = lean_ctor_get(v_x_3819_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_x_3819_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3832_ = v_x_3819_;
v_isShared_3833_ = v_isSharedCheck_3858_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v_x_3819_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3858_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v_producers_3834_; lean_object* v_consumers_3835_; lean_object* v_capacity_3836_; lean_object* v_buf_3837_; lean_object* v_bufCount_3838_; lean_object* v_sendIdx_3839_; lean_object* v_recvIdx_3840_; uint8_t v_closed_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; 
v_producers_3834_ = lean_ctor_get(v_a_3830_, 0);
lean_inc_ref(v_producers_3834_);
v_consumers_3835_ = lean_ctor_get(v_a_3830_, 1);
lean_inc_ref(v_consumers_3835_);
v_capacity_3836_ = lean_ctor_get(v_a_3830_, 2);
lean_inc(v_capacity_3836_);
v_buf_3837_ = lean_ctor_get(v_a_3830_, 3);
lean_inc_ref(v_buf_3837_);
v_bufCount_3838_ = lean_ctor_get(v_a_3830_, 4);
lean_inc(v_bufCount_3838_);
v_sendIdx_3839_ = lean_ctor_get(v_a_3830_, 5);
lean_inc(v_sendIdx_3839_);
v_recvIdx_3840_ = lean_ctor_get(v_a_3830_, 6);
lean_inc(v_recvIdx_3840_);
v_closed_3841_ = lean_ctor_get_uint8(v_a_3830_, sizeof(void*)*7);
lean_dec(v_a_3830_);
v___x_3842_ = lean_unsigned_to_nat(0u);
v___x_3843_ = lean_nat_dec_eq(v_bufCount_3838_, v___x_3842_);
if (v___x_3843_ == 0)
{
uint8_t v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___f_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3853_; 
v___x_3844_ = 1;
v___x_3845_ = lean_box(v___x_3843_);
v___x_3846_ = lean_box(v_closed_3841_);
v___x_3847_ = lean_box(v___x_3844_);
lean_inc(v_recvIdx_3840_);
lean_inc(v_a_3818_);
lean_inc_ref(v_buf_3837_);
v___f_3848_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_3848_, 0, v___x_3842_);
lean_closure_set(v___f_3848_, 1, v___x_3845_);
lean_closure_set(v___f_3848_, 2, v_bufCount_3838_);
lean_closure_set(v___f_3848_, 3, v_producers_3834_);
lean_closure_set(v___f_3848_, 4, v_consumers_3835_);
lean_closure_set(v___f_3848_, 5, v_capacity_3836_);
lean_closure_set(v___f_3848_, 6, v_buf_3837_);
lean_closure_set(v___f_3848_, 7, v_sendIdx_3839_);
lean_closure_set(v___f_3848_, 8, v___x_3846_);
lean_closure_set(v___f_3848_, 9, v_a_3818_);
lean_closure_set(v___f_3848_, 10, v___x_3847_);
lean_closure_set(v___f_3848_, 11, v_recvIdx_3840_);
v___x_3849_ = lean_array_fget(v_buf_3837_, v_recvIdx_3840_);
lean_dec(v_recvIdx_3840_);
lean_dec_ref(v_buf_3837_);
v___x_3850_ = lean_box(0);
v___x_3851_ = lean_st_ref_swap(v___x_3849_, v___x_3850_);
lean_dec(v___x_3849_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v___x_3851_);
v___x_3853_ = v___x_3832_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
v___x_3855_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3842_, v___x_3843_, v___x_3854_, v___f_3848_);
return v___x_3855_;
}
}
else
{
lean_object* v___x_3857_; 
lean_dec(v_recvIdx_3840_);
lean_dec(v_sendIdx_3839_);
lean_dec(v_bufCount_3838_);
lean_dec_ref(v_buf_3837_);
lean_dec(v_capacity_3836_);
lean_dec_ref(v_consumers_3835_);
lean_dec_ref(v_producers_3834_);
lean_del_object(v___x_3832_);
v___x_3857_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_3857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_3859_, lean_object* v_x_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3859_, v_x_3860_);
lean_dec(v_a_3859_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_3863_){
_start:
{
lean_object* v___f_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
lean_inc(v_a_3863_);
v___f_3865_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3865_, 0, v_a_3863_);
v___x_3866_ = lean_unsigned_to_nat(0u);
v___x_3867_ = 0;
v___x_3868_ = lean_st_ref_get(v_a_3863_);
v___x_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
v___x_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
v___x_3871_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3866_, v___x_3867_, v___x_3870_, v___f_3865_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3872_);
lean_dec(v_a_3872_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3876_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_3879_, lean_object* v_a_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_3879_, v_a_3880_);
lean_dec(v_a_3880_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_3883_, lean_object* v_x_3884_){
_start:
{
lean_object* v_val_3887_; lean_object* v___x_3889_; 
v___x_3889_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3883_, v_x_3884_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3889_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3889_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
lean_ctor_set_tag(v___x_3892_, 1);
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
v_val_3887_ = v___x_3895_;
goto v___jp_3886_;
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
v_a_3898_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3889_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3889_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set_tag(v___x_3900_, 0);
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
v_val_3887_ = v___x_3903_;
goto v___jp_3886_;
}
}
}
v___jp_3886_:
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v_val_3887_);
return v___x_3888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_3906_, lean_object* v_x_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_3906_, v_x_3907_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v___y_3910_, lean_object* v___f_3911_, lean_object* v_x_3912_){
_start:
{
if (lean_obj_tag(v_x_3912_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v___f_3911_);
v_a_3914_ = lean_ctor_get(v_x_3912_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_x_3912_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3916_ = v_x_3912_;
v_isShared_3917_ = v_isSharedCheck_3922_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v_x_3912_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3922_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3920_; 
v___x_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
return v___x_3920_;
}
}
}
else
{
lean_object* v_a_3923_; uint8_t v___x_3924_; 
v_a_3923_ = lean_ctor_get(v_x_3912_, 0);
lean_inc(v_a_3923_);
lean_dec_ref_known(v_x_3912_, 1);
v___x_3924_ = lean_unbox(v_a_3923_);
lean_dec(v_a_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; 
lean_dec_ref(v___f_3911_);
v___x_3925_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_3925_;
}
else
{
lean_object* v___x_3926_; uint8_t v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3926_ = lean_unsigned_to_nat(0u);
v___x_3927_ = 0;
v___x_3928_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_3910_);
v___x_3929_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3926_, v___x_3927_, v___x_3928_, v___f_3911_);
return v___x_3929_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v___y_3930_, lean_object* v___f_3931_, lean_object* v_x_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v___y_3930_, v___f_3931_, v_x_3932_);
lean_dec(v___y_3930_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___x_3935_, lean_object* v_x_3936_){
_start:
{
uint8_t v___y_3939_; 
if (lean_obj_tag(v_x_3936_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3951_; 
v_a_3943_ = lean_ctor_get(v_x_3936_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v_x_3936_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3945_ = v_x_3936_;
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v_x_3936_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
return v___x_3949_;
}
}
}
else
{
lean_object* v_a_3952_; lean_object* v_bufCount_3953_; uint8_t v_closed_3954_; uint8_t v___x_3955_; 
v_a_3952_ = lean_ctor_get(v_x_3936_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v_x_3936_, 1);
v_bufCount_3953_ = lean_ctor_get(v_a_3952_, 4);
lean_inc(v_bufCount_3953_);
v_closed_3954_ = lean_ctor_get_uint8(v_a_3952_, sizeof(void*)*7);
lean_dec(v_a_3952_);
v___x_3955_ = lean_nat_dec_eq(v_bufCount_3953_, v___x_3935_);
lean_dec(v_bufCount_3953_);
if (v___x_3955_ == 0)
{
uint8_t v___x_3956_; 
v___x_3956_ = 1;
v___y_3939_ = v___x_3956_;
goto v___jp_3938_;
}
else
{
v___y_3939_ = v_closed_3954_;
goto v___jp_3938_;
}
}
v___jp_3938_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3940_ = lean_box(v___y_3939_);
v___x_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
v___x_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
return v___x_3942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_3957_, lean_object* v_x_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___x_3957_, v_x_3958_);
lean_dec(v___x_3957_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v___f_3966_; lean_object* v___x_3967_; lean_object* v___f_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_inc(v___y_3964_);
v___f_3966_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3966_, 0, v___y_3964_);
lean_closure_set(v___f_3966_, 1, v___f_3963_);
v___x_3967_ = lean_unsigned_to_nat(0u);
v___f_3968_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___closed__0));
v___x_3969_ = 0;
v___x_3970_ = lean_st_ref_get(v___y_3964_);
v___x_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
v___x_3973_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3967_, v___x_3969_, v___x_3972_, v___f_3968_);
v___x_3974_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3967_, v___x_3969_, v___x_3973_, v___f_3966_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_3975_, v___y_3976_);
lean_dec(v___y_3976_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_3979_, lean_object* v_capacity_3980_, lean_object* v_buf_3981_, lean_object* v_bufCount_3982_, lean_object* v_sendIdx_3983_, lean_object* v_recvIdx_3984_, uint8_t v_closed_3985_, lean_object* v___y_3986_, lean_object* v_x_3987_){
_start:
{
if (lean_obj_tag(v_x_3987_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v_recvIdx_3984_);
lean_dec(v_sendIdx_3983_);
lean_dec(v_bufCount_3982_);
lean_dec_ref(v_buf_3981_);
lean_dec(v_capacity_3980_);
lean_dec_ref(v_producers_3979_);
v_a_3989_ = lean_ctor_get(v_x_3987_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v_x_3987_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3991_ = v_x_3987_;
v_isShared_3992_ = v_isSharedCheck_3997_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v_x_3987_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3997_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
return v___x_3995_;
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v_a_3998_ = lean_ctor_get(v_x_3987_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v_x_3987_, 1);
v___x_3999_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3999_, 0, v_producers_3979_);
lean_ctor_set(v___x_3999_, 1, v_a_3998_);
lean_ctor_set(v___x_3999_, 2, v_capacity_3980_);
lean_ctor_set(v___x_3999_, 3, v_buf_3981_);
lean_ctor_set(v___x_3999_, 4, v_bufCount_3982_);
lean_ctor_set(v___x_3999_, 5, v_sendIdx_3983_);
lean_ctor_set(v___x_3999_, 6, v_recvIdx_3984_);
lean_ctor_set_uint8(v___x_3999_, sizeof(void*)*7, v_closed_3985_);
v___x_4000_ = lean_st_ref_swap(v___y_3986_, v___x_3999_);
lean_dec(v___x_4000_);
v___x_4001_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_4002_, lean_object* v_capacity_4003_, lean_object* v_buf_4004_, lean_object* v_bufCount_4005_, lean_object* v_sendIdx_4006_, lean_object* v_recvIdx_4007_, lean_object* v_closed_4008_, lean_object* v___y_4009_, lean_object* v_x_4010_, lean_object* v___y_4011_){
_start:
{
uint8_t v_closed_boxed_4012_; lean_object* v_res_4013_; 
v_closed_boxed_4012_ = lean_unbox(v_closed_4008_);
v_res_4013_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_4002_, v_capacity_4003_, v_buf_4004_, v_bufCount_4005_, v_sendIdx_4006_, v_recvIdx_4007_, v_closed_boxed_4012_, v___y_4009_, v_x_4010_);
lean_dec(v___y_4009_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_4014_, lean_object* v_x_4015_, lean_object* v_head_4016_, lean_object* v_x_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_4014_, v_x_4015_, v_head_4016_, v_x_4017_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_4020_, lean_object* v_x_4021_){
_start:
{
if (lean_obj_tag(v_x_4020_) == 0)
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4023_, 0, v_x_4021_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
return v___x_4024_;
}
else
{
lean_object* v_head_4025_; lean_object* v_tail_4026_; lean_object* v_waiter_4027_; lean_object* v___f_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; 
v_head_4025_ = lean_ctor_get(v_x_4020_, 0);
lean_inc(v_head_4025_);
v_tail_4026_ = lean_ctor_get(v_x_4020_, 1);
lean_inc(v_tail_4026_);
lean_dec_ref_known(v_x_4020_, 2);
v_waiter_4027_ = lean_ctor_get(v_head_4025_, 1);
lean_inc(v_waiter_4027_);
v___f_4028_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4028_, 0, v_tail_4026_);
lean_closure_set(v___f_4028_, 1, v_x_4021_);
lean_closure_set(v___f_4028_, 2, v_head_4025_);
v___x_4029_ = lean_unsigned_to_nat(0u);
v___x_4030_ = 0;
if (lean_obj_tag(v_waiter_4027_) == 0)
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_4032_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4029_, v___x_4030_, v___x_4031_, v___f_4028_);
return v___x_4032_;
}
else
{
lean_object* v_val_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4046_; 
v_val_4033_ = lean_ctor_get(v_waiter_4027_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_waiter_4027_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4035_ = v_waiter_4027_;
v_isShared_4036_ = v_isSharedCheck_4046_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_val_4033_);
lean_dec(v_waiter_4027_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4046_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v_finished_4037_; lean_object* v___f_4038_; lean_object* v___x_4039_; lean_object* v___x_4041_; 
v_finished_4037_ = lean_ctor_get(v_val_4033_, 0);
lean_inc(v_finished_4037_);
lean_dec(v_val_4033_);
v___f_4038_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_4039_ = lean_st_ref_get(v_finished_4037_);
lean_dec(v_finished_4037_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4039_);
v___x_4041_ = v___x_4035_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4039_);
v___x_4041_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
v___x_4043_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4029_, v___x_4030_, v___x_4042_, v___f_4038_);
v___x_4044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4029_, v___x_4030_, v___x_4043_, v___f_4028_);
return v___x_4044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_4047_, lean_object* v_x_4048_, lean_object* v_head_4049_, lean_object* v_x_4050_){
_start:
{
if (lean_obj_tag(v_x_4050_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref(v_head_4049_);
lean_dec(v_x_4048_);
lean_dec(v_tail_4047_);
v_a_4052_ = lean_ctor_get(v_x_4050_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_x_4050_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4054_ = v_x_4050_;
v_isShared_4055_ = v_isSharedCheck_4060_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v_x_4050_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4060_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4058_; 
v___x_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
return v___x_4058_;
}
}
}
else
{
lean_object* v_a_4061_; uint8_t v___x_4062_; 
v_a_4061_ = lean_ctor_get(v_x_4050_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v_x_4050_, 1);
v___x_4062_ = lean_unbox(v_a_4061_);
lean_dec(v_a_4061_);
if (v___x_4062_ == 0)
{
lean_object* v___x_4063_; 
lean_dec_ref(v_head_4049_);
v___x_4063_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4047_, v_x_4048_);
return v___x_4063_;
}
else
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4064_, 0, v_head_4049_);
lean_ctor_set(v___x_4064_, 1, v_x_4048_);
v___x_4065_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4047_, v___x_4064_);
return v___x_4065_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_4066_, lean_object* v_x_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4066_, v_x_4067_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_4070_){
_start:
{
if (lean_obj_tag(v_x_4070_) == 0)
{
lean_object* v___x_4072_; 
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v_x_4070_);
return v___x_4072_;
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4082_; 
v_a_4073_ = lean_ctor_get(v_x_4070_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v_x_4070_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4075_ = v_x_4070_;
v_isShared_4076_ = v_isSharedCheck_4082_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v_x_4070_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4082_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4077_ = l_List_reverse___redArg(v_a_4073_);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v___x_4077_);
v___x_4079_ = v___x_4075_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
return v___x_4080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4083_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4086_, lean_object* v___x_4087_, lean_object* v_x_4088_){
_start:
{
if (lean_obj_tag(v_x_4088_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4098_; 
lean_dec(v___x_4087_);
lean_dec(v_a_4086_);
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
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4115_; 
v_a_4099_ = lean_ctor_get(v_x_4088_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v_x_4088_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4101_ = v_x_4088_;
v_isShared_4102_ = v_isSharedCheck_4115_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v_x_4088_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4115_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
uint8_t v___x_4103_; 
v___x_4103_ = l_List_isEmpty___redArg(v_a_4086_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4106_; 
lean_dec(v___x_4087_);
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v_a_4099_);
lean_ctor_set(v___x_4104_, 1, v_a_4086_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4104_);
v___x_4106_ = v___x_4101_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4104_);
v___x_4106_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; 
v___x_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
return v___x_4107_;
}
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; 
lean_dec(v_a_4086_);
v___x_4109_ = l_List_reverse___redArg(v_a_4099_);
v___x_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4087_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4110_);
v___x_4112_ = v___x_4101_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4110_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4116_, lean_object* v___x_4117_, lean_object* v_x_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4116_, v___x_4117_, v_x_4118_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v___x_4121_, lean_object* v_eList_4122_, lean_object* v___f_4123_, lean_object* v_x_4124_){
_start:
{
if (lean_obj_tag(v_x_4124_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4134_; 
lean_dec_ref(v___f_4123_);
lean_dec(v_eList_4122_);
lean_dec(v___x_4121_);
v_a_4126_ = lean_ctor_get(v_x_4124_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_x_4124_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4128_ = v_x_4124_;
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v_x_4124_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; 
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___f_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_a_4135_ = lean_ctor_get(v_x_4124_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v_x_4124_, 1);
lean_inc(v___x_4121_);
v___f_4136_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4136_, 0, v_a_4135_);
lean_closure_set(v___f_4136_, 1, v___x_4121_);
v___x_4137_ = lean_unsigned_to_nat(0u);
v___x_4138_ = 0;
v___x_4139_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4122_, v___x_4121_);
v___x_4140_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4137_, v___x_4138_, v___x_4139_, v___f_4123_);
v___x_4141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4137_, v___x_4138_, v___x_4140_, v___f_4136_);
return v___x_4141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v___x_4142_, lean_object* v_eList_4143_, lean_object* v___f_4144_, lean_object* v_x_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v___x_4142_, v_eList_4143_, v___f_4144_, v_x_4145_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v_eList_4152_; lean_object* v_dList_4153_; lean_object* v___f_4154_; lean_object* v___x_4155_; lean_object* v___f_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v_eList_4152_ = lean_ctor_get(v_q_4149_, 0);
lean_inc(v_eList_4152_);
v_dList_4153_ = lean_ctor_get(v_q_4149_, 1);
lean_inc(v_dList_4153_);
lean_dec_ref(v_q_4149_);
v___f_4154_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4155_ = lean_box(0);
v___f_4156_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4156_, 0, v___x_4155_);
lean_closure_set(v___f_4156_, 1, v_eList_4152_);
lean_closure_set(v___f_4156_, 2, v___f_4154_);
v___x_4157_ = lean_unsigned_to_nat(0u);
v___x_4158_ = 0;
v___x_4159_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4153_, v___x_4155_);
v___x_4160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4157_, v___x_4158_, v___x_4159_, v___f_4154_);
v___x_4161_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4157_, v___x_4158_, v___x_4160_, v___f_4156_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4162_, v___y_4163_);
lean_dec(v___y_4163_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4166_, lean_object* v_x_4167_){
_start:
{
if (lean_obj_tag(v_x_4167_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4177_; 
v_a_4169_ = lean_ctor_get(v_x_4167_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v_x_4167_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4171_ = v_x_4167_;
v_isShared_4172_ = v_isSharedCheck_4177_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v_x_4167_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4177_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_object* v___x_4175_; 
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
return v___x_4175_;
}
}
}
else
{
lean_object* v_a_4178_; lean_object* v_producers_4179_; lean_object* v_consumers_4180_; lean_object* v_capacity_4181_; lean_object* v_buf_4182_; lean_object* v_bufCount_4183_; lean_object* v_sendIdx_4184_; lean_object* v_recvIdx_4185_; uint8_t v_closed_4186_; lean_object* v___x_4187_; lean_object* v___f_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v_a_4178_ = lean_ctor_get(v_x_4167_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v_x_4167_, 1);
v_producers_4179_ = lean_ctor_get(v_a_4178_, 0);
lean_inc_ref(v_producers_4179_);
v_consumers_4180_ = lean_ctor_get(v_a_4178_, 1);
lean_inc_ref(v_consumers_4180_);
v_capacity_4181_ = lean_ctor_get(v_a_4178_, 2);
lean_inc(v_capacity_4181_);
v_buf_4182_ = lean_ctor_get(v_a_4178_, 3);
lean_inc_ref(v_buf_4182_);
v_bufCount_4183_ = lean_ctor_get(v_a_4178_, 4);
lean_inc(v_bufCount_4183_);
v_sendIdx_4184_ = lean_ctor_get(v_a_4178_, 5);
lean_inc(v_sendIdx_4184_);
v_recvIdx_4185_ = lean_ctor_get(v_a_4178_, 6);
lean_inc(v_recvIdx_4185_);
v_closed_4186_ = lean_ctor_get_uint8(v_a_4178_, sizeof(void*)*7);
lean_dec(v_a_4178_);
v___x_4187_ = lean_box(v_closed_4186_);
lean_inc(v___y_4166_);
v___f_4188_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4188_, 0, v_producers_4179_);
lean_closure_set(v___f_4188_, 1, v_capacity_4181_);
lean_closure_set(v___f_4188_, 2, v_buf_4182_);
lean_closure_set(v___f_4188_, 3, v_bufCount_4183_);
lean_closure_set(v___f_4188_, 4, v_sendIdx_4184_);
lean_closure_set(v___f_4188_, 5, v_recvIdx_4185_);
lean_closure_set(v___f_4188_, 6, v___x_4187_);
lean_closure_set(v___f_4188_, 7, v___y_4166_);
v___x_4189_ = lean_unsigned_to_nat(0u);
v___x_4190_ = 0;
v___x_4191_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4180_, v___y_4166_);
v___x_4192_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4189_, v___x_4190_, v___x_4191_, v___f_4188_);
return v___x_4192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4193_, lean_object* v_x_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4193_, v_x_4194_);
lean_dec(v___y_4193_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4197_){
_start:
{
lean_object* v___f_4199_; lean_object* v___x_4200_; uint8_t v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_inc(v___y_4197_);
v___f_4199_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4199_, 0, v___y_4197_);
v___x_4200_ = lean_unsigned_to_nat(0u);
v___x_4201_ = 0;
v___x_4202_ = lean_st_ref_get(v___y_4197_);
v___x_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
v___x_4205_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4200_, v___x_4201_, v___x_4204_, v___f_4199_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4206_);
lean_dec(v___y_4206_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4212_){
_start:
{
lean_object* v___f_4213_; lean_object* v___f_4214_; lean_object* v___f_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
lean_inc_ref_n(v_ch_4212_, 2);
v___f_4213_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4213_, 0, v_ch_4212_);
v___f_4214_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0));
v___f_4215_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___x_4216_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4216_, 0, lean_box(0));
lean_closure_set(v___x_4216_, 1, lean_box(0));
lean_closure_set(v___x_4216_, 2, v_ch_4212_);
lean_closure_set(v___x_4216_, 3, v___f_4214_);
v___x_4217_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4217_, 0, lean_box(0));
lean_closure_set(v___x_4217_, 1, lean_box(0));
lean_closure_set(v___x_4217_, 2, v_ch_4212_);
lean_closure_set(v___x_4217_, 3, v___f_4215_);
v___x_4218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4216_);
lean_ctor_set(v___x_4218_, 1, v___f_4213_);
lean_ctor_set(v___x_4218_, 2, v___x_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4219_, lean_object* v_ch_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4222_, lean_object* v_q_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4223_, v___y_4224_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4227_, lean_object* v_q_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4227_, v_q_4228_, v___y_4229_);
lean_dec(v___y_4229_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4232_, lean_object* v_x_4233_, lean_object* v_x_4234_, lean_object* v___y_4235_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4233_, v_x_4234_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4238_, lean_object* v_x_4239_, lean_object* v_x_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4238_, v_x_4239_, v_x_4240_, v___y_4241_);
lean_dec(v___y_4241_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl___redArg(lean_object* v_x_4244_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_obj_tag_nat(v_x_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl___redArg___boxed(lean_object* v_x_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Std_CloseableChannel_Flavors_ctorIdx___impl___redArg(v_x_4246_);
lean_dec_ref(v_x_4246_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl(lean_object* v_00_u03b1_4248_, lean_object* v_x_4249_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_obj_tag_nat(v_x_4249_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl___boxed(lean_object* v_00_u03b1_4251_, lean_object* v_x_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Std_CloseableChannel_Flavors_ctorIdx___impl(v_00_u03b1_4251_, v_x_4252_);
lean_dec_ref(v_x_4252_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4254_, lean_object* v_k_4255_){
_start:
{
lean_object* v_ch_4256_; lean_object* v___x_4257_; 
v_ch_4256_ = lean_ctor_get(v_t_4254_, 0);
lean_inc_ref(v_ch_4256_);
lean_dec_ref(v_t_4254_);
v___x_4257_ = lean_apply_1(v_k_4255_, v_ch_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4258_, lean_object* v_motive_4259_, lean_object* v_ctorIdx_4260_, lean_object* v_t_4261_, lean_object* v_h_4262_, lean_object* v_k_4263_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4261_, v_k_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4265_, lean_object* v_motive_4266_, lean_object* v_ctorIdx_4267_, lean_object* v_t_4268_, lean_object* v_h_4269_, lean_object* v_k_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4265_, v_motive_4266_, v_ctorIdx_4267_, v_t_4268_, v_h_4269_, v_k_4270_);
lean_dec(v_ctorIdx_4267_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4272_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4273_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4272_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4275_, lean_object* v_motive_4276_, lean_object* v_t_4277_, lean_object* v_h_4278_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4279_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4277_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4281_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4282_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4281_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4284_, lean_object* v_motive_4285_, lean_object* v_t_4286_, lean_object* v_h_4287_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4286_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4290_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4290_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4293_, lean_object* v_motive_4294_, lean_object* v_t_4295_, lean_object* v_h_4296_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4297_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4295_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4299_){
_start:
{
if (lean_obj_tag(v_capacity_4299_) == 0)
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
return v___x_4302_;
}
else
{
lean_object* v_val_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4320_; 
v_val_4303_ = lean_ctor_get(v_capacity_4299_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_capacity_4299_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4305_ = v_capacity_4299_;
v_isShared_4306_ = v_isSharedCheck_4320_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_val_4303_);
lean_dec(v_capacity_4299_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4320_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v_zero_4307_; uint8_t v_isZero_4308_; 
v_zero_4307_ = lean_unsigned_to_nat(0u);
v_isZero_4308_ = lean_nat_dec_eq(v_val_4303_, v_zero_4307_);
if (v_isZero_4308_ == 1)
{
lean_object* v___x_4309_; lean_object* v___x_4311_; 
lean_dec(v_val_4303_);
v___x_4309_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v___x_4309_);
v___x_4311_ = v___x_4305_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
else
{
lean_object* v_one_4313_; lean_object* v_n_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
v_one_4313_ = lean_unsigned_to_nat(1u);
v_n_4314_ = lean_nat_sub(v_val_4303_, v_one_4313_);
lean_dec(v_val_4303_);
v___x_4315_ = lean_nat_add(v_n_4314_, v_one_4313_);
lean_dec(v_n_4314_);
v___x_4316_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4315_);
if (v_isShared_4306_ == 0)
{
lean_ctor_set_tag(v___x_4305_, 2);
lean_ctor_set(v___x_4305_, 0, v___x_4316_);
v___x_4318_ = v___x_4305_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_Std_CloseableChannel_new___redArg(v_capacity_4321_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4324_, lean_object* v_capacity_4325_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Std_CloseableChannel_new___redArg(v_capacity_4325_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4328_, lean_object* v_capacity_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_Std_CloseableChannel_new(v_00_u03b1_4328_, v_capacity_4329_);
return v_res_4331_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4332_, lean_object* v_v_4333_){
_start:
{
switch(lean_obj_tag(v_ch_4332_))
{
case 0:
{
lean_object* v_ch_4335_; uint8_t v___x_4336_; 
v_ch_4335_ = lean_ctor_get(v_ch_4332_, 0);
lean_inc_ref(v_ch_4335_);
lean_dec_ref_known(v_ch_4332_, 1);
v___x_4336_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4335_, v_v_4333_);
return v___x_4336_;
}
case 1:
{
lean_object* v_ch_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v_ch_4337_ = lean_ctor_get(v_ch_4332_, 0);
lean_inc_ref(v_ch_4337_);
lean_dec_ref_known(v_ch_4332_, 1);
v___x_4338_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4337_, v_v_4333_);
v___x_4339_ = lean_unbox(v___x_4338_);
lean_dec(v___x_4338_);
return v___x_4339_;
}
default: 
{
lean_object* v_ch_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v_ch_4340_ = lean_ctor_get(v_ch_4332_, 0);
lean_inc_ref(v_ch_4340_);
lean_dec_ref_known(v_ch_4332_, 1);
v___x_4341_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4340_, v_v_4333_);
v___x_4342_ = lean_unbox(v___x_4341_);
lean_dec(v___x_4341_);
return v___x_4342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4343_, lean_object* v_v_4344_, lean_object* v_a_4345_){
_start:
{
uint8_t v_res_4346_; lean_object* v_r_4347_; 
v_res_4346_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4343_, v_v_4344_);
v_r_4347_ = lean_box(v_res_4346_);
return v_r_4347_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4348_, lean_object* v_ch_4349_, lean_object* v_v_4350_){
_start:
{
uint8_t v___x_4352_; 
v___x_4352_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4349_, v_v_4350_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4353_, lean_object* v_ch_4354_, lean_object* v_v_4355_, lean_object* v_a_4356_){
_start:
{
uint8_t v_res_4357_; lean_object* v_r_4358_; 
v_res_4357_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4353_, v_ch_4354_, v_v_4355_);
v_r_4358_ = lean_box(v_res_4357_);
return v_r_4358_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4359_, lean_object* v_v_4360_){
_start:
{
switch(lean_obj_tag(v_ch_4359_))
{
case 0:
{
lean_object* v_ch_4362_; lean_object* v___x_4363_; 
v_ch_4362_ = lean_ctor_get(v_ch_4359_, 0);
lean_inc_ref(v_ch_4362_);
lean_dec_ref_known(v_ch_4359_, 1);
v___x_4363_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4362_, v_v_4360_);
return v___x_4363_;
}
case 1:
{
lean_object* v_ch_4364_; lean_object* v___x_4365_; 
v_ch_4364_ = lean_ctor_get(v_ch_4359_, 0);
lean_inc_ref(v_ch_4364_);
lean_dec_ref_known(v_ch_4359_, 1);
v___x_4365_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4364_, v_v_4360_);
return v___x_4365_;
}
default: 
{
lean_object* v_ch_4366_; lean_object* v___x_4367_; 
v_ch_4366_ = lean_ctor_get(v_ch_4359_, 0);
lean_inc_ref(v_ch_4366_);
lean_dec_ref_known(v_ch_4359_, 1);
v___x_4367_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4366_, v_v_4360_);
return v___x_4367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4368_, lean_object* v_v_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Std_CloseableChannel_send___redArg(v_ch_4368_, v_v_4369_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4372_, lean_object* v_ch_4373_, lean_object* v_v_4374_){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = l_Std_CloseableChannel_send___redArg(v_ch_4373_, v_v_4374_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4377_, lean_object* v_ch_4378_, lean_object* v_v_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Std_CloseableChannel_send(v_00_u03b1_4377_, v_ch_4378_, v_v_4379_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4382_){
_start:
{
switch(lean_obj_tag(v_ch_4382_))
{
case 0:
{
lean_object* v_ch_4384_; lean_object* v___x_4385_; 
v_ch_4384_ = lean_ctor_get(v_ch_4382_, 0);
lean_inc_ref(v_ch_4384_);
lean_dec_ref_known(v_ch_4382_, 1);
v___x_4385_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4384_);
return v___x_4385_;
}
case 1:
{
lean_object* v_ch_4386_; lean_object* v___x_4387_; 
v_ch_4386_ = lean_ctor_get(v_ch_4382_, 0);
lean_inc_ref(v_ch_4386_);
lean_dec_ref_known(v_ch_4382_, 1);
v___x_4387_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4386_);
return v___x_4387_;
}
default: 
{
lean_object* v_ch_4388_; lean_object* v___x_4389_; 
v_ch_4388_ = lean_ctor_get(v_ch_4382_, 0);
lean_inc_ref(v_ch_4388_);
lean_dec_ref_known(v_ch_4382_, 1);
v___x_4389_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4388_);
return v___x_4389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Std_CloseableChannel_close___redArg(v_ch_4390_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4393_, lean_object* v_ch_4394_){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = l_Std_CloseableChannel_close___redArg(v_ch_4394_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4397_, lean_object* v_ch_4398_, lean_object* v_a_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_Std_CloseableChannel_close(v_00_u03b1_4397_, v_ch_4398_);
return v_res_4400_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4401_){
_start:
{
switch(lean_obj_tag(v_ch_4401_))
{
case 0:
{
lean_object* v_ch_4403_; lean_object* v___x_4404_; uint8_t v___x_4405_; 
v_ch_4403_ = lean_ctor_get(v_ch_4401_, 0);
lean_inc_ref(v_ch_4403_);
lean_dec_ref_known(v_ch_4401_, 1);
v___x_4404_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4403_);
v___x_4405_ = lean_unbox(v___x_4404_);
lean_dec(v___x_4404_);
return v___x_4405_;
}
case 1:
{
lean_object* v_ch_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v_ch_4406_ = lean_ctor_get(v_ch_4401_, 0);
lean_inc_ref(v_ch_4406_);
lean_dec_ref_known(v_ch_4401_, 1);
v___x_4407_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4406_);
v___x_4408_ = lean_unbox(v___x_4407_);
lean_dec(v___x_4407_);
return v___x_4408_;
}
default: 
{
lean_object* v_ch_4409_; lean_object* v___x_4410_; uint8_t v___x_4411_; 
v_ch_4409_ = lean_ctor_get(v_ch_4401_, 0);
lean_inc_ref(v_ch_4409_);
lean_dec_ref_known(v_ch_4401_, 1);
v___x_4410_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4409_);
v___x_4411_ = lean_unbox(v___x_4410_);
lean_dec(v___x_4410_);
return v___x_4411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4412_, lean_object* v_a_4413_){
_start:
{
uint8_t v_res_4414_; lean_object* v_r_4415_; 
v_res_4414_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4412_);
v_r_4415_ = lean_box(v_res_4414_);
return v_r_4415_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4416_, lean_object* v_ch_4417_){
_start:
{
uint8_t v___x_4419_; 
v___x_4419_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4417_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4420_, lean_object* v_ch_4421_, lean_object* v_a_4422_){
_start:
{
uint8_t v_res_4423_; lean_object* v_r_4424_; 
v_res_4423_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4420_, v_ch_4421_);
v_r_4424_ = lean_box(v_res_4423_);
return v_r_4424_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4425_){
_start:
{
switch(lean_obj_tag(v_ch_4425_))
{
case 0:
{
lean_object* v_ch_4427_; lean_object* v___x_4428_; 
v_ch_4427_ = lean_ctor_get(v_ch_4425_, 0);
lean_inc_ref(v_ch_4427_);
lean_dec_ref_known(v_ch_4425_, 1);
v___x_4428_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4427_);
return v___x_4428_;
}
case 1:
{
lean_object* v_ch_4429_; lean_object* v___x_4430_; 
v_ch_4429_ = lean_ctor_get(v_ch_4425_, 0);
lean_inc_ref(v_ch_4429_);
lean_dec_ref_known(v_ch_4425_, 1);
v___x_4430_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4429_);
return v___x_4430_;
}
default: 
{
lean_object* v_ch_4431_; lean_object* v___x_4432_; 
v_ch_4431_ = lean_ctor_get(v_ch_4425_, 0);
lean_inc_ref(v_ch_4431_);
lean_dec_ref_known(v_ch_4425_, 1);
v___x_4432_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4431_);
return v___x_4432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4433_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4436_, lean_object* v_ch_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4437_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4440_, lean_object* v_ch_4441_, lean_object* v_a_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4440_, v_ch_4441_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4444_){
_start:
{
switch(lean_obj_tag(v_ch_4444_))
{
case 0:
{
lean_object* v_ch_4446_; lean_object* v___x_4447_; 
v_ch_4446_ = lean_ctor_get(v_ch_4444_, 0);
lean_inc_ref(v_ch_4446_);
lean_dec_ref_known(v_ch_4444_, 1);
v___x_4447_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4446_);
return v___x_4447_;
}
case 1:
{
lean_object* v_ch_4448_; lean_object* v___x_4449_; 
v_ch_4448_ = lean_ctor_get(v_ch_4444_, 0);
lean_inc_ref(v_ch_4448_);
lean_dec_ref_known(v_ch_4444_, 1);
v___x_4449_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4448_);
return v___x_4449_;
}
default: 
{
lean_object* v_ch_4450_; lean_object* v___x_4451_; 
v_ch_4450_ = lean_ctor_get(v_ch_4444_, 0);
lean_inc_ref(v_ch_4450_);
lean_dec_ref_known(v_ch_4444_, 1);
v___x_4451_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4450_);
return v___x_4451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Std_CloseableChannel_recv___redArg(v_ch_4452_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4455_, lean_object* v_ch_4456_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_Std_CloseableChannel_recv___redArg(v_ch_4456_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4459_, lean_object* v_ch_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Std_CloseableChannel_recv(v_00_u03b1_4459_, v_ch_4460_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4463_){
_start:
{
switch(lean_obj_tag(v_ch_4463_))
{
case 0:
{
lean_object* v_ch_4464_; lean_object* v___x_4465_; 
v_ch_4464_ = lean_ctor_get(v_ch_4463_, 0);
lean_inc_ref(v_ch_4464_);
lean_dec_ref_known(v_ch_4463_, 1);
v___x_4465_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4464_);
return v___x_4465_;
}
case 1:
{
lean_object* v_ch_4466_; lean_object* v___x_4467_; 
v_ch_4466_ = lean_ctor_get(v_ch_4463_, 0);
lean_inc_ref(v_ch_4466_);
lean_dec_ref_known(v_ch_4463_, 1);
v___x_4467_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4466_);
return v___x_4467_;
}
default: 
{
lean_object* v_ch_4468_; lean_object* v___x_4469_; 
v_ch_4468_ = lean_ctor_get(v_ch_4463_, 0);
lean_inc_ref(v_ch_4468_);
lean_dec_ref_known(v_ch_4463_, 1);
v___x_4469_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4468_);
return v___x_4469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4470_, lean_object* v_ch_4471_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4471_);
return v___x_4472_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4473_ = lean_box(0);
v___x_4474_ = lean_task_pure(v___x_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4475_, lean_object* v_ch_4476_, lean_object* v_prio_4477_, lean_object* v_x_4478_){
_start:
{
if (lean_obj_tag(v_x_4478_) == 0)
{
lean_object* v___x_4480_; 
lean_dec(v_prio_4477_);
lean_dec_ref(v_ch_4476_);
lean_dec_ref(v_f_4475_);
v___x_4480_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4480_;
}
else
{
lean_object* v_val_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v_val_4481_ = lean_ctor_get(v_x_4478_, 0);
lean_inc(v_val_4481_);
lean_dec_ref_known(v_x_4478_, 1);
lean_inc_ref(v_f_4475_);
v___x_4482_ = lean_apply_2(v_f_4475_, v_val_4481_, lean_box(0));
v___x_4483_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4475_, v_ch_4476_, v_prio_4477_);
return v___x_4483_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4484_, lean_object* v_ch_4485_, lean_object* v_prio_4486_, lean_object* v_x_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4484_, v_ch_4485_, v_prio_4486_, v_x_4487_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4490_, lean_object* v_ch_4491_, lean_object* v_prio_4492_){
_start:
{
lean_object* v___f_4494_; lean_object* v___x_4495_; uint8_t v___x_4496_; lean_object* v___x_4497_; 
lean_inc(v_prio_4492_);
lean_inc_ref(v_ch_4491_);
v___f_4494_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4494_, 0, v_f_4490_);
lean_closure_set(v___f_4494_, 1, v_ch_4491_);
lean_closure_set(v___f_4494_, 2, v_prio_4492_);
v___x_4495_ = l_Std_CloseableChannel_recv___redArg(v_ch_4491_);
v___x_4496_ = 0;
v___x_4497_ = lean_io_bind_task(v___x_4495_, v___f_4494_, v_prio_4492_, v___x_4496_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4498_, lean_object* v_ch_4499_, lean_object* v_prio_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4498_, v_ch_4499_, v_prio_4500_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4503_, lean_object* v_f_4504_, lean_object* v_ch_4505_, lean_object* v_prio_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4504_, v_ch_4505_, v_prio_4506_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4509_, lean_object* v_f_4510_, lean_object* v_ch_4511_, lean_object* v_prio_4512_, lean_object* v_a_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4509_, v_f_4510_, v_ch_4511_, v_prio_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(lean_object* v_x_4515_){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_box(0);
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0___boxed(lean_object* v_x_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(v_x_4519_);
lean_dec_ref(v_x_4519_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg(){
_start:
{
lean_object* v___x_4528_; 
v___x_4528_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__2));
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object* v___dummy_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
return v_res_4530_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4531_; 
v___x_4531_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4532_, lean_object* v_inst_4533_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4535_, lean_object* v_inst_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4535_, v_inst_4536_);
lean_dec(v_inst_4536_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object* v_a_4538_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4539_, 0, v_a_4538_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object* v___f_4540_, lean_object* v_x_4541_){
_start:
{
if (lean_obj_tag(v_x_4541_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4551_; 
lean_dec_ref(v___f_4540_);
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
lean_object* v_a_4552_; 
v_a_4552_ = lean_ctor_get(v_x_4541_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v_x_4541_, 1);
if (lean_obj_tag(v_a_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4561_; 
lean_dec_ref(v___f_4540_);
v_a_4553_ = lean_ctor_get(v_a_4552_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_a_4552_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4555_ = v_a_4552_;
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v_a_4552_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4553_);
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
else
{
lean_object* v_a_4562_; lean_object* v___x_4563_; uint8_t v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v_a_4562_ = lean_ctor_get(v_a_4552_, 0);
lean_inc(v_a_4562_);
lean_dec_ref_known(v_a_4552_, 1);
v___x_4563_ = lean_unsigned_to_nat(0u);
v___x_4564_ = 0;
v___x_4565_ = lean_task_map(v___f_4540_, v_a_4562_, v___x_4563_, v___x_4564_);
v___x_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
return v___x_4566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object* v___f_4567_, lean_object* v_x_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_4567_, v_x_4568_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object* v___f_4571_, lean_object* v_receiver_4572_){
_start:
{
lean_object* v___x_4574_; uint8_t v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = 0;
v___x_4576_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4572_);
v___x_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
v___x_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
v___x_4580_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4574_, v___x_4575_, v___x_4579_, v___f_4571_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object* v___f_4581_, lean_object* v_receiver_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_4581_, v_receiver_4582_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg(){
_start:
{
lean_object* v___f_4591_; 
v___f_4591_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__2));
return v___f_4591_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object* v___dummy_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
return v_res_4593_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4595_, lean_object* v_inst_4596_){
_start:
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0);
return v___x_4597_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4598_, lean_object* v_inst_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4598_, v_inst_4599_);
lean_dec(v_inst_4599_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v___f_4602_, lean_object* v_x_4603_){
_start:
{
if (lean_obj_tag(v_x_4603_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4613_; 
lean_dec_ref(v___f_4602_);
v_a_4605_ = lean_ctor_get(v_x_4603_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v_x_4603_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4607_ = v_x_4603_;
v_isShared_4608_ = v_isSharedCheck_4613_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v_x_4603_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4613_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
lean_object* v___x_4611_; 
v___x_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
return v___x_4611_;
}
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v_a_4614_ = lean_ctor_get(v_x_4603_, 0);
lean_inc(v_a_4614_);
lean_dec_ref_known(v_x_4603_, 1);
v___x_4615_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___closed__0));
v___x_4616_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4616_, 0, lean_box(0));
lean_closure_set(v___x_4616_, 1, lean_box(0));
lean_closure_set(v___x_4616_, 2, lean_box(0));
lean_closure_set(v___x_4616_, 3, v___x_4615_);
lean_closure_set(v___x_4616_, 4, v___f_4602_);
v___x_4617_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4617_, 0, lean_box(0));
lean_closure_set(v___x_4617_, 1, lean_box(0));
lean_closure_set(v___x_4617_, 2, lean_box(0));
lean_closure_set(v___x_4617_, 3, v___x_4616_);
v___x_4618_ = lean_unsigned_to_nat(0u);
v___x_4619_ = 0;
v___x_4620_ = lean_task_map(v___x_4617_, v_a_4614_, v___x_4618_, v___x_4619_);
v___x_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
return v___x_4621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v___f_4622_, lean_object* v_x_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_4622_, v_x_4623_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v___f_4626_, lean_object* v_receiver_4627_, lean_object* v_x_4628_){
_start:
{
lean_object* v___x_4630_; uint8_t v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4630_ = lean_unsigned_to_nat(0u);
v___x_4631_ = 0;
v___x_4632_ = l_Std_CloseableChannel_send___redArg(v_receiver_4627_, v_x_4628_);
v___x_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4632_);
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
v___x_4635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4630_, v___x_4631_, v___x_4634_, v___f_4626_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0___boxed(lean_object* v___f_4636_, lean_object* v_receiver_4637_, lean_object* v_x_4638_, lean_object* v___y_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(v___f_4636_, v_receiver_4637_, v_x_4638_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v_x_4641_){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v_x_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(v_x_4644_);
lean_dec_ref(v_x_4644_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(lean_object* v___f_4647_, lean_object* v_socket_4648_, lean_object* v_x_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v___x_4652_; 
v___x_4652_ = lean_apply_3(v___f_4647_, v_socket_4648_, v___y_4650_, lean_box(0));
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object* v___f_4653_, lean_object* v_socket_4654_, lean_object* v_x_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(v___f_4653_, v_socket_4654_, v_x_4655_, v___y_4656_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(lean_object* v___f_4659_, lean_object* v___x_4660_, lean_object* v_socket_4661_, lean_object* v_data_4662_){
_start:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
v___x_4664_ = lean_unsigned_to_nat(0u);
v___x_4665_ = lean_array_get_size(v_data_4662_);
v___x_4666_ = lean_box(0);
v___x_4667_ = lean_nat_dec_lt(v___x_4664_, v___x_4665_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4668_; 
lean_dec_ref(v_data_4662_);
lean_dec_ref(v_socket_4661_);
lean_dec_ref(v___x_4660_);
lean_dec_ref(v___f_4659_);
v___x_4668_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4668_;
}
else
{
lean_object* v___f_4669_; uint8_t v___x_4670_; 
v___f_4669_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4669_, 0, v___f_4659_);
lean_closure_set(v___f_4669_, 1, v_socket_4661_);
v___x_4670_ = lean_nat_dec_le(v___x_4665_, v___x_4665_);
if (v___x_4670_ == 0)
{
if (v___x_4667_ == 0)
{
lean_object* v___x_4671_; 
lean_dec_ref(v___f_4669_);
lean_dec_ref(v_data_4662_);
lean_dec_ref(v___x_4660_);
v___x_4671_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4671_;
}
else
{
size_t v___x_4672_; size_t v___x_4673_; lean_object* v___x_749__overap_4674_; lean_object* v___x_4675_; 
v___x_4672_ = ((size_t)0ULL);
v___x_4673_ = lean_usize_of_nat(v___x_4665_);
v___x_749__overap_4674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4660_, v___f_4669_, v_data_4662_, v___x_4672_, v___x_4673_, v___x_4666_);
v___x_4675_ = lean_apply_1(v___x_749__overap_4674_, lean_box(0));
return v___x_4675_;
}
}
else
{
size_t v___x_4676_; size_t v___x_4677_; lean_object* v___x_752__overap_4678_; lean_object* v___x_4679_; 
v___x_4676_ = ((size_t)0ULL);
v___x_4677_ = lean_usize_of_nat(v___x_4665_);
v___x_752__overap_4678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4660_, v___f_4669_, v_data_4662_, v___x_4676_, v___x_4677_, v___x_4666_);
v___x_4679_ = lean_apply_1(v___x_752__overap_4678_, lean_box(0));
return v___x_4679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object* v___f_4680_, lean_object* v___x_4681_, lean_object* v_socket_4682_, lean_object* v_data_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(v___f_4680_, v___x_4681_, v_socket_4682_, v_data_4683_);
return v_res_4685_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_4691_; 
v___x_4691_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_4691_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___x_4692_; lean_object* v___f_4693_; lean_object* v___f_4694_; 
v___x_4692_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_4693_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1));
v___f_4694_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4694_, 0, v___f_4693_);
lean_closure_set(v___f_4694_, 1, v___x_4692_);
return v___f_4694_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5(void){
_start:
{
lean_object* v___f_4695_; lean_object* v___f_4696_; lean_object* v___f_4697_; lean_object* v___x_4698_; 
v___f_4695_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_4696_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4);
v___f_4697_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1));
v___x_4698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4698_, 0, v___f_4697_);
lean_ctor_set(v___x_4698_, 1, v___f_4696_);
lean_ctor_set(v___x_4698_, 2, v___f_4695_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
return v_res_4702_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4703_; 
v___x_4703_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4704_, lean_object* v_inst_4705_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4707_, lean_object* v_inst_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4707_, v_inst_4708_);
lean_dec(v_inst_4708_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4710_){
_start:
{
lean_inc_ref(v_ch_4710_);
return v_ch_4710_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_Std_CloseableChannel_sync___redArg(v_ch_4711_);
lean_dec_ref(v_ch_4711_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4713_, lean_object* v_ch_4714_){
_start:
{
lean_inc_ref(v_ch_4714_);
return v_ch_4714_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4715_, lean_object* v_ch_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l_Std_CloseableChannel_sync(v_00_u03b1_4715_, v_ch_4716_);
lean_dec_ref(v_ch_4716_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4718_){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l_Std_CloseableChannel_new___redArg(v_capacity_4718_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4721_, lean_object* v_a_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4721_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4724_, lean_object* v_capacity_4725_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l_Std_CloseableChannel_new___redArg(v_capacity_4725_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4728_, lean_object* v_capacity_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4728_, v_capacity_4729_);
return v_res_4731_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4732_, lean_object* v_v_4733_){
_start:
{
uint8_t v___x_4735_; 
v___x_4735_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4732_, v_v_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4736_, lean_object* v_v_4737_, lean_object* v_a_4738_){
_start:
{
uint8_t v_res_4739_; lean_object* v_r_4740_; 
v_res_4739_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4736_, v_v_4737_);
v_r_4740_ = lean_box(v_res_4739_);
return v_r_4740_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4741_, lean_object* v_ch_4742_, lean_object* v_v_4743_){
_start:
{
uint8_t v___x_4745_; 
v___x_4745_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4742_, v_v_4743_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4746_, lean_object* v_ch_4747_, lean_object* v_v_4748_, lean_object* v_a_4749_){
_start:
{
uint8_t v_res_4750_; lean_object* v_r_4751_; 
v_res_4750_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4746_, v_ch_4747_, v_v_4748_);
v_r_4751_ = lean_box(v_res_4750_);
return v_r_4751_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4752_, lean_object* v_v_4753_){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = l_Std_CloseableChannel_send___redArg(v_ch_4752_, v_v_4753_);
v___x_4756_ = lean_io_wait(v___x_4755_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4756_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4756_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set_tag(v___x_4759_, 1);
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
else
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4772_; 
v_a_4765_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4767_ = v___x_4756_;
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4756_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4770_; 
if (v_isShared_4768_ == 0)
{
lean_ctor_set_tag(v___x_4767_, 0);
v___x_4770_ = v___x_4767_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_4773_, lean_object* v_v_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4773_, v_v_4774_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_4777_, lean_object* v_ch_4778_, lean_object* v_v_4779_){
_start:
{
lean_object* v___x_4781_; 
v___x_4781_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4778_, v_v_4779_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_4782_, lean_object* v_ch_4783_, lean_object* v_v_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_4782_, v_ch_4783_, v_v_4784_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_4787_){
_start:
{
lean_object* v___x_4789_; 
v___x_4789_ = l_Std_CloseableChannel_close___redArg(v_ch_4787_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_4790_, lean_object* v_a_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_4790_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_4793_, lean_object* v_ch_4794_){
_start:
{
lean_object* v___x_4796_; 
v___x_4796_ = l_Std_CloseableChannel_close___redArg(v_ch_4794_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_4797_, lean_object* v_ch_4798_, lean_object* v_a_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_4797_, v_ch_4798_);
return v_res_4800_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_4801_){
_start:
{
uint8_t v___x_4803_; 
v___x_4803_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4801_);
return v___x_4803_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_4804_, lean_object* v_a_4805_){
_start:
{
uint8_t v_res_4806_; lean_object* v_r_4807_; 
v_res_4806_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_4804_);
v_r_4807_ = lean_box(v_res_4806_);
return v_r_4807_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_4808_, lean_object* v_ch_4809_){
_start:
{
uint8_t v___x_4811_; 
v___x_4811_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4809_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_4812_, lean_object* v_ch_4813_, lean_object* v_a_4814_){
_start:
{
uint8_t v_res_4815_; lean_object* v_r_4816_; 
v_res_4815_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_4812_, v_ch_4813_);
v_r_4816_ = lean_box(v_res_4815_);
return v_r_4816_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_4817_){
_start:
{
lean_object* v___x_4819_; 
v___x_4819_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4817_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_4820_, lean_object* v_a_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_4820_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_4823_, lean_object* v_ch_4824_){
_start:
{
lean_object* v___x_4826_; 
v___x_4826_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4824_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_4827_, lean_object* v_ch_4828_, lean_object* v_a_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_4827_, v_ch_4828_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_4831_){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = l_Std_CloseableChannel_recv___redArg(v_ch_4831_);
v___x_4834_ = lean_io_wait(v___x_4833_);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4835_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_4838_, lean_object* v_ch_4839_){
_start:
{
lean_object* v___x_4841_; 
v___x_4841_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4839_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_4842_, lean_object* v_ch_4843_, lean_object* v_a_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_4842_, v_ch_4843_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_4846_, lean_object* v_b_4847_, lean_object* v_f_4848_, lean_object* v_toBind_4849_, lean_object* v___f_4850_, lean_object* v_____do__lift_4851_){
_start:
{
if (lean_obj_tag(v_____do__lift_4851_) == 0)
{
lean_object* v___x_4852_; 
lean_dec(v___f_4850_);
lean_dec(v_toBind_4849_);
lean_dec(v_f_4848_);
v___x_4852_ = lean_apply_2(v_toPure_4846_, lean_box(0), v_b_4847_);
return v___x_4852_;
}
else
{
lean_object* v_val_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
lean_dec(v_toPure_4846_);
v_val_4853_ = lean_ctor_get(v_____do__lift_4851_, 0);
lean_inc(v_val_4853_);
lean_dec_ref_known(v_____do__lift_4851_, 1);
v___x_4854_ = lean_apply_2(v_f_4848_, v_val_4853_, v_b_4847_);
v___x_4855_ = lean_apply_4(v_toBind_4849_, lean_box(0), lean_box(0), v___x_4854_, v___f_4850_);
return v___x_4855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_4856_, lean_object* v_inst_4857_, lean_object* v_ch_4858_, lean_object* v_f_4859_, lean_object* v_b_4860_){
_start:
{
lean_object* v_toApplicative_4861_; lean_object* v_toBind_4862_; lean_object* v_toPure_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___f_4866_; lean_object* v___f_4867_; lean_object* v___x_4868_; 
v_toApplicative_4861_ = lean_ctor_get(v_inst_4856_, 0);
v_toBind_4862_ = lean_ctor_get(v_inst_4856_, 1);
lean_inc_n(v_toBind_4862_, 2);
v_toPure_4863_ = lean_ctor_get(v_toApplicative_4861_, 1);
lean_inc_n(v_toPure_4863_, 2);
lean_inc_ref(v_ch_4858_);
v___x_4864_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_4864_, 0, lean_box(0));
lean_closure_set(v___x_4864_, 1, v_ch_4858_);
lean_inc(v_inst_4857_);
v___x_4865_ = lean_apply_2(v_inst_4857_, lean_box(0), v___x_4864_);
lean_inc(v_f_4859_);
v___f_4866_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4866_, 0, v_toPure_4863_);
lean_closure_set(v___f_4866_, 1, v_inst_4856_);
lean_closure_set(v___f_4866_, 2, v_inst_4857_);
lean_closure_set(v___f_4866_, 3, v_ch_4858_);
lean_closure_set(v___f_4866_, 4, v_f_4859_);
v___f_4867_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_4867_, 0, v_toPure_4863_);
lean_closure_set(v___f_4867_, 1, v_b_4860_);
lean_closure_set(v___f_4867_, 2, v_f_4859_);
lean_closure_set(v___f_4867_, 3, v_toBind_4862_);
lean_closure_set(v___f_4867_, 4, v___f_4866_);
v___x_4868_ = lean_apply_4(v_toBind_4862_, lean_box(0), lean_box(0), v___x_4865_, v___f_4867_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_4869_, lean_object* v_inst_4870_, lean_object* v_inst_4871_, lean_object* v_ch_4872_, lean_object* v_f_4873_, lean_object* v_____do__lift_4874_){
_start:
{
if (lean_obj_tag(v_____do__lift_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v___x_4876_; 
lean_dec(v_f_4873_);
lean_dec_ref(v_ch_4872_);
lean_dec(v_inst_4871_);
lean_dec_ref(v_inst_4870_);
v_a_4875_ = lean_ctor_get(v_____do__lift_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref_known(v_____do__lift_4874_, 1);
v___x_4876_ = lean_apply_2(v_toPure_4869_, lean_box(0), v_a_4875_);
return v___x_4876_;
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4878_; 
lean_dec(v_toPure_4869_);
v_a_4877_ = lean_ctor_get(v_____do__lift_4874_, 0);
lean_inc(v_a_4877_);
lean_dec_ref_known(v_____do__lift_4874_, 1);
v___x_4878_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4870_, v_inst_4871_, v_ch_4872_, v_f_4873_, v_a_4877_);
return v___x_4878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_4879_, lean_object* v_00_u03b1_4880_, lean_object* v_00_u03b2_4881_, lean_object* v_inst_4882_, lean_object* v_inst_4883_, lean_object* v_ch_4884_, lean_object* v_f_4885_, lean_object* v_b_4886_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4882_, v_inst_4883_, v_ch_4884_, v_f_4885_, v_b_4886_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_4888_, lean_object* v_inst_4889_, lean_object* v_ch_4890_, lean_object* v_b_4891_, lean_object* v_f_4892_){
_start:
{
lean_object* v___x_4893_; 
v___x_4893_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4888_, v_inst_4889_, v_ch_4890_, v_f_4892_, v_b_4891_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_4894_, lean_object* v_00_u03b1_4895_, lean_object* v_inst_4896_, lean_object* v_inst_4897_, lean_object* v_00_u03b2_4898_, lean_object* v_ch_4899_, lean_object* v_b_4900_, lean_object* v_f_4901_){
_start:
{
lean_object* v___x_4902_; 
v___x_4902_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4896_, v_inst_4897_, v_ch_4899_, v_f_4901_, v_b_4900_);
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_4903_, lean_object* v_inst_4904_, lean_object* v_00_u03b2_4905_, lean_object* v_ch_4906_, lean_object* v_b_4907_, lean_object* v_f_4908_){
_start:
{
lean_object* v___x_4909_; 
v___x_4909_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4903_, v_inst_4904_, v_ch_4906_, v_f_4908_, v_b_4907_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_4910_, lean_object* v_inst_4911_){
_start:
{
lean_object* v___f_4912_; 
v___f_4912_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4912_, 0, v_inst_4910_);
lean_closure_set(v___f_4912_, 1, v_inst_4911_);
return v___f_4912_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_4913_, lean_object* v_00_u03b1_4914_, lean_object* v_inst_4915_, lean_object* v_inst_4916_){
_start:
{
lean_object* v___f_4917_; 
v___f_4917_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4917_, 0, v_inst_4915_);
lean_closure_set(v___f_4917_, 1, v_inst_4916_);
return v___f_4917_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_4918_){
_start:
{
lean_object* v___x_4920_; 
v___x_4920_ = l_Std_CloseableChannel_new___redArg(v_capacity_4918_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Std_Channel_new___redArg(v_capacity_4921_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_4924_, lean_object* v_capacity_4925_){
_start:
{
lean_object* v___x_4927_; 
v___x_4927_ = l_Std_CloseableChannel_new___redArg(v_capacity_4925_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_4928_, lean_object* v_capacity_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Std_Channel_new(v_00_u03b1_4928_, v_capacity_4929_);
return v_res_4931_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_4932_, lean_object* v_v_4933_){
_start:
{
uint8_t v___x_4935_; 
v___x_4935_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4932_, v_v_4933_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_4936_, lean_object* v_v_4937_, lean_object* v_a_4938_){
_start:
{
uint8_t v_res_4939_; lean_object* v_r_4940_; 
v_res_4939_ = l_Std_Channel_trySend___redArg(v_ch_4936_, v_v_4937_);
v_r_4940_ = lean_box(v_res_4939_);
return v_r_4940_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_4941_, lean_object* v_ch_4942_, lean_object* v_v_4943_){
_start:
{
uint8_t v___x_4945_; 
v___x_4945_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4942_, v_v_4943_);
return v___x_4945_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_4946_, lean_object* v_ch_4947_, lean_object* v_v_4948_, lean_object* v_a_4949_){
_start:
{
uint8_t v_res_4950_; lean_object* v_r_4951_; 
v_res_4950_ = l_Std_Channel_trySend(v_00_u03b1_4946_, v_ch_4947_, v_v_4948_);
v_r_4951_ = lean_box(v_res_4950_);
return v_r_4951_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4952_ = lean_box(0);
v___x_4953_ = lean_task_pure(v___x_4952_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_4954_){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_142__overap_4959_; lean_object* v___x_4960_; 
v___x_4956_ = l_instMonadBaseIO;
v___x_4957_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4958_ = l_instInhabitedOfMonad___redArg(v___x_4956_, v___x_4957_);
v___x_142__overap_4959_ = lean_panic_fn_borrowed(v___x_4958_, v_msg_4954_);
lean_dec(v___x_4958_);
v___x_4960_ = lean_apply_1(v___x_142__overap_4959_, lean_box(0));
return v___x_4960_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_4961_);
return v_res_4963_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4967_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4968_ = lean_unsigned_to_nat(21u);
v___x_4969_ = lean_unsigned_to_nat(872u);
v___x_4970_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_4971_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4972_ = l_mkPanicMessageWithDecl(v___x_4971_, v___x_4970_, v___x_4969_, v___x_4968_, v___x_4967_);
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_4973_){
_start:
{
if (lean_obj_tag(v_x_4973_) == 0)
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4975_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_4976_ = l_panic___at___00Std_Channel_send_spec__0(v___x_4975_);
return v___x_4976_;
}
else
{
lean_object* v___x_4977_; 
v___x_4977_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4977_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_4978_, lean_object* v___y_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l_Std_Channel_send___redArg___lam__0(v_x_4978_);
lean_dec_ref(v_x_4978_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_4982_, lean_object* v_v_4983_){
_start:
{
lean_object* v___f_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; uint8_t v___x_4988_; lean_object* v___x_4989_; 
v___f_4985_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_4986_ = l_Std_CloseableChannel_send___redArg(v_ch_4982_, v_v_4983_);
v___x_4987_ = lean_unsigned_to_nat(0u);
v___x_4988_ = 1;
v___x_4989_ = lean_io_bind_task(v___x_4986_, v___f_4985_, v___x_4987_, v___x_4988_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_4990_, lean_object* v_v_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Std_Channel_send___redArg(v_ch_4990_, v_v_4991_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_4994_, lean_object* v_ch_4995_, lean_object* v_v_4996_){
_start:
{
lean_object* v___x_4998_; 
v___x_4998_ = l_Std_Channel_send___redArg(v_ch_4995_, v_v_4996_);
return v___x_4998_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_4999_, lean_object* v_ch_5000_, lean_object* v_v_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Std_Channel_send(v_00_u03b1_4999_, v_ch_5000_, v_v_5001_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_5004_){
_start:
{
lean_object* v___x_5006_; 
v___x_5006_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5004_);
return v___x_5006_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_5007_, lean_object* v_a_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l_Std_Channel_tryRecv___redArg(v_ch_5007_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_5010_, lean_object* v_ch_5011_){
_start:
{
lean_object* v___x_5013_; 
v___x_5013_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5011_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_5014_, lean_object* v_ch_5015_, lean_object* v_a_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l_Std_Channel_tryRecv(v_00_u03b1_5014_, v_ch_5015_);
return v_res_5017_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5019_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_5020_ = lean_unsigned_to_nat(16u);
v___x_5021_ = lean_unsigned_to_nat(883u);
v___x_5022_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_5023_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_5024_ = l_mkPanicMessageWithDecl(v___x_5023_, v___x_5022_, v___x_5021_, v___x_5020_, v___x_5019_);
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_5025_, lean_object* v_x_5026_){
_start:
{
if (lean_obj_tag(v_x_5026_) == 0)
{
lean_object* v___x_5028_; lean_object* v___x_144__overap_5029_; lean_object* v___x_5030_; 
v___x_5028_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_144__overap_5029_ = l_panic___redArg(v___x_5025_, v___x_5028_);
v___x_5030_ = lean_apply_1(v___x_144__overap_5029_, lean_box(0));
return v___x_5030_;
}
else
{
lean_object* v_val_5031_; lean_object* v___x_5032_; 
v_val_5031_ = lean_ctor_get(v_x_5026_, 0);
lean_inc(v_val_5031_);
lean_dec_ref_known(v_x_5026_, 1);
v___x_5032_ = lean_task_pure(v_val_5031_);
return v___x_5032_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_5033_, lean_object* v_x_5034_, lean_object* v___y_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Std_Channel_recv___redArg___lam__0(v___x_5033_, v_x_5034_);
lean_dec(v___x_5033_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_5037_, lean_object* v_ch_5038_){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___f_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; uint8_t v___x_5046_; lean_object* v___x_5047_; 
v___x_5040_ = l_instMonadBaseIO;
v___x_5041_ = lean_task_pure(v_inst_5037_);
v___x_5042_ = l_instInhabitedOfMonad___redArg(v___x_5040_, v___x_5041_);
v___f_5043_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5043_, 0, v___x_5042_);
v___x_5044_ = l_Std_CloseableChannel_recv___redArg(v_ch_5038_);
v___x_5045_ = lean_unsigned_to_nat(0u);
v___x_5046_ = 1;
v___x_5047_ = lean_io_bind_task(v___x_5044_, v___f_5043_, v___x_5045_, v___x_5046_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_5048_, lean_object* v_ch_5049_, lean_object* v_a_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l_Std_Channel_recv___redArg(v_inst_5048_, v_ch_5049_);
return v_res_5051_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_5052_, lean_object* v_inst_5053_, lean_object* v_ch_5054_){
_start:
{
lean_object* v___x_5056_; 
v___x_5056_ = l_Std_Channel_recv___redArg(v_inst_5053_, v_ch_5054_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_5057_, lean_object* v_inst_5058_, lean_object* v_ch_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Std_Channel_recv(v_00_u03b1_5057_, v_inst_5058_, v_ch_5059_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_5062_){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5064_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5062_);
v___x_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5064_);
v___x_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5065_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_5067_, lean_object* v___y_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5067_);
return v_res_5069_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5073_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_5074_ = lean_unsigned_to_nat(14u);
v___x_5075_ = lean_unsigned_to_nat(22u);
v___x_5076_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_5077_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_5078_ = l_mkPanicMessageWithDecl(v___x_5077_, v___x_5076_, v___x_5075_, v___x_5074_, v___x_5073_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_5079_, lean_object* v_inst_5080_, lean_object* v_x_5081_){
_start:
{
lean_object* v___y_5084_; lean_object* v___y_5088_; 
if (lean_obj_tag(v_x_5081_) == 0)
{
lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5090_ = lean_box(0);
v___x_5091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5090_);
return v___x_5091_;
}
else
{
lean_object* v_val_5092_; 
v_val_5092_ = lean_ctor_get(v_x_5081_, 0);
lean_inc(v_val_5092_);
lean_dec_ref_known(v_x_5081_, 1);
if (lean_obj_tag(v_val_5092_) == 0)
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
v_a_5093_ = lean_ctor_get(v_val_5092_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v_val_5092_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v_val_5092_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v_val_5092_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
v___y_5084_ = v___x_5098_;
goto v___jp_5083_;
}
}
}
else
{
lean_object* v_a_5101_; 
v_a_5101_ = lean_ctor_get(v_val_5092_, 0);
lean_inc(v_a_5101_);
lean_dec_ref_known(v_val_5092_, 1);
if (lean_obj_tag(v_a_5101_) == 0)
{
lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5102_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5103_ = l_panic___redArg(v_inst_5080_, v___x_5102_);
v___y_5088_ = v___x_5103_;
goto v___jp_5087_;
}
else
{
lean_object* v_val_5104_; 
v_val_5104_ = lean_ctor_get(v_a_5101_, 0);
lean_inc(v_val_5104_);
lean_dec_ref_known(v_a_5101_, 1);
v___y_5088_ = v_val_5104_;
goto v___jp_5087_;
}
}
}
v___jp_5083_:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = lean_io_promise_resolve(v___y_5084_, v_promise_5079_);
v___x_5086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5086_, 0, v___x_5085_);
return v___x_5086_;
}
v___jp_5087_:
{
lean_object* v___x_5089_; 
v___x_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5089_, 0, v___y_5088_);
v___y_5084_ = v___x_5089_;
goto v___jp_5083_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5105_, lean_object* v_inst_5106_, lean_object* v_x_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5105_, v_inst_5106_, v_x_5107_);
lean_dec(v_inst_5106_);
lean_dec(v_promise_5105_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5110_, lean_object* v___f_5111_, lean_object* v_x_5112_){
_start:
{
lean_object* v_val_5115_; 
if (lean_obj_tag(v_x_5112_) == 0)
{
lean_object* v___x_5117_; 
lean_dec_ref(v___f_5111_);
v___x_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5117_, 0, v_x_5112_);
return v___x_5117_;
}
else
{
lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5133_; 
v_isSharedCheck_5133_ = !lean_is_exclusive(v_x_5112_);
if (v_isSharedCheck_5133_ == 0)
{
lean_object* v_unused_5134_; 
v_unused_5134_ = lean_ctor_get(v_x_5112_, 0);
lean_dec(v_unused_5134_);
v___x_5119_ = v_x_5112_;
v_isShared_5120_ = v_isSharedCheck_5133_;
goto v_resetjp_5118_;
}
else
{
lean_dec(v_x_5112_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5133_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; uint8_t v___x_5123_; lean_object* v___x_5124_; 
v___x_5121_ = lean_io_promise_result_opt(v_a_5110_);
v___x_5122_ = lean_unsigned_to_nat(0u);
v___x_5123_ = 1;
v___x_5124_ = l_EIO_chainTask___redArg(v___x_5121_, v___f_5111_, v___x_5122_, v___x_5123_);
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v_a_5125_; lean_object* v___x_5127_; 
v_a_5125_ = lean_ctor_get(v___x_5124_, 0);
lean_inc(v_a_5125_);
lean_dec_ref_known(v___x_5124_, 1);
if (v_isShared_5120_ == 0)
{
lean_ctor_set(v___x_5119_, 0, v_a_5125_);
v___x_5127_ = v___x_5119_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5125_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
v_val_5115_ = v___x_5127_;
goto v___jp_5114_;
}
}
else
{
lean_object* v_a_5129_; lean_object* v___x_5131_; 
v_a_5129_ = lean_ctor_get(v___x_5124_, 0);
lean_inc(v_a_5129_);
lean_dec_ref_known(v___x_5124_, 1);
if (v_isShared_5120_ == 0)
{
lean_ctor_set_tag(v___x_5119_, 0);
lean_ctor_set(v___x_5119_, 0, v_a_5129_);
v___x_5131_ = v___x_5119_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5129_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
v_val_5115_ = v___x_5131_;
goto v___jp_5114_;
}
}
}
}
v___jp_5114_:
{
lean_object* v___x_5116_; 
v___x_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5116_, 0, v_val_5115_);
return v___x_5116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5135_, lean_object* v___f_5136_, lean_object* v_x_5137_, lean_object* v___y_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5135_, v___f_5136_, v_x_5137_);
lean_dec(v_a_5135_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5140_, lean_object* v___f_5141_, lean_object* v_finished_5142_, lean_object* v_x_5143_){
_start:
{
if (lean_obj_tag(v_x_5143_) == 0)
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5153_; 
lean_dec(v_finished_5142_);
lean_dec_ref(v___f_5141_);
lean_dec_ref(v_sel_5140_);
v_a_5145_ = lean_ctor_get(v_x_5143_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v_x_5143_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5147_ = v_x_5143_;
v_isShared_5148_ = v_isSharedCheck_5153_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v_x_5143_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5153_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
lean_object* v___x_5151_; 
v___x_5151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5151_, 0, v___x_5150_);
return v___x_5151_;
}
}
}
else
{
lean_object* v_a_5154_; lean_object* v_registerFn_5155_; lean_object* v___f_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; 
v_a_5154_ = lean_ctor_get(v_x_5143_, 0);
lean_inc_n(v_a_5154_, 2);
lean_dec_ref_known(v_x_5143_, 1);
v_registerFn_5155_ = lean_ctor_get(v_sel_5140_, 1);
lean_inc_ref(v_registerFn_5155_);
lean_dec_ref(v_sel_5140_);
v___f_5156_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5156_, 0, v_a_5154_);
lean_closure_set(v___f_5156_, 1, v___f_5141_);
v___x_5157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5157_, 0, v_finished_5142_);
lean_ctor_set(v___x_5157_, 1, v_a_5154_);
v___x_5158_ = lean_unsigned_to_nat(0u);
v___x_5159_ = 0;
v___x_5160_ = lean_apply_2(v_registerFn_5155_, v___x_5157_, lean_box(0));
v___x_5161_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5158_, v___x_5159_, v___x_5160_, v___f_5156_);
return v___x_5161_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5162_, lean_object* v___f_5163_, lean_object* v_finished_5164_, lean_object* v_x_5165_, lean_object* v___y_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5162_, v___f_5163_, v_finished_5164_, v_x_5165_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5168_, lean_object* v_sel_5169_, lean_object* v_waiter_5170_){
_start:
{
lean_object* v_finished_5172_; lean_object* v_promise_5173_; lean_object* v___f_5174_; lean_object* v___f_5175_; lean_object* v___x_5176_; uint8_t v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
v_finished_5172_ = lean_ctor_get(v_waiter_5170_, 0);
lean_inc(v_finished_5172_);
v_promise_5173_ = lean_ctor_get(v_waiter_5170_, 1);
lean_inc(v_promise_5173_);
lean_dec_ref(v_waiter_5170_);
v___f_5174_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5174_, 0, v_promise_5173_);
lean_closure_set(v___f_5174_, 1, v_inst_5168_);
v___f_5175_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5175_, 0, v_sel_5169_);
lean_closure_set(v___f_5175_, 1, v___f_5174_);
lean_closure_set(v___f_5175_, 2, v_finished_5172_);
v___x_5176_ = lean_unsigned_to_nat(0u);
v___x_5177_ = 0;
v___x_5178_ = lean_io_promise_new();
v___x_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5178_);
v___x_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5179_);
v___x_5181_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5176_, v___x_5177_, v___x_5180_, v___f_5175_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5182_, lean_object* v_sel_5183_, lean_object* v_waiter_5184_, lean_object* v___y_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5182_, v_sel_5183_, v_waiter_5184_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5187_, lean_object* v_ch_5188_){
_start:
{
lean_object* v_sel_5189_; lean_object* v_unregisterFn_5190_; lean_object* v___f_5191_; lean_object* v___f_5192_; lean_object* v___x_5193_; 
lean_inc_ref(v_ch_5188_);
v_sel_5189_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5188_);
v_unregisterFn_5190_ = lean_ctor_get(v_sel_5189_, 2);
lean_inc_ref(v_unregisterFn_5190_);
v___f_5191_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5191_, 0, v_ch_5188_);
v___f_5192_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5192_, 0, v_inst_5187_);
lean_closure_set(v___f_5192_, 1, v_sel_5189_);
v___x_5193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5193_, 0, v___f_5191_);
lean_ctor_set(v___x_5193_, 1, v___f_5192_);
lean_ctor_set(v___x_5193_, 2, v_unregisterFn_5190_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5194_, lean_object* v_inst_5195_, lean_object* v_ch_5196_){
_start:
{
lean_object* v___x_5197_; 
v___x_5197_ = l_Std_Channel_recvSelector___redArg(v_inst_5195_, v_ch_5196_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5198_, lean_object* v_inst_5199_, lean_object* v_ch_5200_, lean_object* v_prio_5201_, lean_object* v_v_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5198_, v_inst_5199_, v_ch_5200_, v_prio_5201_, v_v_5202_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5205_, lean_object* v_f_5206_, lean_object* v_ch_5207_, lean_object* v_prio_5208_){
_start:
{
lean_object* v___f_5210_; lean_object* v___x_5211_; uint8_t v___x_5212_; lean_object* v___x_5213_; 
lean_inc(v_prio_5208_);
lean_inc_ref(v_ch_5207_);
lean_inc(v_inst_5205_);
v___f_5210_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5210_, 0, v_f_5206_);
lean_closure_set(v___f_5210_, 1, v_inst_5205_);
lean_closure_set(v___f_5210_, 2, v_ch_5207_);
lean_closure_set(v___f_5210_, 3, v_prio_5208_);
v___x_5211_ = l_Std_Channel_recv___redArg(v_inst_5205_, v_ch_5207_);
v___x_5212_ = 0;
v___x_5213_ = lean_io_bind_task(v___x_5211_, v___f_5210_, v_prio_5208_, v___x_5212_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5214_, lean_object* v_inst_5215_, lean_object* v_ch_5216_, lean_object* v_prio_5217_, lean_object* v_v_5218_){
_start:
{
lean_object* v___x_5220_; lean_object* v___x_5221_; 
lean_inc_ref(v_f_5214_);
v___x_5220_ = lean_apply_2(v_f_5214_, v_v_5218_, lean_box(0));
v___x_5221_ = l_Std_Channel_forAsync___redArg(v_inst_5215_, v_f_5214_, v_ch_5216_, v_prio_5217_);
return v___x_5221_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5222_, lean_object* v_f_5223_, lean_object* v_ch_5224_, lean_object* v_prio_5225_, lean_object* v_a_5226_){
_start:
{
lean_object* v_res_5227_; 
v_res_5227_ = l_Std_Channel_forAsync___redArg(v_inst_5222_, v_f_5223_, v_ch_5224_, v_prio_5225_);
return v_res_5227_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5228_, lean_object* v_inst_5229_, lean_object* v_f_5230_, lean_object* v_ch_5231_, lean_object* v_prio_5232_){
_start:
{
lean_object* v___x_5234_; 
v___x_5234_ = l_Std_Channel_forAsync___redArg(v_inst_5229_, v_f_5230_, v_ch_5231_, v_prio_5232_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5235_, lean_object* v_inst_5236_, lean_object* v_f_5237_, lean_object* v_ch_5238_, lean_object* v_prio_5239_, lean_object* v_a_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Std_Channel_forAsync(v_00_u03b1_5235_, v_inst_5236_, v_f_5237_, v_ch_5238_, v_prio_5239_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5242_, lean_object* v_channel_5243_){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Std_Channel_recvSelector___redArg(v_inst_5242_, v_channel_5243_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5245_){
_start:
{
lean_object* v___f_5246_; lean_object* v___f_5247_; lean_object* v___x_5248_; 
v___f_5246_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5246_, 0, v_inst_5245_);
v___f_5247_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__1));
v___x_5248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5248_, 0, v___f_5246_);
lean_ctor_set(v___x_5248_, 1, v___f_5247_);
return v___x_5248_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5249_, lean_object* v_inst_5250_){
_start:
{
lean_object* v___x_5251_; 
v___x_5251_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5250_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5252_){
_start:
{
lean_object* v___x_5253_; 
v___x_5253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5253_, 0, v_a_5252_);
return v___x_5253_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5254_, lean_object* v_x_5255_){
_start:
{
if (lean_obj_tag(v_x_5255_) == 0)
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5265_; 
lean_dec_ref(v___f_5254_);
v_a_5257_ = lean_ctor_get(v_x_5255_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v_x_5255_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5259_ = v_x_5255_;
v_isShared_5260_ = v_isSharedCheck_5265_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v_x_5255_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5265_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5257_);
v___x_5262_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
lean_object* v___x_5263_; 
v___x_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5263_, 0, v___x_5262_);
return v___x_5263_;
}
}
}
else
{
lean_object* v_a_5266_; 
v_a_5266_ = lean_ctor_get(v_x_5255_, 0);
lean_inc(v_a_5266_);
lean_dec_ref_known(v_x_5255_, 1);
if (lean_obj_tag(v_a_5266_) == 0)
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5275_; 
lean_dec_ref(v___f_5254_);
v_a_5267_ = lean_ctor_get(v_a_5266_, 0);
v_isSharedCheck_5275_ = !lean_is_exclusive(v_a_5266_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5269_ = v_a_5266_;
v_isShared_5270_ = v_isSharedCheck_5275_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v_a_5266_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5275_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
lean_object* v___x_5273_; 
v___x_5273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5273_, 0, v___x_5272_);
return v___x_5273_;
}
}
}
else
{
lean_object* v_a_5276_; lean_object* v___x_5277_; uint8_t v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
v_a_5276_ = lean_ctor_get(v_a_5266_, 0);
lean_inc(v_a_5276_);
lean_dec_ref_known(v_a_5266_, 1);
v___x_5277_ = lean_unsigned_to_nat(0u);
v___x_5278_ = 0;
v___x_5279_ = lean_task_map(v___f_5254_, v_a_5276_, v___x_5277_, v___x_5278_);
v___x_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5279_);
return v___x_5280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5281_, lean_object* v_x_5282_, lean_object* v___y_5283_){
_start:
{
lean_object* v_res_5284_; 
v_res_5284_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5281_, v_x_5282_);
return v_res_5284_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5285_, lean_object* v___f_5286_, lean_object* v_receiver_5287_){
_start:
{
lean_object* v___x_5289_; uint8_t v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5289_ = lean_unsigned_to_nat(0u);
v___x_5290_ = 0;
v___x_5291_ = l_Std_Channel_recv___redArg(v_inst_5285_, v_receiver_5287_);
v___x_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5291_);
v___x_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
v___x_5294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
v___x_5295_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5289_, v___x_5290_, v___x_5294_, v___f_5286_);
return v___x_5295_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5296_, lean_object* v___f_5297_, lean_object* v_receiver_5298_, lean_object* v___y_5299_){
_start:
{
lean_object* v_res_5300_; 
v_res_5300_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5296_, v___f_5297_, v_receiver_5298_);
return v_res_5300_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5304_){
_start:
{
lean_object* v___f_5305_; lean_object* v___f_5306_; 
v___f_5305_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5306_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5306_, 0, v_inst_5304_);
lean_closure_set(v___f_5306_, 1, v___f_5305_);
return v___f_5306_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5307_, lean_object* v_inst_5308_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5308_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v_a_5310_){
_start:
{
lean_object* v___x_5311_; 
v___x_5311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5311_, 0, v_a_5310_);
return v___x_5311_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v___f_5312_, lean_object* v_x_5313_){
_start:
{
if (lean_obj_tag(v_x_5313_) == 0)
{
lean_object* v_a_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5323_; 
lean_dec_ref(v___f_5312_);
v_a_5315_ = lean_ctor_get(v_x_5313_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v_x_5313_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5317_ = v_x_5313_;
v_isShared_5318_ = v_isSharedCheck_5323_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_a_5315_);
lean_dec(v_x_5313_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5323_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5320_; 
if (v_isShared_5318_ == 0)
{
v___x_5320_ = v___x_5317_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5315_);
v___x_5320_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
lean_object* v___x_5321_; 
v___x_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5320_);
return v___x_5321_;
}
}
}
else
{
lean_object* v_a_5324_; lean_object* v___x_5325_; uint8_t v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
v_a_5324_ = lean_ctor_get(v_x_5313_, 0);
lean_inc(v_a_5324_);
lean_dec_ref_known(v_x_5313_, 1);
v___x_5325_ = lean_unsigned_to_nat(0u);
v___x_5326_ = 0;
v___x_5327_ = lean_task_map(v___f_5312_, v_a_5324_, v___x_5325_, v___x_5326_);
v___x_5328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5327_);
return v___x_5328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5329_, lean_object* v_x_5330_, lean_object* v___y_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_5329_, v_x_5330_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v___f_5333_, lean_object* v_receiver_5334_, lean_object* v_x_5335_){
_start:
{
lean_object* v___x_5337_; uint8_t v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5337_ = lean_unsigned_to_nat(0u);
v___x_5338_ = 0;
v___x_5339_ = l_Std_Channel_send___redArg(v_receiver_5334_, v_x_5335_);
v___x_5340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5340_, 0, v___x_5339_);
v___x_5341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5340_);
v___x_5342_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5337_, v___x_5338_, v___x_5341_, v___f_5333_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5343_, lean_object* v_receiver_5344_, lean_object* v_x_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(v___f_5343_, v_receiver_5344_, v_x_5345_);
return v_res_5347_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_5353_; lean_object* v___f_5354_; lean_object* v___f_5355_; 
v___x_5353_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5354_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5355_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5355_, 0, v___f_5354_);
lean_closure_set(v___f_5355_, 1, v___x_5353_);
return v___f_5355_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___f_5356_; lean_object* v___f_5357_; lean_object* v___f_5358_; lean_object* v___x_5359_; 
v___f_5356_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5357_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5358_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2));
v___x_5359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5359_, 0, v___f_5358_);
lean_ctor_set(v___x_5359_, 1, v___f_5357_);
lean_ctor_set(v___x_5359_, 2, v___f_5356_);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_5361_; 
v___x_5361_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4);
return v___x_5361_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_5362_){
_start:
{
lean_object* v_res_5363_; 
v_res_5363_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg();
return v_res_5363_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5364_; 
v___x_5364_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg();
return v___x_5364_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5365_, lean_object* v_inst_5366_){
_start:
{
lean_object* v___x_5367_; 
v___x_5367_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__0, &l_Std_Channel_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__0);
return v___x_5367_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5368_, lean_object* v_inst_5369_){
_start:
{
lean_object* v_res_5370_; 
v_res_5370_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_5368_, v_inst_5369_);
lean_dec(v_inst_5369_);
return v_res_5370_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object* v_ch_5371_){
_start:
{
lean_inc_ref(v_ch_5371_);
return v_ch_5371_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object* v_ch_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_Std_Channel_sync___redArg(v_ch_5372_);
lean_dec_ref(v_ch_5372_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object* v_00_u03b1_5374_, lean_object* v_ch_5375_){
_start:
{
lean_inc_ref(v_ch_5375_);
return v_ch_5375_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object* v_00_u03b1_5376_, lean_object* v_ch_5377_){
_start:
{
lean_object* v_res_5378_; 
v_res_5378_ = l_Std_Channel_sync(v_00_u03b1_5376_, v_ch_5377_);
lean_dec_ref(v_ch_5377_);
return v_res_5378_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg(lean_object* v_capacity_5379_){
_start:
{
lean_object* v___x_5381_; 
v___x_5381_ = l_Std_CloseableChannel_new___redArg(v_capacity_5379_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object* v_capacity_5382_, lean_object* v_a_5383_){
_start:
{
lean_object* v_res_5384_; 
v_res_5384_ = l_Std_Channel_Sync_new___redArg(v_capacity_5382_);
return v_res_5384_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new(lean_object* v_00_u03b1_5385_, lean_object* v_capacity_5386_){
_start:
{
lean_object* v___x_5388_; 
v___x_5388_ = l_Std_CloseableChannel_new___redArg(v_capacity_5386_);
return v___x_5388_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object* v_00_u03b1_5389_, lean_object* v_capacity_5390_, lean_object* v_a_5391_){
_start:
{
lean_object* v_res_5392_; 
v_res_5392_ = l_Std_Channel_Sync_new(v_00_u03b1_5389_, v_capacity_5390_);
return v_res_5392_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object* v_ch_5393_, lean_object* v_v_5394_){
_start:
{
uint8_t v___x_5396_; 
v___x_5396_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5393_, v_v_5394_);
return v___x_5396_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object* v_ch_5397_, lean_object* v_v_5398_, lean_object* v_a_5399_){
_start:
{
uint8_t v_res_5400_; lean_object* v_r_5401_; 
v_res_5400_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5397_, v_v_5398_);
v_r_5401_ = lean_box(v_res_5400_);
return v_r_5401_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend(lean_object* v_00_u03b1_5402_, lean_object* v_ch_5403_, lean_object* v_v_5404_){
_start:
{
uint8_t v___x_5406_; 
v___x_5406_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5403_, v_v_5404_);
return v___x_5406_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object* v_00_u03b1_5407_, lean_object* v_ch_5408_, lean_object* v_v_5409_, lean_object* v_a_5410_){
_start:
{
uint8_t v_res_5411_; lean_object* v_r_5412_; 
v_res_5411_ = l_Std_Channel_Sync_trySend(v_00_u03b1_5407_, v_ch_5408_, v_v_5409_);
v_r_5412_ = lean_box(v_res_5411_);
return v_r_5412_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg(lean_object* v_ch_5413_, lean_object* v_v_5414_){
_start:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5416_ = l_Std_Channel_send___redArg(v_ch_5413_, v_v_5414_);
v___x_5417_ = lean_io_wait(v___x_5416_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object* v_ch_5418_, lean_object* v_v_5419_, lean_object* v_a_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Std_Channel_Sync_send___redArg(v_ch_5418_, v_v_5419_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send(lean_object* v_00_u03b1_5422_, lean_object* v_ch_5423_, lean_object* v_v_5424_){
_start:
{
lean_object* v___x_5426_; 
v___x_5426_ = l_Std_Channel_Sync_send___redArg(v_ch_5423_, v_v_5424_);
return v___x_5426_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object* v_00_u03b1_5427_, lean_object* v_ch_5428_, lean_object* v_v_5429_, lean_object* v_a_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l_Std_Channel_Sync_send(v_00_u03b1_5427_, v_ch_5428_, v_v_5429_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object* v_ch_5432_){
_start:
{
lean_object* v___x_5434_; 
v___x_5434_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5432_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5435_, lean_object* v_a_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5435_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv(lean_object* v_00_u03b1_5438_, lean_object* v_ch_5439_){
_start:
{
lean_object* v___x_5441_; 
v___x_5441_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5439_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5442_, lean_object* v_ch_5443_, lean_object* v_a_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_5442_, v_ch_5443_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg(lean_object* v_inst_5446_, lean_object* v_ch_5447_){
_start:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; 
v___x_5449_ = l_Std_Channel_recv___redArg(v_inst_5446_, v_ch_5447_);
v___x_5450_ = lean_io_wait(v___x_5449_);
return v___x_5450_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object* v_inst_5451_, lean_object* v_ch_5452_, lean_object* v_a_5453_){
_start:
{
lean_object* v_res_5454_; 
v_res_5454_ = l_Std_Channel_Sync_recv___redArg(v_inst_5451_, v_ch_5452_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv(lean_object* v_00_u03b1_5455_, lean_object* v_inst_5456_, lean_object* v_ch_5457_){
_start:
{
lean_object* v___x_5459_; 
v___x_5459_ = l_Std_Channel_Sync_recv___redArg(v_inst_5456_, v_ch_5457_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object* v_00_u03b1_5460_, lean_object* v_inst_5461_, lean_object* v_ch_5462_, lean_object* v_a_5463_){
_start:
{
lean_object* v_res_5464_; 
v_res_5464_ = l_Std_Channel_Sync_recv(v_00_u03b1_5460_, v_inst_5461_, v_ch_5462_);
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object* v_f_5465_, lean_object* v_b_5466_, lean_object* v_toBind_5467_, lean_object* v___f_5468_, lean_object* v_a_5469_){
_start:
{
lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___x_5470_ = lean_apply_2(v_f_5465_, v_a_5469_, v_b_5466_);
v___x_5471_ = lean_apply_4(v_toBind_5467_, lean_box(0), lean_box(0), v___x_5470_, v___f_5468_);
return v___x_5471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object* v_inst_5472_, lean_object* v_inst_5473_, lean_object* v_inst_5474_, lean_object* v_ch_5475_, lean_object* v_f_5476_, lean_object* v_b_5477_){
_start:
{
lean_object* v_toApplicative_5478_; lean_object* v_toBind_5479_; lean_object* v_toPure_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___f_5483_; lean_object* v___f_5484_; lean_object* v___x_5485_; 
v_toApplicative_5478_ = lean_ctor_get(v_inst_5473_, 0);
v_toBind_5479_ = lean_ctor_get(v_inst_5473_, 1);
lean_inc_n(v_toBind_5479_, 2);
v_toPure_5480_ = lean_ctor_get(v_toApplicative_5478_, 1);
lean_inc(v_toPure_5480_);
lean_inc_ref(v_ch_5475_);
lean_inc(v_inst_5472_);
v___x_5481_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_recv___boxed), 4, 3);
lean_closure_set(v___x_5481_, 0, lean_box(0));
lean_closure_set(v___x_5481_, 1, v_inst_5472_);
lean_closure_set(v___x_5481_, 2, v_ch_5475_);
lean_inc(v_inst_5474_);
v___x_5482_ = lean_apply_2(v_inst_5474_, lean_box(0), v___x_5481_);
lean_inc(v_f_5476_);
v___f_5483_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5483_, 0, v_toPure_5480_);
lean_closure_set(v___f_5483_, 1, v_inst_5472_);
lean_closure_set(v___f_5483_, 2, v_inst_5473_);
lean_closure_set(v___f_5483_, 3, v_inst_5474_);
lean_closure_set(v___f_5483_, 4, v_ch_5475_);
lean_closure_set(v___f_5483_, 5, v_f_5476_);
v___f_5484_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1), 5, 4);
lean_closure_set(v___f_5484_, 0, v_f_5476_);
lean_closure_set(v___f_5484_, 1, v_b_5477_);
lean_closure_set(v___f_5484_, 2, v_toBind_5479_);
lean_closure_set(v___f_5484_, 3, v___f_5483_);
v___x_5485_ = lean_apply_4(v_toBind_5479_, lean_box(0), lean_box(0), v___x_5482_, v___f_5484_);
return v___x_5485_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5486_, lean_object* v_inst_5487_, lean_object* v_inst_5488_, lean_object* v_inst_5489_, lean_object* v_ch_5490_, lean_object* v_f_5491_, lean_object* v_____do__lift_5492_){
_start:
{
if (lean_obj_tag(v_____do__lift_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5494_; 
lean_dec(v_f_5491_);
lean_dec_ref(v_ch_5490_);
lean_dec(v_inst_5489_);
lean_dec_ref(v_inst_5488_);
lean_dec(v_inst_5487_);
v_a_5493_ = lean_ctor_get(v_____do__lift_5492_, 0);
lean_inc(v_a_5493_);
lean_dec_ref_known(v_____do__lift_5492_, 1);
v___x_5494_ = lean_apply_2(v_toPure_5486_, lean_box(0), v_a_5493_);
return v___x_5494_;
}
else
{
lean_object* v_a_5495_; lean_object* v___x_5496_; 
lean_dec(v_toPure_5486_);
v_a_5495_ = lean_ctor_get(v_____do__lift_5492_, 0);
lean_inc(v_a_5495_);
lean_dec_ref_known(v_____do__lift_5492_, 1);
v___x_5496_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5487_, v_inst_5488_, v_inst_5489_, v_ch_5490_, v_f_5491_, v_a_5495_);
return v___x_5496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object* v_00_u03b1_5497_, lean_object* v_m_5498_, lean_object* v_00_u03b2_5499_, lean_object* v_inst_5500_, lean_object* v_inst_5501_, lean_object* v_inst_5502_, lean_object* v_ch_5503_, lean_object* v_f_5504_, lean_object* v_b_5505_){
_start:
{
lean_object* v___x_5506_; 
v___x_5506_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5500_, v_inst_5501_, v_inst_5502_, v_ch_5503_, v_f_5504_, v_b_5505_);
return v___x_5506_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5507_, lean_object* v_inst_5508_, lean_object* v_inst_5509_, lean_object* v_ch_5510_, lean_object* v_b_5511_, lean_object* v_f_5512_){
_start:
{
lean_object* v___x_5513_; 
v___x_5513_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5507_, v_inst_5508_, v_inst_5509_, v_ch_5510_, v_f_5512_, v_b_5511_);
return v___x_5513_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_00_u03b1_5514_, lean_object* v_m_5515_, lean_object* v_inst_5516_, lean_object* v_inst_5517_, lean_object* v_inst_5518_, lean_object* v_00_u03b2_5519_, lean_object* v_ch_5520_, lean_object* v_b_5521_, lean_object* v_f_5522_){
_start:
{
lean_object* v___x_5523_; 
v___x_5523_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5516_, v_inst_5517_, v_inst_5518_, v_ch_5520_, v_f_5522_, v_b_5521_);
return v___x_5523_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5524_, lean_object* v_inst_5525_, lean_object* v_inst_5526_, lean_object* v_00_u03b2_5527_, lean_object* v_ch_5528_, lean_object* v_b_5529_, lean_object* v_f_5530_){
_start:
{
lean_object* v___x_5531_; 
v___x_5531_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5524_, v_inst_5525_, v_inst_5526_, v_ch_5528_, v_f_5530_, v_b_5529_);
return v___x_5531_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5532_, lean_object* v_inst_5533_, lean_object* v_inst_5534_){
_start:
{
lean_object* v___f_5535_; 
v___f_5535_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5535_, 0, v_inst_5532_);
lean_closure_set(v___f_5535_, 1, v_inst_5533_);
lean_closure_set(v___f_5535_, 2, v_inst_5534_);
return v___f_5535_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5536_, lean_object* v_m_5537_, lean_object* v_inst_5538_, lean_object* v_inst_5539_, lean_object* v_inst_5540_){
_start:
{
lean_object* v___f_5541_; 
v___f_5541_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5541_, 0, v_inst_5538_);
lean_closure_set(v___f_5541_, 1, v_inst_5539_);
lean_closure_set(v___f_5541_, 2, v_inst_5540_);
return v___f_5541_;
}
}
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Channel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_Channel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Queue(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* initialize_Std_Async_IO(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_Channel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Channel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_Channel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_Channel(builtin);
}
#ifdef __cplusplus
}
#endif

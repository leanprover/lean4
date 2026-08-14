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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* l_Std_Queue_empty(lean_object*);
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
lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_EAsync_instMonad(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_mapError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0;
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
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1_value),((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value)} };
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
static lean_once_cell_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1;
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
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object*);
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
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0_value),((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value)} };
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
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0;
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
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0_value;
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0_value),((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value)} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_recvSelector___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1 = (const lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1_value;
static const lean_ctor_object l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_value),((lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1_value)}};
static const lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2 = (const lean_object*)&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2_value;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_value)} };
static const lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__1 = (const lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__1_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__1_value)} };
static const lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2 = (const lean_object*)&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2_value;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lean_mk_io_user_error, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instToStringError___closed__0_value)} };
static const lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0 = (const lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_value)} };
static const lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1 = (const lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1_value;
static const lean_closure_object l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2 = (const lean_object*)&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2_value;
static lean_once_cell_t l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3;
static lean_once_cell_t l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4;
static lean_once_cell_t l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5;
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
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Channel_instAsyncWriteOfInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Channel_instAsyncWriteOfInhabited___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Channel_instAsyncWriteOfInhabited___closed__0 = (const lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___closed__0_value;
static const lean_closure_object l_Std_Channel_instAsyncWriteOfInhabited___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___closed__0_value)} };
static const lean_object* l_Std_Channel_instAsyncWriteOfInhabited___closed__1 = (const lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___closed__1_value;
static const lean_closure_object l_Std_Channel_instAsyncWriteOfInhabited___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___closed__1_value)} };
static const lean_object* l_Std_Channel_instAsyncWriteOfInhabited___closed__2 = (const lean_object*)&l_Std_Channel_instAsyncWriteOfInhabited___closed__2_value;
static lean_once_cell_t l_Std_Channel_instAsyncWriteOfInhabited___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Channel_instAsyncWriteOfInhabited___closed__3;
static lean_once_cell_t l_Std_Channel_instAsyncWriteOfInhabited___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Channel_instAsyncWriteOfInhabited___closed__4;
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
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
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
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_CloseableChannel_Error_ctorIdx(v_x_boxed_5_);
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
uint8_t v_x_121__boxed_84_; lean_object* v_res_85_; 
v_x_121__boxed_84_ = lean_unbox(v_x_82_);
v_res_85_ = l_Std_CloseableChannel_instReprError_repr(v_x_121__boxed_84_, v_prec_83_);
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
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_98_ = l_Std_CloseableChannel_Error_ctorIdx(v_x_96_);
v___x_99_ = l_Std_CloseableChannel_Error_ctorIdx(v_y_97_);
v___x_100_ = lean_nat_dec_eq(v___x_98_, v___x_99_);
lean_dec(v___x_99_);
lean_dec(v___x_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instDecidableEqError___boxed(lean_object* v_x_101_, lean_object* v_y_102_){
_start:
{
uint8_t v_x_13__boxed_103_; uint8_t v_y_14__boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_x_13__boxed_103_ = lean_unbox(v_x_101_);
v_y_14__boxed_104_ = lean_unbox(v_y_102_);
v_res_105_ = l_Std_CloseableChannel_instDecidableEqError(v_x_13__boxed_103_, v_y_14__boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint64_t l_Std_CloseableChannel_instHashableError_hash(uint8_t v_x_107_){
_start:
{
if (v_x_107_ == 0)
{
uint64_t v___x_108_; 
v___x_108_ = 0ULL;
return v___x_108_;
}
else
{
uint64_t v___x_109_; 
v___x_109_ = 1ULL;
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instHashableError_hash___boxed(lean_object* v_x_110_){
_start:
{
uint8_t v_x_28__boxed_111_; uint64_t v_res_112_; lean_object* v_r_113_; 
v_x_28__boxed_111_ = lean_unbox(v_x_110_);
v_res_112_ = l_Std_CloseableChannel_instHashableError_hash(v_x_28__boxed_111_);
v_r_113_ = lean_box_uint64(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instToStringError___lam__0(uint8_t v_x_118_){
_start:
{
if (v_x_118_ == 0)
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Std_CloseableChannel_instToStringError___lam__0___closed__0));
return v___x_119_;
}
else
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Std_CloseableChannel_instToStringError___lam__0___closed__1));
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instToStringError___lam__0___boxed(lean_object* v_x_121_){
_start:
{
uint8_t v_x_26__boxed_122_; lean_object* v_res_123_; 
v_x_26__boxed_122_ = lean_unbox(v_x_121_);
v_res_123_ = l_Std_CloseableChannel_instToStringError___lam__0(v_x_26__boxed_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(lean_object* v_00_u03b1_130_, lean_object* v_x_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_apply_1(v_x_131_, lean_box(0));
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_155_; 
v_a_142_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_155_ == 0)
{
v___x_144_ = v___x_133_;
v_isShared_145_ = v_isSharedCheck_155_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_133_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_155_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
uint8_t v___x_146_; 
v___x_146_ = lean_unbox(v_a_142_);
lean_dec(v_a_142_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = ((lean_object*)(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0));
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_147_);
v___x_149_ = v___x_144_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = ((lean_object*)(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1));
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_151_);
v___x_153_ = v___x_144_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___boxed(lean_object* v_00_u03b1_156_, lean_object* v_x_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(v_00_u03b1_156_, v_x_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_unsigned_to_nat(0u);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_unsigned_to_nat(1u);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg___boxed(lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(v_x_165_);
lean_dec_ref(v_x_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx(lean_object* v_00_u03b1_167_, lean_object* v_x_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(v_x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___boxed(lean_object* v_00_u03b1_170_, lean_object* v_x_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx(v_00_u03b1_170_, v_x_171_);
lean_dec_ref(v_x_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(lean_object* v_t_173_, lean_object* v_k_174_){
_start:
{
if (lean_obj_tag(v_t_173_) == 0)
{
lean_object* v_promise_175_; lean_object* v___x_176_; 
v_promise_175_ = lean_ctor_get(v_t_173_, 0);
lean_inc(v_promise_175_);
lean_dec_ref_known(v_t_173_, 1);
v___x_176_ = lean_apply_1(v_k_174_, v_promise_175_);
return v___x_176_;
}
else
{
lean_object* v_finished_177_; lean_object* v___x_178_; 
v_finished_177_ = lean_ctor_get(v_t_173_, 0);
lean_inc_ref(v_finished_177_);
lean_dec_ref_known(v_t_173_, 1);
v___x_178_ = lean_apply_1(v_k_174_, v_finished_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(lean_object* v_00_u03b1_179_, lean_object* v_motive_180_, lean_object* v_ctorIdx_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_k_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_182_, v_k_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___boxed(lean_object* v_00_u03b1_186_, lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(v_00_u03b1_186_, v_motive_187_, v_ctorIdx_188_, v_t_189_, v_h_190_, v_k_191_);
lean_dec(v_ctorIdx_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim___redArg(lean_object* v_t_193_, lean_object* v_normal_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_193_, v_normal_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim(lean_object* v_00_u03b1_196_, lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_normal_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_198_, v_normal_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim___redArg(lean_object* v_t_202_, lean_object* v_select_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_202_, v_select_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim(lean_object* v_00_u03b1_205_, lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_select_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_207_, v_select_209_);
return v___x_210_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(lean_object* v_x_211_, lean_object* v_w_212_, lean_object* v_lose_213_){
_start:
{
lean_object* v_finished_215_; lean_object* v_promise_216_; lean_object* v___x_217_; uint8_t v___y_219_; uint8_t v___x_227_; 
v_finished_215_ = lean_ctor_get(v_w_212_, 0);
v_promise_216_ = lean_ctor_get(v_w_212_, 1);
v___x_217_ = lean_st_ref_take(v_finished_215_);
v___x_227_ = lean_unbox(v___x_217_);
lean_dec(v___x_217_);
if (v___x_227_ == 0)
{
uint8_t v___x_228_; 
v___x_228_ = 1;
v___y_219_ = v___x_228_;
goto v___jp_218_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = 0;
v___y_219_ = v___x_229_;
goto v___jp_218_;
}
v___jp_218_:
{
uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = 1;
v___x_221_ = lean_box(v___x_220_);
v___x_222_ = lean_st_ref_put(v_finished_215_, v___x_221_);
if (v___y_219_ == 0)
{
lean_object* v___x_223_; uint8_t v___x_224_; 
lean_dec(v_x_211_);
v___x_223_ = lean_apply_1(v_lose_213_, lean_box(0));
v___x_224_ = lean_unbox(v___x_223_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v_lose_213_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_x_211_);
v___x_226_ = lean_io_promise_resolve(v___x_225_, v_promise_216_);
return v___y_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg___boxed(lean_object* v_x_230_, lean_object* v_w_231_, lean_object* v_lose_232_, lean_object* v___y_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_230_, v_w_231_, v_lose_232_);
lean_dec_ref(v_w_231_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(lean_object* v_00_u03b1_236_, lean_object* v_x_237_, lean_object* v_w_238_, lean_object* v_lose_239_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_237_, v_w_238_, v_lose_239_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___boxed(lean_object* v_00_u03b1_242_, lean_object* v_x_243_, lean_object* v_w_244_, lean_object* v_lose_245_, lean_object* v___y_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(v_00_u03b1_242_, v_x_243_, v_w_244_, v_lose_245_);
lean_dec_ref(v_w_244_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(uint8_t v___x_249_){
_start:
{
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0___boxed(lean_object* v___x_251_, lean_object* v___y_252_){
_start:
{
uint8_t v___x_400__boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v___x_400__boxed_253_ = lean_unbox(v___x_251_);
v_res_254_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(v___x_400__boxed_253_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(lean_object* v_c_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_c_259_) == 0)
{
lean_object* v_promise_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_promise_262_ = lean_ctor_get(v_c_259_, 0);
v___x_263_ = lean_io_promise_resolve(v_x_260_, v_promise_262_);
v___x_264_ = 1;
return v___x_264_;
}
else
{
lean_object* v_finished_265_; lean_object* v_lose_266_; uint8_t v___x_267_; 
v_finished_265_ = lean_ctor_get(v_c_259_, 0);
v_lose_266_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0));
v___x_267_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_260_, v_finished_265_, v_lose_266_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___boxed(lean_object* v_c_268_, lean_object* v_x_269_, lean_object* v_a_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_c_268_, v_x_269_);
lean_dec_ref(v_c_268_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(lean_object* v_00_u03b1_273_, lean_object* v_c_274_, lean_object* v_x_275_){
_start:
{
uint8_t v___x_277_; 
v___x_277_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_c_274_, v_x_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___boxed(lean_object* v_00_u03b1_278_, lean_object* v_c_279_, lean_object* v_x_280_, lean_object* v_a_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(v_00_u03b1_278_, v_c_279_, v_x_280_);
lean_dec_ref(v_c_279_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Std_Queue_empty(lean_box(0));
return v___x_284_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = 0;
v___x_286_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_287_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*2, v___x_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg(){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1);
v___x_290_ = l_Std_Mutex_new___redArg(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___boxed(lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(lean_object* v_00_u03b1_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___boxed(lean_object* v_00_u03b1_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(v_00_u03b1_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(lean_object* v_mutex_299_, lean_object* v_k_300_){
_start:
{
lean_object* v_ref_302_; lean_object* v_mutex_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_ref_302_ = lean_ctor_get(v_mutex_299_, 0);
lean_inc(v_ref_302_);
v_mutex_303_ = lean_ctor_get(v_mutex_299_, 1);
lean_inc(v_mutex_303_);
lean_dec_ref(v_mutex_299_);
v___x_304_ = lean_io_basemutex_lock(v_mutex_303_);
v___x_305_ = lean_apply_2(v_k_300_, v_ref_302_, lean_box(0));
v___x_306_ = lean_io_basemutex_unlock(v_mutex_303_);
lean_dec(v_mutex_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg___boxed(lean_object* v_mutex_307_, lean_object* v_k_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_307_, v_k_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_mutex_313_, lean_object* v_k_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_313_, v_k_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___boxed(lean_object* v_00_u03b1_317_, lean_object* v_00_u03b2_318_, lean_object* v_mutex_319_, lean_object* v_k_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(v_00_u03b1_317_, v_00_u03b2_318_, v_mutex_319_, v_k_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(lean_object* v_v_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_values_327_; lean_object* v_consumers_328_; uint8_t v_closed_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_356_; 
v___x_326_ = lean_st_ref_get(v___y_324_);
v_values_327_ = lean_ctor_get(v___x_326_, 0);
v_consumers_328_ = lean_ctor_get(v___x_326_, 1);
v_closed_329_ = lean_ctor_get_uint8(v___x_326_, sizeof(void*)*2);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_356_ == 0)
{
v___x_331_ = v___x_326_;
v_isShared_332_ = v_isSharedCheck_356_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_consumers_328_);
lean_inc(v_values_327_);
lean_dec(v___x_326_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_356_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(0);
lean_inc_ref(v_consumers_328_);
v___x_334_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_328_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_consumers_328_);
v_val_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_350_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_350_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_val_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_350_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_fst_339_; lean_object* v_snd_340_; lean_object* v___x_342_; 
v_fst_339_ = lean_ctor_get(v_val_335_, 0);
lean_inc(v_fst_339_);
v_snd_340_ = lean_ctor_get(v_val_335_, 1);
lean_inc(v_snd_340_);
lean_dec(v_val_335_);
lean_inc(v_v_323_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v_v_323_);
v___x_342_ = v___x_337_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_v_323_);
v___x_342_ = v_reuseFailAlloc_349_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
uint8_t v___x_343_; lean_object* v___x_345_; 
v___x_343_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_339_, v___x_342_);
lean_dec(v_fst_339_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v_snd_340_);
v___x_345_ = v___x_331_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_values_327_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_snd_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_348_, sizeof(void*)*2, v_closed_329_);
v___x_345_ = v_reuseFailAlloc_348_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; 
v___x_346_ = lean_st_ref_swap(v___y_324_, v___x_345_);
lean_dec(v___x_346_);
if (v___x_343_ == 0)
{
goto _start;
}
else
{
lean_dec(v_v_323_);
return v___x_333_;
}
}
}
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_353_; 
lean_dec(v___x_334_);
v___x_351_ = l_Std_Queue_enqueue___redArg(v_v_323_, v_values_327_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_351_);
v___x_353_ = v___x_331_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_consumers_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*2, v_closed_329_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = lean_st_ref_swap(v___y_324_, v___x_353_);
lean_dec(v___x_354_);
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg___boxed(lean_object* v_v_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_357_, v___y_358_);
lean_dec(v___y_358_);
return v_res_360_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(lean_object* v_v_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; uint8_t v_closed_365_; 
v___x_364_ = lean_st_ref_get(v___y_362_);
v_closed_365_ = lean_ctor_get_uint8(v___x_364_, sizeof(void*)*2);
lean_dec(v___x_364_);
if (v_closed_365_ == 0)
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_361_, v___y_362_);
v___x_367_ = 1;
return v___x_367_;
}
else
{
uint8_t v___x_368_; 
lean_dec(v_v_361_);
v___x_368_ = 0;
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed(lean_object* v_v_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(v_v_369_, v___y_370_);
lean_dec(v___y_370_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(lean_object* v_ch_374_, lean_object* v_v_375_){
_start:
{
lean_object* v___f_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___f_377_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_377_, 0, v_v_375_);
v___x_378_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_374_, v___f_377_);
v___x_379_ = lean_unbox(v___x_378_);
lean_dec(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___boxed(lean_object* v_ch_380_, lean_object* v_v_381_, lean_object* v_a_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_380_, v_v_381_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(lean_object* v_00_u03b1_385_, lean_object* v_ch_386_, lean_object* v_v_387_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_386_, v_v_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___boxed(lean_object* v_00_u03b1_390_, lean_object* v_ch_391_, lean_object* v_v_392_, lean_object* v_a_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(v_00_u03b1_390_, v_ch_391_, v_v_392_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(lean_object* v_00_u03b1_396_, lean_object* v_v_397_, lean_object* v_inst_398_, lean_object* v_a_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_397_, v___y_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_403_, lean_object* v_v_404_, lean_object* v_inst_405_, lean_object* v_a_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(v_00_u03b1_403_, v_v_404_, v_inst_405_, v_a_406_, v___y_407_);
lean_dec(v___y_407_);
return v_res_409_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
v___x_414_ = lean_task_pure(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
v___x_418_ = lean_task_pure(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(lean_object* v_ch_419_, lean_object* v_v_420_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_419_, v_v_420_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_423_;
}
else
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___boxed(lean_object* v_ch_425_, lean_object* v_v_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_425_, v_v_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(lean_object* v_00_u03b1_429_, lean_object* v_ch_430_, lean_object* v_v_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_430_, v_v_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___boxed(lean_object* v_00_u03b1_434_, lean_object* v_ch_435_, lean_object* v_v_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(v_00_u03b1_434_, v_ch_435_, v_v_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(lean_object* v_mutex_439_, lean_object* v_k_440_){
_start:
{
lean_object* v_ref_442_; lean_object* v_mutex_443_; lean_object* v___x_444_; lean_object* v_r_445_; 
v_ref_442_ = lean_ctor_get(v_mutex_439_, 0);
lean_inc(v_ref_442_);
v_mutex_443_ = lean_ctor_get(v_mutex_439_, 1);
lean_inc(v_mutex_443_);
lean_dec_ref(v_mutex_439_);
v___x_444_ = lean_io_basemutex_lock(v_mutex_443_);
v_r_445_ = lean_apply_2(v_k_440_, v_ref_442_, lean_box(0));
if (lean_obj_tag(v_r_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
v_a_446_ = lean_ctor_get(v_r_445_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_r_445_);
if (v_isSharedCheck_454_ == 0)
{
v___x_448_ = v_r_445_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v_r_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_io_basemutex_unlock(v_mutex_443_);
lean_dec(v_mutex_443_);
if (v_isShared_449_ == 0)
{
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_446_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_463_; 
v_a_455_ = lean_ctor_get(v_r_445_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_r_445_);
if (v_isSharedCheck_463_ == 0)
{
v___x_457_ = v_r_445_;
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v_r_445_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_io_basemutex_unlock(v_mutex_443_);
lean_dec(v_mutex_443_);
if (v_isShared_458_ == 0)
{
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_455_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg___boxed(lean_object* v_mutex_464_, lean_object* v_k_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_464_, v_k_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(lean_object* v_00_u03b1_468_, lean_object* v_00_u03b2_469_, lean_object* v_mutex_470_, lean_object* v_k_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_470_, v_k_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___boxed(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_mutex_476_, lean_object* v_k_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(v_00_u03b1_474_, v_00_u03b2_475_, v_mutex_476_, v_k_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(lean_object* v_as_480_, size_t v_sz_481_, size_t v_i_482_, lean_object* v_b_483_){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = lean_usize_dec_lt(v_i_482_, v_sz_481_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_b_483_);
return v___x_486_;
}
else
{
lean_object* v_a_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; size_t v___x_491_; size_t v___x_492_; 
v_a_487_ = lean_array_uget_borrowed(v_as_480_, v_i_482_);
v___x_488_ = lean_box(0);
v___x_489_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_487_, v___x_488_);
v___x_490_ = lean_box(0);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_482_, v___x_491_);
v_i_482_ = v___x_492_;
v_b_483_ = v___x_490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg___boxed(lean_object* v_as_494_, lean_object* v_sz_495_, lean_object* v_i_496_, lean_object* v_b_497_, lean_object* v___y_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_495_);
lean_dec(v_sz_495_);
v_i_boxed_500_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_494_, v_sz_boxed_499_, v_i_boxed_500_, v_b_497_);
lean_dec_ref(v_as_494_);
return v_res_501_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_Queue_empty(lean_box(0));
return v___x_502_;
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
v___x_520_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
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
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(lean_object* v_ch_581_){
_start:
{
lean_object* v___f_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___f_583_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0));
v___x_584_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_581_, v___f_583_);
v___x_585_ = lean_unbox(v___x_584_);
lean_dec(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___boxed(lean_object* v_ch_586_, lean_object* v_a_587_){
_start:
{
uint8_t v_res_588_; lean_object* v_r_589_; 
v_res_588_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_586_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(lean_object* v_00_u03b1_590_, lean_object* v_ch_591_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___boxed(lean_object* v_00_u03b1_594_, lean_object* v_ch_595_, lean_object* v_a_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(v_00_u03b1_594_, v_ch_595_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_599_, lean_object* v_fst_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_toPure_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_toPure_602_ = lean_ctor_get(v_toApplicative_599_, 1);
lean_inc(v_toPure_602_);
lean_dec_ref(v_toApplicative_599_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v_fst_600_);
v___x_604_ = lean_apply_2(v_toPure_602_, lean_box(0), v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_605_, lean_object* v_a_606_, lean_object* v_inst_607_, lean_object* v_toBind_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_values_610_; lean_object* v_consumers_611_; uint8_t v_closed_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_630_; 
v_values_610_ = lean_ctor_get(v_a_609_, 0);
v_consumers_611_ = lean_ctor_get(v_a_609_, 1);
v_closed_612_ = lean_ctor_get_uint8(v_a_609_, sizeof(void*)*2);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_609_);
if (v_isSharedCheck_630_ == 0)
{
v___x_614_ = v_a_609_;
v_isShared_615_ = v_isSharedCheck_630_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_consumers_611_);
lean_inc(v_values_610_);
lean_dec(v_a_609_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_630_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_Queue_dequeue_x3f___redArg(v_values_610_);
if (lean_obj_tag(v___x_616_) == 1)
{
lean_object* v_val_617_; lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___f_620_; lean_object* v___x_622_; 
v_val_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v___x_616_, 1);
v_fst_618_ = lean_ctor_get(v_val_617_, 0);
lean_inc(v_fst_618_);
v_snd_619_ = lean_ctor_get(v_val_617_, 1);
lean_inc(v_snd_619_);
lean_dec(v_val_617_);
v___f_620_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_620_, 0, v_toApplicative_605_);
lean_closure_set(v___f_620_, 1, v_fst_618_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v_snd_619_);
v___x_622_ = v___x_614_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_snd_619_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_consumers_611_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*2, v_closed_612_);
v___x_622_ = v_reuseFailAlloc_626_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_inc(v_a_606_);
v___x_623_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_623_, 0, lean_box(0));
lean_closure_set(v___x_623_, 1, lean_box(0));
lean_closure_set(v___x_623_, 2, v_a_606_);
lean_closure_set(v___x_623_, 3, v___x_622_);
v___x_624_ = lean_apply_2(v_inst_607_, lean_box(0), v___x_623_);
v___x_625_ = lean_apply_4(v_toBind_608_, lean_box(0), lean_box(0), v___x_624_, v___f_620_);
return v___x_625_;
}
}
else
{
lean_object* v_toPure_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v___x_616_);
lean_del_object(v___x_614_);
lean_dec_ref(v_consumers_611_);
lean_dec(v_toBind_608_);
lean_dec(v_inst_607_);
v_toPure_627_ = lean_ctor_get(v_toApplicative_605_, 1);
lean_inc(v_toPure_627_);
lean_dec_ref(v_toApplicative_605_);
v___x_628_ = lean_box(0);
v___x_629_ = lean_apply_2(v_toPure_627_, lean_box(0), v___x_628_);
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_631_, lean_object* v_a_632_, lean_object* v_inst_633_, lean_object* v_toBind_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(v_toApplicative_631_, v_a_632_, v_inst_633_, v_toBind_634_, v_a_635_);
lean_dec(v_a_632_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_toApplicative_640_; lean_object* v_toBind_641_; lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_toApplicative_640_ = lean_ctor_get(v_inst_637_, 0);
lean_inc_ref(v_toApplicative_640_);
v_toBind_641_ = lean_ctor_get(v_inst_637_, 1);
lean_inc_n(v_toBind_641_, 2);
lean_dec_ref(v_inst_637_);
lean_inc(v_inst_638_);
lean_inc_n(v_a_639_, 2);
v___f_642_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_642_, 0, v_toApplicative_640_);
lean_closure_set(v___f_642_, 1, v_a_639_);
lean_closure_set(v___f_642_, 2, v_inst_638_);
lean_closure_set(v___f_642_, 3, v_toBind_641_);
v___x_643_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_643_, 0, lean_box(0));
lean_closure_set(v___x_643_, 1, lean_box(0));
lean_closure_set(v___x_643_, 2, v_a_639_);
v___x_644_ = lean_apply_2(v_inst_638_, lean_box(0), v___x_643_);
v___x_645_ = lean_apply_4(v_toBind_641_, lean_box(0), lean_box(0), v___x_644_, v___f_642_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_646_, v_inst_647_, v_a_648_);
lean_dec(v_a_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(lean_object* v_m_650_, lean_object* v_00_u03b1_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_652_, v_inst_653_, v_a_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___boxed(lean_object* v_m_656_, lean_object* v_00_u03b1_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(v_m_656_, v_00_u03b1_657_, v_inst_658_, v_inst_659_, v_a_660_);
lean_dec(v_a_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; lean_object* v_values_665_; lean_object* v_consumers_666_; uint8_t v_closed_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_687_; 
v___x_664_ = lean_st_ref_get(v_a_662_);
v_values_665_ = lean_ctor_get(v___x_664_, 0);
v_consumers_666_ = lean_ctor_get(v___x_664_, 1);
v_closed_667_ = lean_ctor_get_uint8(v___x_664_, sizeof(void*)*2);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_687_ == 0)
{
v___x_669_ = v___x_664_;
v_isShared_670_ = v_isSharedCheck_687_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_consumers_666_);
lean_inc(v_values_665_);
lean_dec(v___x_664_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_687_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_Queue_dequeue_x3f___redArg(v_values_665_);
if (lean_obj_tag(v___x_671_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_685_; 
v_val_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_685_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_685_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_val_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_685_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_fst_676_; lean_object* v_snd_677_; lean_object* v___x_679_; 
v_fst_676_ = lean_ctor_get(v_val_672_, 0);
lean_inc(v_fst_676_);
v_snd_677_ = lean_ctor_get(v_val_672_, 1);
lean_inc(v_snd_677_);
lean_dec(v_val_672_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v_snd_677_);
v___x_679_ = v___x_669_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_snd_677_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_consumers_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_684_, sizeof(void*)*2, v_closed_667_);
v___x_679_ = v_reuseFailAlloc_684_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_st_ref_swap(v_a_662_, v___x_679_);
lean_dec(v___x_680_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v_fst_676_);
v___x_682_ = v___x_674_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_fst_676_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v___x_686_; 
lean_dec(v___x_671_);
lean_del_object(v___x_669_);
lean_dec_ref(v_consumers_666_);
v___x_686_ = lean_box(0);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_688_);
lean_dec(v_a_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(lean_object* v_00_u03b1_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_695_, lean_object* v_a_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(v_00_u03b1_695_, v_a_696_);
lean_dec(v_a_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(lean_object* v_ch_700_){
_start:
{
lean_object* v___f_702_; lean_object* v___x_703_; 
v___f_702_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0));
v___x_703_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_700_, v___f_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___boxed(lean_object* v_ch_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(lean_object* v_00_u03b1_707_, lean_object* v_ch_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___boxed(lean_object* v_00_u03b1_711_, lean_object* v_ch_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(v_00_u03b1_711_, v_ch_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(lean_object* v_x_715_){
_start:
{
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_box(0);
return v___x_716_;
}
else
{
lean_object* v_val_717_; 
v_val_717_ = lean_ctor_get(v_x_715_, 0);
lean_inc(v_val_717_);
return v_val_717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed(lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(v_x_718_);
lean_dec(v_x_718_);
return v_res_719_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_box(0);
v___x_721_ = lean_task_pure(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(lean_object* v___f_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v___y_723_);
if (lean_obj_tag(v___x_725_) == 1)
{
lean_object* v___x_726_; 
lean_dec_ref(v___f_722_);
v___x_726_ = lean_task_pure(v___x_725_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; uint8_t v_closed_728_; 
lean_dec(v___x_725_);
v___x_727_ = lean_st_ref_get(v___y_723_);
v_closed_728_ = lean_ctor_get_uint8(v___x_727_, sizeof(void*)*2);
lean_dec(v___x_727_);
if (v_closed_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_values_731_; lean_object* v_consumers_732_; uint8_t v_closed_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_747_; 
v___x_729_ = lean_io_promise_new();
v___x_730_ = lean_st_ref_take(v___y_723_);
v_values_731_ = lean_ctor_get(v___x_730_, 0);
v_consumers_732_ = lean_ctor_get(v___x_730_, 1);
v_closed_733_ = lean_ctor_get_uint8(v___x_730_, sizeof(void*)*2);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_747_ == 0)
{
v___x_735_ = v___x_730_;
v_isShared_736_ = v_isSharedCheck_747_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_consumers_732_);
lean_inc(v_values_731_);
lean_dec(v___x_730_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_747_;
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
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_values_731_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, sizeof(void*)*2, v_closed_733_);
v___x_740_ = v_reuseFailAlloc_746_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_741_ = lean_st_ref_put(v___y_723_, v___x_740_);
v___x_742_ = 1;
v___x_743_ = lean_io_promise_result_opt(v___x_729_);
lean_dec(v___x_729_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_task_map(v___f_722_, v___x_743_, v___x_744_, v___x_742_);
return v___x_745_;
}
}
}
else
{
lean_object* v___x_748_; 
lean_dec_ref(v___f_722_);
v___x_748_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed(lean_object* v___f_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(v___f_749_, v___y_750_);
lean_dec(v___y_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(lean_object* v_ch_756_){
_start:
{
lean_object* v___f_758_; lean_object* v___x_759_; 
v___f_758_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1));
v___x_759_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_756_, v___f_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___boxed(lean_object* v_ch_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(lean_object* v_00_u03b1_763_, lean_object* v_ch_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_764_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___boxed(lean_object* v_00_u03b1_767_, lean_object* v_ch_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(v_00_u03b1_767_, v_ch_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_771_, lean_object* v_a_772_){
_start:
{
uint8_t v___y_774_; lean_object* v_values_778_; uint8_t v_closed_779_; uint8_t v___x_780_; 
v_values_778_ = lean_ctor_get(v_a_772_, 0);
v_closed_779_ = lean_ctor_get_uint8(v_a_772_, sizeof(void*)*2);
v___x_780_ = l_Std_Queue_isEmpty___redArg(v_values_778_);
if (v___x_780_ == 0)
{
uint8_t v___x_781_; 
v___x_781_ = 1;
v___y_774_ = v___x_781_;
goto v___jp_773_;
}
else
{
v___y_774_ = v_closed_779_;
goto v___jp_773_;
}
v___jp_773_:
{
lean_object* v_toPure_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_toPure_775_ = lean_ctor_get(v_toApplicative_771_, 1);
lean_inc(v_toPure_775_);
lean_dec_ref(v_toApplicative_771_);
v___x_776_ = lean_box(v___y_774_);
v___x_777_ = lean_apply_2(v_toPure_775_, lean_box(0), v___x_776_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(v_toApplicative_782_, v_a_783_);
lean_dec_ref(v_a_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_toApplicative_788_; lean_object* v_toBind_789_; lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_toApplicative_788_ = lean_ctor_get(v_inst_785_, 0);
lean_inc_ref(v_toApplicative_788_);
v_toBind_789_ = lean_ctor_get(v_inst_785_, 1);
lean_inc(v_toBind_789_);
lean_dec_ref(v_inst_785_);
v___f_790_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_790_, 0, v_toApplicative_788_);
lean_inc(v_a_787_);
v___x_791_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_791_, 0, lean_box(0));
lean_closure_set(v___x_791_, 1, lean_box(0));
lean_closure_set(v___x_791_, 2, v_a_787_);
v___x_792_ = lean_apply_2(v_inst_786_, lean_box(0), v___x_791_);
v___x_793_ = lean_apply_4(v_toBind_789_, lean_box(0), lean_box(0), v___x_792_, v___f_790_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___boxed(lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(v_inst_794_, v_inst_795_, v_a_796_);
lean_dec(v_a_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(lean_object* v_m_798_, lean_object* v_00_u03b1_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_toApplicative_803_; lean_object* v_toBind_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_toApplicative_803_ = lean_ctor_get(v_inst_800_, 0);
lean_inc_ref(v_toApplicative_803_);
v_toBind_804_ = lean_ctor_get(v_inst_800_, 1);
lean_inc(v_toBind_804_);
lean_dec_ref(v_inst_800_);
v___f_805_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_805_, 0, v_toApplicative_803_);
lean_inc(v_a_802_);
v___x_806_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_806_, 0, lean_box(0));
lean_closure_set(v___x_806_, 1, lean_box(0));
lean_closure_set(v___x_806_, 2, v_a_802_);
v___x_807_ = lean_apply_2(v_inst_801_, lean_box(0), v___x_806_);
v___x_808_ = lean_apply_4(v_toBind_804_, lean_box(0), lean_box(0), v___x_807_, v___f_805_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___boxed(lean_object* v_m_809_, lean_object* v_00_u03b1_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(v_m_809_, v_00_u03b1_810_, v_inst_811_, v_inst_812_, v_a_813_);
lean_dec(v_a_813_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_fst_815_, lean_object* v_x_816_){
_start:
{
if (lean_obj_tag(v_x_816_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_fst_815_);
v_a_818_ = lean_ctor_get(v_x_816_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_x_816_);
if (v_isSharedCheck_826_ == 0)
{
v___x_820_ = v_x_816_;
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v_x_816_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_825_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; 
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
}
}
else
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_835_; 
v_isSharedCheck_835_ = !lean_is_exclusive(v_x_816_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v_x_816_, 0);
lean_dec(v_unused_836_);
v___x_828_ = v_x_816_;
v_isShared_829_ = v_isSharedCheck_835_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_x_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_835_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_830_, 0, v_fst_815_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_834_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_837_, lean_object* v_x_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(v_fst_837_, v_x_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_849_, lean_object* v_x_850_){
_start:
{
if (lean_obj_tag(v_x_850_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_a_852_ = lean_ctor_get(v_x_850_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_860_ == 0)
{
v___x_854_ = v_x_850_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v_x_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v_values_862_; lean_object* v_consumers_863_; uint8_t v_closed_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_882_; 
v_a_861_ = lean_ctor_get(v_x_850_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v_x_850_, 1);
v_values_862_ = lean_ctor_get(v_a_861_, 0);
v_consumers_863_ = lean_ctor_get(v_a_861_, 1);
v_closed_864_ = lean_ctor_get_uint8(v_a_861_, sizeof(void*)*2);
v_isSharedCheck_882_ = !lean_is_exclusive(v_a_861_);
if (v_isSharedCheck_882_ == 0)
{
v___x_866_ = v_a_861_;
v_isShared_867_ = v_isSharedCheck_882_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_consumers_863_);
lean_inc(v_values_862_);
lean_dec(v_a_861_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_882_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_Queue_dequeue_x3f___redArg(v_values_862_);
if (lean_obj_tag(v___x_868_) == 1)
{
lean_object* v_val_869_; lean_object* v_fst_870_; lean_object* v_snd_871_; lean_object* v___x_873_; 
v_val_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v___x_868_, 1);
v_fst_870_ = lean_ctor_get(v_val_869_, 0);
lean_inc(v_fst_870_);
v_snd_871_ = lean_ctor_get(v_val_869_, 1);
lean_inc(v_snd_871_);
lean_dec(v_val_869_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_snd_871_);
v___x_873_ = v___x_866_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_snd_871_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_consumers_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_880_, sizeof(void*)*2, v_closed_864_);
v___x_873_ = v_reuseFailAlloc_880_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; 
v___x_874_ = lean_st_ref_swap(v_a_849_, v___x_873_);
lean_dec(v___x_874_);
v___f_875_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_875_, 0, v_fst_870_);
v___x_876_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = 0;
v___x_879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_877_, v___x_878_, v___x_876_, v___f_875_);
return v___x_879_;
}
}
else
{
lean_object* v___x_881_; 
lean_dec(v___x_868_);
lean_del_object(v___x_866_);
lean_dec_ref(v_consumers_863_);
v___x_881_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_883_, lean_object* v_x_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_883_, v_x_884_);
lean_dec(v_a_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(lean_object* v_a_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; 
v___x_889_ = lean_st_ref_get(v_a_887_);
lean_inc(v_a_887_);
v___f_890_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_890_, 0, v_a_887_);
v___x_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = 0;
v___x_895_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_893_, v___x_894_, v___x_892_, v___f_890_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_896_);
lean_dec(v_a_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_object* v_00_u03b1_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_903_, lean_object* v_a_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(v_00_u03b1_903_, v_a_904_);
lean_dec(v_a_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_promise_907_, lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_a_910_ = lean_ctor_get(v_x_908_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_908_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v_x_908_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v_x_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_917_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_io_promise_resolve(v_x_908_, v_promise_907_);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_promise_922_, lean_object* v_x_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_922_, v_x_923_);
lean_dec(v_promise_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_926_, lean_object* v___y_927_, lean_object* v___f_928_, lean_object* v_x_929_){
_start:
{
if (lean_obj_tag(v_x_929_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v___f_928_);
lean_dec_ref(v_lose_926_);
v_a_931_ = lean_ctor_get(v_x_929_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v_x_929_);
if (v_isSharedCheck_939_ == 0)
{
v___x_933_ = v_x_929_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v_x_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
}
else
{
lean_object* v_a_940_; uint8_t v___x_941_; 
v_a_940_ = lean_ctor_get(v_x_929_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v_x_929_, 1);
v___x_941_ = lean_unbox(v_a_940_);
lean_dec(v_a_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec_ref(v___f_928_);
lean_inc(v___y_927_);
v___x_942_ = lean_apply_2(v_lose_926_, v___y_927_, lean_box(0));
return v___x_942_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; 
lean_dec_ref(v_lose_926_);
v___x_943_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_927_);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = 0;
v___x_946_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_944_, v___x_945_, v___x_943_, v___f_928_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_947_, lean_object* v___y_948_, lean_object* v___f_949_, lean_object* v_x_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_947_, v___y_948_, v___f_949_, v_x_950_);
lean_dec(v___y_948_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object* v_w_953_, lean_object* v_lose_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_finished_957_; lean_object* v_promise_958_; lean_object* v___x_959_; lean_object* v___f_960_; lean_object* v___f_961_; uint8_t v___y_963_; uint8_t v___x_973_; 
v_finished_957_ = lean_ctor_get(v_w_953_, 0);
lean_inc(v_finished_957_);
v_promise_958_ = lean_ctor_get(v_w_953_, 1);
lean_inc(v_promise_958_);
lean_dec_ref(v_w_953_);
v___x_959_ = lean_st_ref_take(v_finished_957_);
v___f_960_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_960_, 0, v_promise_958_);
lean_inc(v___y_955_);
v___f_961_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_961_, 0, v_lose_954_);
lean_closure_set(v___f_961_, 1, v___y_955_);
lean_closure_set(v___f_961_, 2, v___f_960_);
v___x_973_ = lean_unbox(v___x_959_);
lean_dec(v___x_959_);
if (v___x_973_ == 0)
{
uint8_t v___x_974_; 
v___x_974_ = 1;
v___y_963_ = v___x_974_;
goto v___jp_962_;
}
else
{
uint8_t v___x_975_; 
v___x_975_ = 0;
v___y_963_ = v___x_975_;
goto v___jp_962_;
}
v___jp_962_:
{
uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; 
v___x_964_ = 1;
v___x_965_ = lean_box(v___x_964_);
v___x_966_ = lean_st_ref_put(v_finished_957_, v___x_965_);
lean_dec(v_finished_957_);
v___x_967_ = lean_box(v___y_963_);
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = 0;
v___x_972_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_970_, v___x_971_, v___x_969_, v___f_961_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object* v_w_976_, lean_object* v_lose_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_976_, v_lose_977_, v___y_978_);
lean_dec(v___y_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object* v_00_u03b1_981_, lean_object* v_w_982_, lean_object* v_lose_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_982_, v_lose_983_, v___y_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_987_, lean_object* v_w_988_, lean_object* v_lose_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(v_00_u03b1_987_, v_w_988_, v_lose_989_, v___y_990_);
lean_dec(v___y_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_993_, lean_object* v_x_994_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_io_basemutex_unlock(v_mutex_993_);
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_999_, lean_object* v_x_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(v_mutex_999_, v_x_1000_);
lean_dec(v_x_1000_);
lean_dec(v_mutex_999_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_1003_, lean_object* v_ref_1004_, lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_ref_1004_);
lean_dec_ref(v_k_1003_);
v_a_1007_ = lean_ctor_get(v_x_1005_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_x_1005_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1009_ = v_x_1005_;
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v_x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
}
else
{
lean_object* v___x_1016_; 
lean_dec_ref_known(v_x_1005_, 1);
v___x_1016_ = lean_apply_2(v_k_1003_, v_ref_1004_, lean_box(0));
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_1017_, lean_object* v_ref_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_k_1017_, v_ref_1018_, v_x_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_1022_, lean_object* v___f_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1025_ = lean_io_basemutex_lock(v_mutex_1022_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = 0;
v___x_1030_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1028_, v___x_1029_, v___x_1027_, v___f_1023_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_1031_, lean_object* v___f_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_mutex_1031_, v___f_1032_);
lean_dec(v_mutex_1031_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_1035_){
_start:
{
if (lean_obj_tag(v___y_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1036_ = lean_ctor_get(v___y_1035_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___y_1035_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___y_1035_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___y_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
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
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
v_a_1044_ = lean_ctor_get(v___y_1035_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___y_1035_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1046_ = v___y_1035_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___y_1035_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v_fst_1048_; lean_object* v___x_1050_; 
v_fst_1048_ = lean_ctor_get(v_a_1044_, 0);
lean_inc(v_fst_1048_);
lean_dec(v_a_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v_fst_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_fst_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(lean_object* v_mutex_1054_, lean_object* v_k_1055_){
_start:
{
lean_object* v_ref_1057_; lean_object* v_mutex_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___y_1066_; 
v_ref_1057_ = lean_ctor_get(v_mutex_1054_, 0);
lean_inc(v_ref_1057_);
v_mutex_1058_ = lean_ctor_get(v_mutex_1054_, 1);
lean_inc_n(v_mutex_1058_, 2);
lean_dec_ref(v_mutex_1054_);
v___f_1059_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1059_, 0, v_mutex_1058_);
v___f_1060_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1060_, 0, v_k_1055_);
lean_closure_set(v___f_1060_, 1, v_ref_1057_);
v___f_1061_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1061_, 0, v_mutex_1058_);
lean_closure_set(v___f_1061_, 1, v___f_1060_);
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = 0;
v___x_1064_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1061_, v___f_1059_, v___x_1062_, v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1068_; 
v_a_1068_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1064_, 1);
if (lean_obj_tag(v_a_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v_a_1068_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_a_1068_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v_a_1068_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v_a_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
v___y_1066_ = v___x_1074_;
goto v___jp_1065_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1085_; 
v_a_1077_ = lean_ctor_get(v_a_1068_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_a_1068_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1079_ = v_a_1068_;
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v_a_1068_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_fst_1081_; lean_object* v___x_1083_; 
v_fst_1081_ = lean_ctor_get(v_a_1077_, 0);
lean_inc(v_fst_1081_);
lean_dec(v_a_1077_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_fst_1081_);
v___x_1083_ = v___x_1079_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_fst_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
v___y_1066_ = v___x_1083_;
goto v___jp_1065_;
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1095_; 
v_a_1086_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1088_ = v___x_1064_;
v_isShared_1089_ = v_isSharedCheck_1095_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1064_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1095_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___f_1090_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0));
v___x_1091_ = lean_task_map(v___f_1090_, v_a_1086_, v___x_1062_, v___x_1063_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
v___jp_1065_:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___y_1066_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_1096_, lean_object* v_k_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1096_, v_k_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_object* v_00_u03b1_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_mutex_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1102_, v_k_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_mutex_1108_, lean_object* v_k_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(v_00_u03b1_1106_, v_00_u03b2_1107_, v_mutex_1108_, v_k_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1122_; 
v_a_1114_ = lean_ctor_get(v_x_1112_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1116_ = v_x_1112_;
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v_x_1112_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1132_; 
v_a_1123_ = lean_ctor_get(v_x_1112_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1125_ = v_x_1112_;
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v_x_1112_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_a_1123_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(lean_object* v_x_1136_){
_start:
{
uint8_t v___y_1139_; 
if (lean_obj_tag(v_x_1136_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v_a_1143_ = lean_ctor_get(v_x_1136_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_x_1136_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1145_ = v_x_1136_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v_x_1136_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
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
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v_values_1153_; uint8_t v_closed_1154_; uint8_t v___x_1155_; 
v_a_1152_ = lean_ctor_get(v_x_1136_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v_x_1136_, 1);
v_values_1153_ = lean_ctor_get(v_a_1152_, 0);
lean_inc_ref(v_values_1153_);
v_closed_1154_ = lean_ctor_get_uint8(v_a_1152_, sizeof(void*)*2);
lean_dec(v_a_1152_);
v___x_1155_ = l_Std_Queue_isEmpty___redArg(v_values_1153_);
lean_dec_ref(v_values_1153_);
if (v___x_1155_ == 0)
{
uint8_t v___x_1156_; 
v___x_1156_ = 1;
v___y_1139_ = v___x_1156_;
goto v___jp_1138_;
}
else
{
v___y_1139_ = v_closed_1154_;
goto v___jp_1138_;
}
}
v___jp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_box(v___y_1139_);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(lean_object* v_x_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(lean_object* v___x_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1160_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_1165_, v___y_1166_);
lean_dec(v___y_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(lean_object* v___y_1171_, lean_object* v_waiter_1172_, lean_object* v_x_1173_){
_start:
{
if (lean_obj_tag(v_x_1173_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_waiter_1172_);
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
lean_object* v_a_1184_; uint8_t v___x_1185_; 
v_a_1184_ = lean_ctor_get(v_x_1173_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v_x_1173_, 1);
v___x_1185_ = lean_unbox(v_a_1184_);
lean_dec(v_a_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v_values_1187_; lean_object* v_consumers_1188_; uint8_t v_closed_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1200_; 
v___x_1186_ = lean_st_ref_take(v___y_1171_);
v_values_1187_ = lean_ctor_get(v___x_1186_, 0);
v_consumers_1188_ = lean_ctor_get(v___x_1186_, 1);
v_closed_1189_ = lean_ctor_get_uint8(v___x_1186_, sizeof(void*)*2);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1191_ = v___x_1186_;
v_isShared_1192_ = v_isSharedCheck_1200_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_consumers_1188_);
lean_inc(v_values_1187_);
lean_dec(v___x_1186_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1200_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_waiter_1172_);
v___x_1194_ = l_Std_Queue_enqueue___redArg(v___x_1193_, v_consumers_1188_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___x_1194_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_values_1187_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1194_);
lean_ctor_set_uint8(v_reuseFailAlloc_1199_, sizeof(void*)*2, v_closed_1189_);
v___x_1196_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_st_ref_put(v___y_1171_, v___x_1196_);
v___x_1198_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_1198_;
}
}
}
else
{
lean_object* v_lose_1201_; lean_object* v___x_1202_; 
v_lose_1201_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0));
v___x_1202_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_waiter_1172_, v_lose_1201_, v___y_1171_);
return v___x_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(lean_object* v___y_1203_, lean_object* v_waiter_1204_, lean_object* v_x_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_1203_, v_waiter_1204_, v_x_1205_);
lean_dec(v___y_1203_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(lean_object* v___f_1208_, lean_object* v_waiter_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; 
v___x_1212_ = lean_st_ref_get(v___y_1210_);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = 0;
v___x_1217_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1215_, v___x_1216_, v___x_1214_, v___f_1208_);
lean_inc(v___y_1210_);
v___f_1218_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1218_, 0, v___y_1210_);
lean_closure_set(v___f_1218_, 1, v_waiter_1209_);
v___x_1219_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1215_, v___x_1216_, v___x_1217_, v___f_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(lean_object* v___f_1220_, lean_object* v_waiter_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v___f_1220_, v_waiter_1221_, v___y_1222_);
lean_dec(v___y_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(lean_object* v___f_1225_, lean_object* v_ch_1226_, lean_object* v_waiter_1227_){
_start:
{
lean_object* v___f_1229_; lean_object* v___x_1230_; 
v___f_1229_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1229_, 0, v___f_1225_);
lean_closure_set(v___f_1229_, 1, v_waiter_1227_);
v___x_1230_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_1226_, v___f_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(lean_object* v___f_1231_, lean_object* v_ch_1232_, lean_object* v_waiter_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_1231_, v_ch_1232_, v_waiter_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(lean_object* v___y_1240_, lean_object* v___f_1241_, lean_object* v_x_1242_){
_start:
{
if (lean_obj_tag(v_x_1242_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v___f_1241_);
v_a_1244_ = lean_ctor_get(v_x_1242_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_x_1242_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1246_ = v_x_1242_;
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v_x_1242_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
}
else
{
lean_object* v_a_1253_; uint8_t v___x_1254_; 
v_a_1253_ = lean_ctor_get(v_x_1242_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v_x_1242_, 1);
v___x_1254_ = lean_unbox(v_a_1253_);
lean_dec(v_a_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v___f_1241_);
v___x_1255_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_1255_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_1240_);
v___x_1257_ = lean_unsigned_to_nat(0u);
v___x_1258_ = 0;
v___x_1259_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1257_, v___x_1258_, v___x_1256_, v___f_1241_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(lean_object* v___y_1260_, lean_object* v___f_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_1260_, v___f_1261_, v_x_1262_);
lean_dec(v___y_1260_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(lean_object* v___f_1265_, lean_object* v___f_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___f_1275_; lean_object* v___x_1276_; 
v___x_1269_ = lean_st_ref_get(v___y_1267_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = 0;
v___x_1274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1272_, v___x_1273_, v___x_1271_, v___f_1265_);
lean_inc(v___y_1267_);
v___f_1275_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1275_, 0, v___y_1267_);
lean_closure_set(v___f_1275_, 1, v___f_1266_);
v___x_1276_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1272_, v___x_1273_, v___x_1274_, v___f_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(lean_object* v___f_1277_, lean_object* v___f_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_1277_, v___f_1278_, v___y_1279_);
lean_dec(v___y_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(lean_object* v_values_1282_, uint8_t v_closed_1283_, lean_object* v___y_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_values_1282_);
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
lean_object* v_a_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_a_1296_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1297_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1297_, 0, v_values_1282_);
lean_ctor_set(v___x_1297_, 1, v_a_1296_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*2, v_closed_1283_);
v___x_1298_ = lean_st_ref_swap(v___y_1284_, v___x_1297_);
lean_dec(v___x_1298_);
v___x_1299_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_1299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed(lean_object* v_values_1300_, lean_object* v_closed_1301_, lean_object* v___y_1302_, lean_object* v_x_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v_closed_boxed_1305_; lean_object* v_res_1306_; 
v_closed_boxed_1305_ = lean_unbox(v_closed_1301_);
v_res_1306_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(v_values_1300_, v_closed_boxed_1305_, v___y_1302_, v_x_1303_);
lean_dec(v___y_1302_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1307_) == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_x_1307_);
return v___x_1309_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1319_; 
v_a_1310_ = lean_ctor_get(v_x_1307_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_x_1307_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1312_ = v_x_1307_;
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v_x_1307_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = l_List_reverse___redArg(v_a_1310_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1314_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(v_x_1320_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_1323_, lean_object* v___x_1324_, lean_object* v_x_1325_){
_start:
{
if (lean_obj_tag(v_x_1325_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v___x_1324_);
lean_dec(v_a_1323_);
v_a_1327_ = lean_ctor_get(v_x_1325_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v_x_1325_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v_x_1325_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1352_; 
v_a_1336_ = lean_ctor_get(v_x_1325_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1338_ = v_x_1325_;
v_isShared_1339_ = v_isSharedCheck_1352_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v_x_1325_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1352_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v___x_1340_; 
v___x_1340_ = l_List_isEmpty___redArg(v_a_1323_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
lean_dec(v___x_1324_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_a_1336_);
lean_ctor_set(v___x_1341_, 1, v_a_1323_);
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
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
lean_dec(v_a_1323_);
v___x_1346_ = l_List_reverse___redArg(v_a_1336_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1324_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1347_);
v___x_1349_ = v___x_1338_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_1353_, lean_object* v___x_1354_, lean_object* v_x_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(v_a_1353_, v___x_1354_, v_x_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(lean_object* v_x_1358_){
_start:
{
uint8_t v___y_1361_; 
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_x_1358_);
return v___x_1365_;
}
else
{
lean_object* v_a_1366_; uint8_t v___x_1367_; 
v_a_1366_ = lean_ctor_get(v_x_1358_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v_x_1358_, 1);
v___x_1367_ = lean_unbox(v_a_1366_);
lean_dec(v_a_1366_);
if (v___x_1367_ == 0)
{
uint8_t v___x_1368_; 
v___x_1368_ = 1;
v___y_1361_ = v___x_1368_;
goto v___jp_1360_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = 0;
v___y_1361_ = v___x_1369_;
goto v___jp_1360_;
}
}
v___jp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_box(v___y_1361_);
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(lean_object* v_x_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_tail_1373_, lean_object* v_x_1374_, lean_object* v_head_1375_, lean_object* v_x_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_1373_, v_x_1374_, v_head_1375_, v_x_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_x_1386_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v_head_1390_; lean_object* v_tail_1391_; lean_object* v___f_1392_; lean_object* v_val_1394_; 
v_head_1390_ = lean_ctor_get(v_x_1385_, 0);
lean_inc_n(v_head_1390_, 2);
v_tail_1391_ = lean_ctor_get(v_x_1385_, 1);
lean_inc(v_tail_1391_);
lean_dec_ref_known(v_x_1385_, 2);
v___f_1392_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1392_, 0, v_tail_1391_);
lean_closure_set(v___f_1392_, 1, v_x_1386_);
lean_closure_set(v___f_1392_, 2, v_head_1390_);
if (lean_obj_tag(v_head_1390_) == 0)
{
lean_object* v___x_1398_; 
lean_dec_ref_known(v_head_1390_, 1);
v___x_1398_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_1394_ = v___x_1398_;
goto v___jp_1393_;
}
else
{
lean_object* v_finished_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1413_; 
v_finished_1399_ = lean_ctor_get(v_head_1390_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_head_1390_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1401_ = v_head_1390_;
v_isShared_1402_ = v_isSharedCheck_1413_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_finished_1399_);
lean_dec(v_head_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1413_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_finished_1403_; lean_object* v___x_1404_; lean_object* v___f_1405_; lean_object* v___x_1407_; 
v_finished_1403_ = lean_ctor_get(v_finished_1399_, 0);
lean_inc(v_finished_1403_);
lean_dec_ref(v_finished_1399_);
v___x_1404_ = lean_st_ref_get(v_finished_1403_);
lean_dec(v_finished_1403_);
v___f_1405_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1404_);
v___x_1407_ = v___x_1401_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1404_);
v___x_1407_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = 0;
v___x_1411_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1409_, v___x_1410_, v___x_1408_, v___f_1405_);
v_val_1394_ = v___x_1411_;
goto v___jp_1393_;
}
}
}
v___jp_1393_:
{
lean_object* v___x_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = 0;
v___x_1397_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1395_, v___x_1396_, v_val_1394_, v___f_1392_);
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object* v_tail_1414_, lean_object* v_x_1415_, lean_object* v_head_1416_, lean_object* v_x_1417_){
_start:
{
if (lean_obj_tag(v_x_1417_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v_head_1416_);
lean_dec(v_x_1415_);
lean_dec(v_tail_1414_);
v_a_1419_ = lean_ctor_get(v_x_1417_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1417_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1421_ = v_x_1417_;
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v_x_1417_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1428_; uint8_t v___x_1429_; 
v_a_1428_ = lean_ctor_get(v_x_1417_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v_x_1417_, 1);
v___x_1429_ = lean_unbox(v_a_1428_);
lean_dec(v_a_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
lean_dec_ref(v_head_1416_);
v___x_1430_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1414_, v_x_1415_);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_head_1416_);
lean_ctor_set(v___x_1431_, 1, v_x_1415_);
v___x_1432_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1414_, v___x_1431_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1433_, v_x_1434_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_1437_, lean_object* v___x_1438_, lean_object* v___f_1439_, lean_object* v_x_1440_){
_start:
{
if (lean_obj_tag(v_x_1440_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v___f_1439_);
lean_dec(v___x_1438_);
lean_dec(v_eList_1437_);
v_a_1442_ = lean_ctor_get(v_x_1440_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_x_1440_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1444_ = v_x_1440_;
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v_x_1440_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; 
v_a_1451_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v_x_1440_, 1);
lean_inc(v___x_1438_);
v___x_1452_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_1437_, v___x_1438_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = 0;
v___x_1455_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1453_, v___x_1454_, v___x_1452_, v___f_1439_);
v___f_1456_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1456_, 0, v_a_1451_);
lean_closure_set(v___f_1456_, 1, v___x_1438_);
v___x_1457_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1453_, v___x_1454_, v___x_1455_, v___f_1456_);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_1458_, lean_object* v___x_1459_, lean_object* v___f_1460_, lean_object* v_x_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v_eList_1458_, v___x_1459_, v___f_1460_, v_x_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object* v_q_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_eList_1468_; lean_object* v_dList_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___f_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; 
v_eList_1468_ = lean_ctor_get(v_q_1465_, 0);
lean_inc(v_eList_1468_);
v_dList_1469_ = lean_ctor_get(v_q_1465_, 1);
lean_inc(v_dList_1469_);
lean_dec_ref(v_q_1465_);
v___x_1470_ = lean_box(0);
v___x_1471_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_1469_, v___x_1470_);
v___f_1472_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = 0;
v___x_1475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1473_, v___x_1474_, v___x_1471_, v___f_1472_);
v___f_1476_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1476_, 0, v_eList_1468_);
lean_closure_set(v___f_1476_, 1, v___x_1470_);
lean_closure_set(v___f_1476_, 2, v___f_1472_);
v___x_1477_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1473_, v___x_1474_, v___x_1475_, v___f_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object* v_q_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1478_, v___y_1479_);
lean_dec(v___y_1479_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object* v___y_1482_, lean_object* v_x_1483_){
_start:
{
if (lean_obj_tag(v_x_1483_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1493_; 
v_a_1485_ = lean_ctor_get(v_x_1483_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_x_1483_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1487_ = v_x_1483_;
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v_x_1483_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
return v___x_1491_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v_values_1495_; lean_object* v_consumers_1496_; uint8_t v_closed_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___f_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; 
v_a_1494_ = lean_ctor_get(v_x_1483_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v_x_1483_, 1);
v_values_1495_ = lean_ctor_get(v_a_1494_, 0);
lean_inc_ref(v_values_1495_);
v_consumers_1496_ = lean_ctor_get(v_a_1494_, 1);
lean_inc_ref(v_consumers_1496_);
v_closed_1497_ = lean_ctor_get_uint8(v_a_1494_, sizeof(void*)*2);
lean_dec(v_a_1494_);
v___x_1498_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_1496_, v___y_1482_);
v___x_1499_ = lean_box(v_closed_1497_);
lean_inc(v___y_1482_);
v___f_1500_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1500_, 0, v_values_1495_);
lean_closure_set(v___f_1500_, 1, v___x_1499_);
lean_closure_set(v___f_1500_, 2, v___y_1482_);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = 0;
v___x_1503_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1501_, v___x_1502_, v___x_1498_, v___f_1500_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object* v___y_1504_, lean_object* v_x_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1504_, v_x_1505_);
lean_dec(v___y_1504_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___f_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; 
v___x_1510_ = lean_st_ref_get(v___y_1508_);
lean_inc(v___y_1508_);
v___f_1511_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1511_, 0, v___y_1508_);
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = 0;
v___x_1516_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1514_, v___x_1515_, v___x_1513_, v___f_1511_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1517_);
lean_dec(v___y_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object* v_ch_1526_){
_start:
{
lean_object* v___f_1527_; lean_object* v___f_1528_; lean_object* v___f_1529_; lean_object* v___f_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___f_1527_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1));
lean_inc_ref_n(v_ch_1526_, 2);
v___f_1528_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1528_, 0, v___f_1527_);
lean_closure_set(v___f_1528_, 1, v_ch_1526_);
v___f_1529_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2));
v___f_1530_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3));
v___x_1531_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1531_, 0, lean_box(0));
lean_closure_set(v___x_1531_, 1, lean_box(0));
lean_closure_set(v___x_1531_, 2, v_ch_1526_);
lean_closure_set(v___x_1531_, 3, v___f_1529_);
v___x_1532_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1532_, 0, lean_box(0));
lean_closure_set(v___x_1532_, 1, lean_box(0));
lean_closure_set(v___x_1532_, 2, v_ch_1526_);
lean_closure_set(v___x_1532_, 3, v___f_1530_);
v___x_1533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___f_1528_);
lean_ctor_set(v___x_1533_, 2, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object* v_00_u03b1_1534_, lean_object* v_ch_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object* v_00_u03b1_1537_, lean_object* v_q_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1538_, v___y_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_1542_, lean_object* v_q_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_1542_, v_q_1543_, v___y_1544_);
lean_dec(v___y_1544_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object* v_00_u03b1_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1548_, v_x_1549_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_1553_, v_x_1554_, v_x_1555_, v___y_1556_);
lean_dec(v___y_1556_);
return v_res_1558_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Std_Queue_empty(lean_box(0));
return v___x_1559_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = 0;
v___x_1561_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0);
v___x_1562_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*2, v___x_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg(){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1);
v___x_1565_ = l_Std_Mutex_new___redArg(v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object* v_00_u03b1_1568_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object* v_00_u03b1_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object* v_v_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v_producers_1587_; lean_object* v_consumers_1588_; uint8_t v_closed_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1612_; 
v___x_1586_ = lean_st_ref_get(v___y_1584_);
v_producers_1587_ = lean_ctor_get(v___x_1586_, 0);
v_consumers_1588_ = lean_ctor_get(v___x_1586_, 1);
v_closed_1589_ = lean_ctor_get_uint8(v___x_1586_, sizeof(void*)*2);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1591_ = v___x_1586_;
v_isShared_1592_ = v_isSharedCheck_1612_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_consumers_1588_);
lean_inc(v_producers_1587_);
lean_dec(v___x_1586_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1612_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_1588_);
if (lean_obj_tag(v___x_1593_) == 1)
{
lean_object* v_val_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1610_; 
v_val_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1610_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_val_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1610_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_fst_1598_; lean_object* v_snd_1599_; lean_object* v___x_1601_; 
v_fst_1598_ = lean_ctor_get(v_val_1594_, 0);
lean_inc(v_fst_1598_);
v_snd_1599_ = lean_ctor_get(v_val_1594_, 1);
lean_inc(v_snd_1599_);
lean_dec(v_val_1594_);
lean_inc(v_v_1583_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_v_1583_);
v___x_1601_ = v___x_1596_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_v_1583_);
v___x_1601_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
uint8_t v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_1598_, v___x_1601_);
lean_dec(v_fst_1598_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 1, v_snd_1599_);
v___x_1604_ = v___x_1591_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_producers_1587_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_snd_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1608_, sizeof(void*)*2, v_closed_1589_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_st_ref_swap(v___y_1584_, v___x_1604_);
lean_dec(v___x_1605_);
if (v___x_1602_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_1607_; 
lean_dec(v_v_1583_);
v___x_1607_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0));
return v___x_1607_;
}
}
}
}
}
else
{
lean_object* v___x_1611_; 
lean_dec(v___x_1593_);
lean_del_object(v___x_1591_);
lean_dec_ref(v_producers_1587_);
lean_dec(v_v_1583_);
v___x_1611_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2));
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object* v_v_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1613_, v___y_1614_);
lean_dec(v___y_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object* v_v_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v_fst_1621_; 
v___x_1620_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1617_, v_a_1618_);
v_fst_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_fst_1621_);
lean_dec_ref(v___x_1620_);
if (lean_obj_tag(v_fst_1621_) == 0)
{
uint8_t v___x_1622_; 
v___x_1622_ = 1;
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; uint8_t v___x_1624_; 
v_val_1623_ = lean_ctor_get(v_fst_1621_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v_fst_1621_, 1);
v___x_1624_ = lean_unbox(v_val_1623_);
lean_dec(v_val_1623_);
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object* v_v_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_res_1628_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1625_, v_a_1626_);
lean_dec(v_a_1626_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object* v_00_u03b1_1630_, lean_object* v_v_1631_, lean_object* v_a_1632_){
_start:
{
uint8_t v___x_1634_; 
v___x_1634_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1631_, v_a_1632_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object* v_00_u03b1_1635_, lean_object* v_v_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
uint8_t v_res_1639_; lean_object* v_r_1640_; 
v_res_1639_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(v_00_u03b1_1635_, v_v_1636_, v_a_1637_);
lean_dec(v_a_1637_);
v_r_1640_ = lean_box(v_res_1639_);
return v_r_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object* v_00_u03b1_1641_, lean_object* v_v_1642_, lean_object* v_inst_1643_, lean_object* v_a_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1642_, v___y_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1648_, lean_object* v_v_1649_, lean_object* v_inst_1650_, lean_object* v_a_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_1648_, v_v_1649_, v_inst_1650_, v_a_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v_a_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object* v_v_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; uint8_t v_closed_1659_; 
v___x_1658_ = lean_st_ref_get(v___y_1656_);
v_closed_1659_ = lean_ctor_get_uint8(v___x_1658_, sizeof(void*)*2);
lean_dec(v___x_1658_);
if (v_closed_1659_ == 0)
{
uint8_t v___x_1660_; 
v___x_1660_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1655_, v___y_1656_);
return v___x_1660_;
}
else
{
uint8_t v___x_1661_; 
lean_dec(v_v_1655_);
v___x_1661_ = 0;
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object* v_v_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1662_, v___y_1663_);
lean_dec(v___y_1663_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object* v_ch_1667_, lean_object* v_v_1668_){
_start:
{
lean_object* v___f_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___f_1670_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1670_, 0, v_v_1668_);
v___x_1671_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1667_, v___f_1670_);
v___x_1672_ = lean_unbox(v___x_1671_);
lean_dec(v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object* v_ch_1673_, lean_object* v_v_1674_, lean_object* v_a_1675_){
_start:
{
uint8_t v_res_1676_; lean_object* v_r_1677_; 
v_res_1676_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1673_, v_v_1674_);
v_r_1677_ = lean_box(v_res_1676_);
return v_r_1677_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object* v_00_u03b1_1678_, lean_object* v_ch_1679_, lean_object* v_v_1680_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1679_, v_v_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object* v_00_u03b1_1683_, lean_object* v_ch_1684_, lean_object* v_v_1685_, lean_object* v_a_1686_){
_start:
{
uint8_t v_res_1687_; lean_object* v_r_1688_; 
v_res_1687_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(v_00_u03b1_1683_, v_ch_1684_, v_v_1685_);
v_r_1688_ = lean_box(v_res_1687_);
return v_r_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object* v_x_1689_){
_start:
{
if (lean_obj_tag(v_x_1689_) == 0)
{
goto v___jp_1690_;
}
else
{
lean_object* v_val_1692_; uint8_t v___x_1693_; 
v_val_1692_ = lean_ctor_get(v_x_1689_, 0);
v___x_1693_ = lean_unbox(v_val_1692_);
if (v___x_1693_ == 0)
{
goto v___jp_1690_;
}
else
{
lean_object* v___x_1694_; 
v___x_1694_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
return v___x_1694_;
}
}
v___jp_1690_:
{
lean_object* v___x_1691_; 
v___x_1691_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_1695_);
lean_dec(v_x_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object* v_v_1697_, lean_object* v___f_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; uint8_t v_closed_1702_; 
v___x_1701_ = lean_st_ref_get(v___y_1699_);
v_closed_1702_ = lean_ctor_get_uint8(v___x_1701_, sizeof(void*)*2);
lean_dec(v___x_1701_);
if (v_closed_1702_ == 0)
{
uint8_t v___x_1703_; 
lean_inc(v_v_1697_);
v___x_1703_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1697_, v___y_1699_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v_producers_1706_; lean_object* v_consumers_1707_; uint8_t v_closed_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1722_; 
v___x_1704_ = lean_io_promise_new();
v___x_1705_ = lean_st_ref_take(v___y_1699_);
v_producers_1706_ = lean_ctor_get(v___x_1705_, 0);
v_consumers_1707_ = lean_ctor_get(v___x_1705_, 1);
v_closed_1708_ = lean_ctor_get_uint8(v___x_1705_, sizeof(void*)*2);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1710_ = v___x_1705_;
v_isShared_1711_ = v_isSharedCheck_1722_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_consumers_1707_);
lean_inc(v_producers_1706_);
lean_dec(v___x_1705_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1722_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_inc(v___x_1704_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_v_1697_);
lean_ctor_set(v___x_1712_, 1, v___x_1704_);
v___x_1713_ = l_Std_Queue_enqueue___redArg(v___x_1712_, v_producers_1706_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1713_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_consumers_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*2, v_closed_1708_);
v___x_1715_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1716_ = lean_st_ref_put(v___y_1699_, v___x_1715_);
v___x_1717_ = 1;
v___x_1718_ = lean_io_promise_result_opt(v___x_1704_);
lean_dec(v___x_1704_);
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_task_map(v___f_1698_, v___x_1718_, v___x_1719_, v___x_1717_);
return v___x_1720_;
}
}
}
else
{
lean_object* v___x_1723_; 
lean_dec_ref(v___f_1698_);
lean_dec(v_v_1697_);
v___x_1723_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_1723_;
}
}
else
{
lean_object* v___x_1724_; 
lean_dec_ref(v___f_1698_);
lean_dec(v_v_1697_);
v___x_1724_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_1724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object* v_v_1725_, lean_object* v___f_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1725_, v___f_1726_, v___y_1727_);
lean_dec(v___y_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object* v_ch_1731_, lean_object* v_v_1732_){
_start:
{
lean_object* v___f_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; 
v___f_1734_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0));
v___f_1735_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1735_, 0, v_v_1732_);
lean_closure_set(v___f_1735_, 1, v___f_1734_);
v___x_1736_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1731_, v___f_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object* v_ch_1737_, lean_object* v_v_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1737_, v_v_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object* v_00_u03b1_1741_, lean_object* v_ch_1742_, lean_object* v_v_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1742_, v_v_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_ch_1747_, lean_object* v_v_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(v_00_u03b1_1746_, v_ch_1747_, v_v_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object* v_as_1751_, size_t v_sz_1752_, size_t v_i_1753_, lean_object* v_b_1754_){
_start:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_usize_dec_lt(v_i_1753_, v_sz_1752_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_b_1754_);
return v___x_1757_;
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; size_t v___x_1762_; size_t v___x_1763_; 
v_a_1758_ = lean_array_uget_borrowed(v_as_1751_, v_i_1753_);
v___x_1759_ = lean_box(0);
v___x_1760_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_1758_, v___x_1759_);
v___x_1761_ = lean_box(0);
v___x_1762_ = ((size_t)1ULL);
v___x_1763_ = lean_usize_add(v_i_1753_, v___x_1762_);
v_i_1753_ = v___x_1763_;
v_b_1754_ = v___x_1761_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object* v_as_1765_, lean_object* v_sz_1766_, lean_object* v_i_1767_, lean_object* v_b_1768_, lean_object* v___y_1769_){
_start:
{
size_t v_sz_boxed_1770_; size_t v_i_boxed_1771_; lean_object* v_res_1772_; 
v_sz_boxed_1770_ = lean_unbox_usize(v_sz_1766_);
lean_dec(v_sz_1766_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1767_);
lean_dec(v_i_1767_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1765_, v_sz_boxed_1770_, v_i_boxed_1771_, v_b_1768_);
lean_dec_ref(v_as_1765_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; uint8_t v_closed_1776_; 
v___x_1775_ = lean_st_ref_get(v___y_1773_);
v_closed_1776_ = lean_ctor_get_uint8(v___x_1775_, sizeof(void*)*2);
if (v_closed_1776_ == 0)
{
lean_object* v_producers_1777_; lean_object* v_consumers_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1801_; 
v_producers_1777_ = lean_ctor_get(v___x_1775_, 0);
v_consumers_1778_ = lean_ctor_get(v___x_1775_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1780_ = v___x_1775_;
v_isShared_1781_ = v_isSharedCheck_1801_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_consumers_1778_);
lean_inc(v_producers_1777_);
lean_dec(v___x_1775_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1801_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; size_t v_sz_1784_; size_t v___x_1785_; lean_object* v___x_1786_; 
v___x_1782_ = l_Std_Queue_toArray___redArg(v_consumers_1778_);
v___x_1783_ = lean_box(0);
v_sz_1784_ = lean_array_size(v___x_1782_);
v___x_1785_ = ((size_t)0ULL);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_1782_, v_sz_1784_, v___x_1785_, v___x_1783_);
lean_dec_ref(v___x_1782_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1799_; 
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; 
v_unused_1800_ = lean_ctor_get(v___x_1786_, 0);
lean_dec(v_unused_1800_);
v___x_1788_ = v___x_1786_;
v_isShared_1789_ = v_isSharedCheck_1799_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v___x_1786_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1799_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; uint8_t v___x_1791_; lean_object* v___x_1793_; 
v___x_1790_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
v___x_1791_ = 1;
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v___x_1790_);
v___x_1793_ = v___x_1780_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_producers_1777_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v___x_1790_);
v___x_1793_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1794_; lean_object* v___x_1796_; 
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*2, v___x_1791_);
v___x_1794_ = lean_st_ref_swap(v___y_1773_, v___x_1793_);
lean_dec(v___x_1794_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1783_);
v___x_1796_ = v___x_1788_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1783_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_del_object(v___x_1780_);
lean_dec_ref(v_producers_1777_);
return v___x_1786_;
}
}
}
else
{
uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v___x_1775_);
v___x_1802_ = 1;
v___x_1803_ = lean_box(v___x_1802_);
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1805_);
lean_dec(v___y_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object* v_ch_1809_){
_start:
{
lean_object* v___f_1811_; lean_object* v___x_1812_; 
v___f_1811_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0));
v___x_1812_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_1809_, v___f_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object* v_ch_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object* v_00_u03b1_1816_, lean_object* v_ch_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object* v_00_u03b1_1820_, lean_object* v_ch_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(v_00_u03b1_1820_, v_ch_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object* v_00_u03b1_1824_, lean_object* v_as_1825_, size_t v_sz_1826_, size_t v_i_1827_, lean_object* v_b_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1825_, v_sz_1826_, v_i_1827_, v_b_1828_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object* v_00_u03b1_1832_, lean_object* v_as_1833_, lean_object* v_sz_1834_, lean_object* v_i_1835_, lean_object* v_b_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
size_t v_sz_boxed_1839_; size_t v_i_boxed_1840_; lean_object* v_res_1841_; 
v_sz_boxed_1839_ = lean_unbox_usize(v_sz_1834_);
lean_dec(v_sz_1834_);
v_i_boxed_1840_ = lean_unbox_usize(v_i_1835_);
lean_dec(v_i_1835_);
v_res_1841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_1832_, v_as_1833_, v_sz_boxed_1839_, v_i_boxed_1840_, v_b_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v_as_1833_);
return v_res_1841_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; uint8_t v_closed_1845_; 
v___x_1844_ = lean_st_ref_get(v___y_1842_);
v_closed_1845_ = lean_ctor_get_uint8(v___x_1844_, sizeof(void*)*2);
lean_dec(v___x_1844_);
return v_closed_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
uint8_t v_res_1848_; lean_object* v_r_1849_; 
v_res_1848_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1846_);
lean_dec(v___y_1846_);
v_r_1849_ = lean_box(v_res_1848_);
return v_r_1849_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object* v_ch_1851_){
_start:
{
lean_object* v___f_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___f_1853_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0));
v___x_1854_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1851_, v___f_1853_);
v___x_1855_ = lean_unbox(v___x_1854_);
lean_dec(v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object* v_ch_1856_, lean_object* v_a_1857_){
_start:
{
uint8_t v_res_1858_; lean_object* v_r_1859_; 
v_res_1858_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1856_);
v_r_1859_ = lean_box(v_res_1858_);
return v_r_1859_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object* v_00_u03b1_1860_, lean_object* v_ch_1861_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object* v_00_u03b1_1864_, lean_object* v_ch_1865_, lean_object* v_a_1866_){
_start:
{
uint8_t v_res_1867_; lean_object* v_r_1868_; 
v_res_1867_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(v_00_u03b1_1864_, v_ch_1865_);
v_r_1868_ = lean_box(v_res_1867_);
return v_r_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object* v_snd_1869_, lean_object* v_inst_1870_, lean_object* v_toBind_1871_, lean_object* v___f_1872_, lean_object* v_a_1873_){
_start:
{
uint8_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1874_ = 1;
v___x_1875_ = lean_box(v___x_1874_);
v___x_1876_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1876_, 0, lean_box(0));
lean_closure_set(v___x_1876_, 1, v___x_1875_);
lean_closure_set(v___x_1876_, 2, v_snd_1869_);
v___x_1877_ = lean_apply_2(v_inst_1870_, lean_box(0), v___x_1876_);
v___x_1878_ = lean_apply_4(v_toBind_1871_, lean_box(0), lean_box(0), v___x_1877_, v___f_1872_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_1879_, lean_object* v_inst_1880_, lean_object* v_toBind_1881_, lean_object* v_a_1882_, lean_object* v_inst_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_producers_1885_; lean_object* v_consumers_1886_; uint8_t v_closed_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1908_; 
v_producers_1885_ = lean_ctor_get(v_a_1884_, 0);
v_consumers_1886_ = lean_ctor_get(v_a_1884_, 1);
v_closed_1887_ = lean_ctor_get_uint8(v_a_1884_, sizeof(void*)*2);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_a_1884_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1889_ = v_a_1884_;
v_isShared_1890_ = v_isSharedCheck_1908_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_consumers_1886_);
lean_inc(v_producers_1885_);
lean_dec(v_a_1884_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1908_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1885_);
if (lean_obj_tag(v___x_1891_) == 1)
{
lean_object* v_val_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v_fst_1895_; lean_object* v_snd_1896_; lean_object* v___f_1897_; lean_object* v___f_1898_; lean_object* v___x_1900_; 
v_val_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_val_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v_fst_1893_ = lean_ctor_get(v_val_1892_, 0);
lean_inc(v_fst_1893_);
v_snd_1894_ = lean_ctor_get(v_val_1892_, 1);
lean_inc(v_snd_1894_);
lean_dec(v_val_1892_);
v_fst_1895_ = lean_ctor_get(v_fst_1893_, 0);
lean_inc(v_fst_1895_);
v_snd_1896_ = lean_ctor_get(v_fst_1893_, 1);
lean_inc(v_snd_1896_);
lean_dec(v_fst_1893_);
v___f_1897_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1897_, 0, v_toApplicative_1879_);
lean_closure_set(v___f_1897_, 1, v_fst_1895_);
lean_inc(v_toBind_1881_);
v___f_1898_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1898_, 0, v_snd_1896_);
lean_closure_set(v___f_1898_, 1, v_inst_1880_);
lean_closure_set(v___f_1898_, 2, v_toBind_1881_);
lean_closure_set(v___f_1898_, 3, v___f_1897_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_snd_1894_);
v___x_1900_ = v___x_1889_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_snd_1894_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_consumers_1886_);
lean_ctor_set_uint8(v_reuseFailAlloc_1904_, sizeof(void*)*2, v_closed_1887_);
v___x_1900_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_inc(v_a_1882_);
v___x_1901_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1901_, 0, lean_box(0));
lean_closure_set(v___x_1901_, 1, lean_box(0));
lean_closure_set(v___x_1901_, 2, v_a_1882_);
lean_closure_set(v___x_1901_, 3, v___x_1900_);
v___x_1902_ = lean_apply_2(v_inst_1883_, lean_box(0), v___x_1901_);
v___x_1903_ = lean_apply_4(v_toBind_1881_, lean_box(0), lean_box(0), v___x_1902_, v___f_1898_);
return v___x_1903_;
}
}
else
{
lean_object* v_toPure_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_dec(v___x_1891_);
lean_del_object(v___x_1889_);
lean_dec_ref(v_consumers_1886_);
lean_dec(v_inst_1883_);
lean_dec(v_toBind_1881_);
lean_dec(v_inst_1880_);
v_toPure_1905_ = lean_ctor_get(v_toApplicative_1879_, 1);
lean_inc(v_toPure_1905_);
lean_dec_ref(v_toApplicative_1879_);
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_apply_2(v_toPure_1905_, lean_box(0), v___x_1906_);
return v___x_1907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_1909_, lean_object* v_inst_1910_, lean_object* v_toBind_1911_, lean_object* v_a_1912_, lean_object* v_inst_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(v_toApplicative_1909_, v_inst_1910_, v_toBind_1911_, v_a_1912_, v_inst_1913_, v_a_1914_);
lean_dec(v_a_1912_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_toApplicative_1920_; lean_object* v_toBind_1921_; lean_object* v___f_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_toApplicative_1920_ = lean_ctor_get(v_inst_1916_, 0);
lean_inc_ref(v_toApplicative_1920_);
v_toBind_1921_ = lean_ctor_get(v_inst_1916_, 1);
lean_inc_n(v_toBind_1921_, 2);
lean_dec_ref(v_inst_1916_);
lean_inc(v_inst_1917_);
lean_inc_n(v_a_1919_, 2);
v___f_1922_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1922_, 0, v_toApplicative_1920_);
lean_closure_set(v___f_1922_, 1, v_inst_1918_);
lean_closure_set(v___f_1922_, 2, v_toBind_1921_);
lean_closure_set(v___f_1922_, 3, v_a_1919_);
lean_closure_set(v___f_1922_, 4, v_inst_1917_);
v___x_1923_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1923_, 0, lean_box(0));
lean_closure_set(v___x_1923_, 1, lean_box(0));
lean_closure_set(v___x_1923_, 2, v_a_1919_);
v___x_1924_ = lean_apply_2(v_inst_1917_, lean_box(0), v___x_1923_);
v___x_1925_ = lean_apply_4(v_toBind_1921_, lean_box(0), lean_box(0), v___x_1924_, v___f_1922_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(lean_object* v_inst_1926_, lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1926_, v_inst_1927_, v_inst_1928_, v_a_1929_);
lean_dec(v_a_1929_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object* v_m_1931_, lean_object* v_00_u03b1_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1933_, v_inst_1934_, v_inst_1935_, v_a_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(lean_object* v_m_1938_, lean_object* v_00_u03b1_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(v_m_1938_, v_00_u03b1_1939_, v_inst_1940_, v_inst_1941_, v_inst_1942_, v_a_1943_);
lean_dec(v_a_1943_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v_producers_1948_; lean_object* v_consumers_1949_; uint8_t v_closed_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1975_; 
v___x_1947_ = lean_st_ref_get(v_a_1945_);
v_producers_1948_ = lean_ctor_get(v___x_1947_, 0);
v_consumers_1949_ = lean_ctor_get(v___x_1947_, 1);
v_closed_1950_ = lean_ctor_get_uint8(v___x_1947_, sizeof(void*)*2);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1952_ = v___x_1947_;
v_isShared_1953_ = v_isSharedCheck_1975_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_consumers_1949_);
lean_inc(v_producers_1948_);
lean_dec(v___x_1947_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1975_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1948_);
if (lean_obj_tag(v___x_1954_) == 1)
{
lean_object* v_val_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1973_; 
v_val_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1973_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_val_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1973_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v_fst_1961_; lean_object* v_snd_1962_; lean_object* v___x_1964_; 
v_fst_1959_ = lean_ctor_get(v_val_1955_, 0);
lean_inc(v_fst_1959_);
v_snd_1960_ = lean_ctor_get(v_val_1955_, 1);
lean_inc(v_snd_1960_);
lean_dec(v_val_1955_);
v_fst_1961_ = lean_ctor_get(v_fst_1959_, 0);
lean_inc(v_fst_1961_);
v_snd_1962_ = lean_ctor_get(v_fst_1959_, 1);
lean_inc(v_snd_1962_);
lean_dec(v_fst_1959_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v_snd_1960_);
v___x_1964_ = v___x_1952_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_snd_1960_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_consumers_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*2, v_closed_1950_);
v___x_1964_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1965_ = lean_st_ref_swap(v_a_1945_, v___x_1964_);
lean_dec(v___x_1965_);
v___x_1966_ = 1;
v___x_1967_ = lean_box(v___x_1966_);
v___x_1968_ = lean_io_promise_resolve(v___x_1967_, v_snd_1962_);
lean_dec(v_snd_1962_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v_fst_1961_);
v___x_1970_ = v___x_1957_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_fst_1961_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v___x_1974_; 
lean_dec(v___x_1954_);
lean_del_object(v___x_1952_);
lean_dec_ref(v_consumers_1949_);
v___x_1974_ = lean_box(0);
return v___x_1974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object* v_a_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1976_);
lean_dec(v_a_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object* v_00_u03b1_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_1983_, lean_object* v_a_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_1983_, v_a_1984_);
lean_dec(v_a_1984_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object* v_ch_1988_){
_start:
{
lean_object* v___f_1990_; lean_object* v___x_1991_; 
v___f_1990_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0));
v___x_1991_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1988_, v___f_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object* v_ch_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_1992_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object* v_00_u03b1_1995_, lean_object* v_ch_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_ch_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(v_00_u03b1_1999_, v_ch_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object* v___f_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_st_ref_get(v___y_2004_);
v___x_2007_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_2004_);
if (lean_obj_tag(v___x_2007_) == 1)
{
lean_object* v___x_2008_; 
lean_dec(v___x_2006_);
lean_dec_ref(v___f_2003_);
v___x_2008_ = lean_task_pure(v___x_2007_);
return v___x_2008_;
}
else
{
uint8_t v_closed_2009_; 
lean_dec(v___x_2007_);
v_closed_2009_ = lean_ctor_get_uint8(v___x_2006_, sizeof(void*)*2);
if (v_closed_2009_ == 0)
{
lean_object* v_producers_2010_; lean_object* v_consumers_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2026_; 
v_producers_2010_ = lean_ctor_get(v___x_2006_, 0);
v_consumers_2011_ = lean_ctor_get(v___x_2006_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2013_ = v___x_2006_;
v_isShared_2014_ = v_isSharedCheck_2026_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_consumers_2011_);
lean_inc(v_producers_2010_);
lean_dec(v___x_2006_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2026_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2015_ = lean_io_promise_new();
lean_inc(v___x_2015_);
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
v___x_2017_ = l_Std_Queue_enqueue___redArg(v___x_2016_, v_consumers_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v___x_2017_);
v___x_2019_ = v___x_2013_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_producers_2010_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*2, v_closed_2009_);
v___x_2019_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2020_ = lean_st_ref_swap(v___y_2004_, v___x_2019_);
lean_dec(v___x_2020_);
v___x_2021_ = 1;
v___x_2022_ = lean_io_promise_result_opt(v___x_2015_);
lean_dec(v___x_2015_);
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_task_map(v___f_2003_, v___x_2022_, v___x_2023_, v___x_2021_);
return v___x_2024_;
}
}
}
else
{
lean_object* v___x_2027_; 
lean_dec(v___x_2006_);
lean_dec_ref(v___f_2003_);
v___x_2027_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object* v___f_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2028_, v___y_2029_);
lean_dec(v___y_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object* v_ch_2034_){
_start:
{
lean_object* v___f_2036_; lean_object* v___x_2037_; 
v___f_2036_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0));
v___x_2037_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2034_, v___f_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object* v_ch_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object* v_00_u03b1_2041_, lean_object* v_ch_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2042_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object* v_00_u03b1_2045_, lean_object* v_ch_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(v_00_u03b1_2045_, v_ch_2046_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_2049_, lean_object* v_a_2050_){
_start:
{
uint8_t v___y_2052_; lean_object* v_producers_2056_; uint8_t v_closed_2057_; uint8_t v___x_2058_; 
v_producers_2056_ = lean_ctor_get(v_a_2050_, 0);
v_closed_2057_ = lean_ctor_get_uint8(v_a_2050_, sizeof(void*)*2);
v___x_2058_ = l_Std_Queue_isEmpty___redArg(v_producers_2056_);
if (v___x_2058_ == 0)
{
uint8_t v___x_2059_; 
v___x_2059_ = 1;
v___y_2052_ = v___x_2059_;
goto v___jp_2051_;
}
else
{
v___y_2052_ = v_closed_2057_;
goto v___jp_2051_;
}
v___jp_2051_:
{
lean_object* v_toPure_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_toPure_2053_ = lean_ctor_get(v_toApplicative_2049_, 1);
lean_inc(v_toPure_2053_);
lean_dec_ref(v_toApplicative_2049_);
v___x_2054_ = lean_box(v___y_2052_);
v___x_2055_ = lean_apply_2(v_toPure_2053_, lean_box(0), v___x_2054_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(v_toApplicative_2060_, v_a_2061_);
lean_dec_ref(v_a_2061_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_toApplicative_2066_; lean_object* v_toBind_2067_; lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_toApplicative_2066_ = lean_ctor_get(v_inst_2063_, 0);
lean_inc_ref(v_toApplicative_2066_);
v_toBind_2067_ = lean_ctor_get(v_inst_2063_, 1);
lean_inc(v_toBind_2067_);
lean_dec_ref(v_inst_2063_);
v___f_2068_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2068_, 0, v_toApplicative_2066_);
lean_inc(v_a_2065_);
v___x_2069_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2069_, 0, lean_box(0));
lean_closure_set(v___x_2069_, 1, lean_box(0));
lean_closure_set(v___x_2069_, 2, v_a_2065_);
v___x_2070_ = lean_apply_2(v_inst_2064_, lean_box(0), v___x_2069_);
v___x_2071_ = lean_apply_4(v_toBind_2067_, lean_box(0), lean_box(0), v___x_2070_, v___f_2068_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(v_inst_2072_, v_inst_2073_, v_a_2074_);
lean_dec(v_a_2074_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object* v_m_2076_, lean_object* v_00_u03b1_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_toApplicative_2081_; lean_object* v_toBind_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_toApplicative_2081_ = lean_ctor_get(v_inst_2078_, 0);
lean_inc_ref(v_toApplicative_2081_);
v_toBind_2082_ = lean_ctor_get(v_inst_2078_, 1);
lean_inc(v_toBind_2082_);
lean_dec_ref(v_inst_2078_);
v___f_2083_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2083_, 0, v_toApplicative_2081_);
lean_inc(v_a_2080_);
v___x_2084_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2084_, 0, lean_box(0));
lean_closure_set(v___x_2084_, 1, lean_box(0));
lean_closure_set(v___x_2084_, 2, v_a_2080_);
v___x_2085_ = lean_apply_2(v_inst_2079_, lean_box(0), v___x_2084_);
v___x_2086_ = lean_apply_4(v_toBind_2082_, lean_box(0), lean_box(0), v___x_2085_, v___f_2083_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(lean_object* v_m_2087_, lean_object* v_00_u03b1_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(v_m_2087_, v_00_u03b1_2088_, v_inst_2089_, v_inst_2090_, v_a_2091_);
lean_dec(v_a_2091_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object* v_snd_2093_, lean_object* v___f_2094_, lean_object* v_x_2095_){
_start:
{
if (lean_obj_tag(v_x_2095_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2105_; 
lean_dec_ref(v___f_2094_);
v_a_2097_ = lean_ctor_get(v_x_2095_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_x_2095_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2099_ = v_x_2095_;
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v_x_2095_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; 
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
}
else
{
lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2119_; 
v_isSharedCheck_2119_ = !lean_is_exclusive(v_x_2095_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v_x_2095_, 0);
lean_dec(v_unused_2120_);
v___x_2107_ = v_x_2095_;
v_isShared_2108_ = v_isSharedCheck_2119_;
goto v_resetjp_2106_;
}
else
{
lean_dec(v_x_2095_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2119_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2109_ = 1;
v___x_2110_ = lean_box(v___x_2109_);
v___x_2111_ = lean_io_promise_resolve(v___x_2110_, v_snd_2093_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2111_);
v___x_2113_ = v___x_2107_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = 0;
v___x_2117_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2115_, v___x_2116_, v___x_2114_, v___f_2094_);
return v___x_2117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_snd_2121_, lean_object* v___f_2122_, lean_object* v_x_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2121_, v___f_2122_, v_x_2123_);
lean_dec(v_snd_2121_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object* v_a_2126_, lean_object* v_x_2127_){
_start:
{
if (lean_obj_tag(v_x_2127_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2137_; 
v_a_2129_ = lean_ctor_get(v_x_2127_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_x_2127_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2131_ = v_x_2127_;
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v_x_2127_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
return v___x_2135_;
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v_producers_2139_; lean_object* v_consumers_2140_; uint8_t v_closed_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2162_; 
v_a_2138_ = lean_ctor_get(v_x_2127_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v_x_2127_, 1);
v_producers_2139_ = lean_ctor_get(v_a_2138_, 0);
v_consumers_2140_ = lean_ctor_get(v_a_2138_, 1);
v_closed_2141_ = lean_ctor_get_uint8(v_a_2138_, sizeof(void*)*2);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_a_2138_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2143_ = v_a_2138_;
v_isShared_2144_ = v_isSharedCheck_2162_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_consumers_2140_);
lean_inc(v_producers_2139_);
lean_dec(v_a_2138_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2162_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2139_);
if (lean_obj_tag(v___x_2145_) == 1)
{
lean_object* v_val_2146_; lean_object* v_fst_2147_; lean_object* v_snd_2148_; lean_object* v_fst_2149_; lean_object* v_snd_2150_; lean_object* v___x_2152_; 
v_val_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_val_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v_fst_2147_ = lean_ctor_get(v_val_2146_, 0);
lean_inc(v_fst_2147_);
v_snd_2148_ = lean_ctor_get(v_val_2146_, 1);
lean_inc(v_snd_2148_);
lean_dec(v_val_2146_);
v_fst_2149_ = lean_ctor_get(v_fst_2147_, 0);
lean_inc(v_fst_2149_);
v_snd_2150_ = lean_ctor_get(v_fst_2147_, 1);
lean_inc(v_snd_2150_);
lean_dec(v_fst_2147_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v_snd_2148_);
v___x_2152_ = v___x_2143_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_snd_2148_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_consumers_2140_);
lean_ctor_set_uint8(v_reuseFailAlloc_2160_, sizeof(void*)*2, v_closed_2141_);
v___x_2152_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___f_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2153_ = lean_st_ref_swap(v_a_2126_, v___x_2152_);
lean_dec(v___x_2153_);
v___f_2154_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2154_, 0, v_fst_2149_);
v___f_2155_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2155_, 0, v_snd_2150_);
lean_closure_set(v___f_2155_, 1, v___f_2154_);
v___x_2156_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = 0;
v___x_2159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2157_, v___x_2158_, v___x_2156_, v___f_2155_);
return v___x_2159_;
}
}
else
{
lean_object* v___x_2161_; 
lean_dec(v___x_2145_);
lean_del_object(v___x_2143_);
lean_dec_ref(v_consumers_2140_);
v___x_2161_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_2161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_a_2163_, lean_object* v_x_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2163_, v_x_2164_);
lean_dec(v_a_2163_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object* v_a_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; 
v___x_2169_ = lean_st_ref_get(v_a_2167_);
lean_inc(v_a_2167_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2170_, 0, v_a_2167_);
v___x_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
v___x_2173_ = lean_unsigned_to_nat(0u);
v___x_2174_ = 0;
v___x_2175_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2173_, v___x_2174_, v___x_2172_, v___f_2170_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object* v_a_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2176_);
lean_dec(v_a_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object* v_00_u03b1_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_a_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_2183_, v_a_2184_);
lean_dec(v_a_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_2187_, lean_object* v___y_2188_, lean_object* v___f_2189_, lean_object* v_x_2190_){
_start:
{
if (lean_obj_tag(v_x_2190_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v___f_2189_);
lean_dec_ref(v_lose_2187_);
v_a_2192_ = lean_ctor_get(v_x_2190_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_x_2190_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2194_ = v_x_2190_;
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v_x_2190_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
}
}
else
{
lean_object* v_a_2201_; uint8_t v___x_2202_; 
v_a_2201_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v_x_2190_, 1);
v___x_2202_ = lean_unbox(v_a_2201_);
lean_dec(v_a_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; 
lean_dec_ref(v___f_2189_);
lean_inc(v___y_2188_);
v___x_2203_ = lean_apply_2(v_lose_2187_, v___y_2188_, lean_box(0));
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; 
lean_dec_ref(v_lose_2187_);
v___x_2204_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2188_);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = 0;
v___x_2207_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2205_, v___x_2206_, v___x_2204_, v___f_2189_);
return v___x_2207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_2208_, lean_object* v___y_2209_, lean_object* v___f_2210_, lean_object* v_x_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2208_, v___y_2209_, v___f_2210_, v_x_2211_);
lean_dec(v___y_2209_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object* v_w_2214_, lean_object* v_lose_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_finished_2218_; lean_object* v_promise_2219_; lean_object* v___x_2220_; lean_object* v___f_2221_; lean_object* v___f_2222_; uint8_t v___y_2224_; uint8_t v___x_2234_; 
v_finished_2218_ = lean_ctor_get(v_w_2214_, 0);
lean_inc(v_finished_2218_);
v_promise_2219_ = lean_ctor_get(v_w_2214_, 1);
lean_inc(v_promise_2219_);
lean_dec_ref(v_w_2214_);
v___x_2220_ = lean_st_ref_take(v_finished_2218_);
v___f_2221_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2221_, 0, v_promise_2219_);
lean_inc(v___y_2216_);
v___f_2222_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2222_, 0, v_lose_2215_);
lean_closure_set(v___f_2222_, 1, v___y_2216_);
lean_closure_set(v___f_2222_, 2, v___f_2221_);
v___x_2234_ = lean_unbox(v___x_2220_);
lean_dec(v___x_2220_);
if (v___x_2234_ == 0)
{
uint8_t v___x_2235_; 
v___x_2235_ = 1;
v___y_2224_ = v___x_2235_;
goto v___jp_2223_;
}
else
{
uint8_t v___x_2236_; 
v___x_2236_ = 0;
v___y_2224_ = v___x_2236_;
goto v___jp_2223_;
}
v___jp_2223_:
{
uint8_t v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2225_ = 1;
v___x_2226_ = lean_box(v___x_2225_);
v___x_2227_ = lean_st_ref_put(v_finished_2218_, v___x_2226_);
lean_dec(v_finished_2218_);
v___x_2228_ = lean_box(v___y_2224_);
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
v___x_2231_ = lean_unsigned_to_nat(0u);
v___x_2232_ = 0;
v___x_2233_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2231_, v___x_2232_, v___x_2230_, v___f_2222_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object* v_w_2237_, lean_object* v_lose_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2237_, v_lose_2238_, v___y_2239_);
lean_dec(v___y_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object* v_00_u03b1_2242_, lean_object* v_w_2243_, lean_object* v_lose_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2243_, v_lose_2244_, v___y_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_2248_, lean_object* v_w_2249_, lean_object* v_lose_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_2248_, v_w_2249_, v_lose_2250_, v___y_2251_);
lean_dec(v___y_2251_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object* v_x_2254_){
_start:
{
uint8_t v___y_2257_; 
if (lean_obj_tag(v_x_2254_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2269_; 
v_a_2261_ = lean_ctor_get(v_x_2254_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_x_2254_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2263_ = v_x_2254_;
v_isShared_2264_ = v_isSharedCheck_2269_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v_x_2254_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2269_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v_producers_2271_; uint8_t v_closed_2272_; uint8_t v___x_2273_; 
v_a_2270_ = lean_ctor_get(v_x_2254_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v_x_2254_, 1);
v_producers_2271_ = lean_ctor_get(v_a_2270_, 0);
lean_inc_ref(v_producers_2271_);
v_closed_2272_ = lean_ctor_get_uint8(v_a_2270_, sizeof(void*)*2);
lean_dec(v_a_2270_);
v___x_2273_ = l_Std_Queue_isEmpty___redArg(v_producers_2271_);
lean_dec_ref(v_producers_2271_);
if (v___x_2273_ == 0)
{
uint8_t v___x_2274_; 
v___x_2274_ = 1;
v___y_2257_ = v___x_2274_;
goto v___jp_2256_;
}
else
{
v___y_2257_ = v_closed_2272_;
goto v___jp_2256_;
}
}
v___jp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = lean_box(v___y_2257_);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object* v_x_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object* v___y_2278_, lean_object* v_waiter_2279_, lean_object* v_x_2280_){
_start:
{
if (lean_obj_tag(v_x_2280_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_waiter_2279_);
v_a_2282_ = lean_ctor_get(v_x_2280_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_x_2280_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2284_ = v_x_2280_;
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v_x_2280_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
}
}
else
{
lean_object* v_a_2291_; uint8_t v___x_2292_; 
v_a_2291_ = lean_ctor_get(v_x_2280_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v_x_2280_, 1);
v___x_2292_ = lean_unbox(v_a_2291_);
lean_dec(v_a_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; lean_object* v_producers_2294_; lean_object* v_consumers_2295_; uint8_t v_closed_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2307_; 
v___x_2293_ = lean_st_ref_take(v___y_2278_);
v_producers_2294_ = lean_ctor_get(v___x_2293_, 0);
v_consumers_2295_ = lean_ctor_get(v___x_2293_, 1);
v_closed_2296_ = lean_ctor_get_uint8(v___x_2293_, sizeof(void*)*2);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2298_ = v___x_2293_;
v_isShared_2299_ = v_isSharedCheck_2307_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_consumers_2295_);
lean_inc(v_producers_2294_);
lean_dec(v___x_2293_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2307_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_waiter_2279_);
v___x_2301_ = l_Std_Queue_enqueue___redArg(v___x_2300_, v_consumers_2295_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v___x_2301_);
v___x_2303_ = v___x_2298_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_producers_2294_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v___x_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2306_, sizeof(void*)*2, v_closed_2296_);
v___x_2303_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_st_ref_put(v___y_2278_, v___x_2303_);
v___x_2305_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2305_;
}
}
}
else
{
lean_object* v_lose_2308_; lean_object* v___x_2309_; 
v_lose_2308_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0));
v___x_2309_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_2279_, v_lose_2308_, v___y_2278_);
return v___x_2309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object* v___y_2310_, lean_object* v_waiter_2311_, lean_object* v_x_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2310_, v_waiter_2311_, v_x_2312_);
lean_dec(v___y_2310_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object* v___f_2315_, lean_object* v_waiter_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___f_2325_; lean_object* v___x_2326_; 
v___x_2319_ = lean_st_ref_get(v___y_2317_);
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = 0;
v___x_2324_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2322_, v___x_2323_, v___x_2321_, v___f_2315_);
lean_inc(v___y_2317_);
v___f_2325_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2325_, 0, v___y_2317_);
lean_closure_set(v___f_2325_, 1, v_waiter_2316_);
v___x_2326_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2322_, v___x_2323_, v___x_2324_, v___f_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object* v___f_2327_, lean_object* v_waiter_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v___f_2327_, v_waiter_2328_, v___y_2329_);
lean_dec(v___y_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object* v___f_2332_, lean_object* v_ch_2333_, lean_object* v_waiter_2334_){
_start:
{
lean_object* v___f_2336_; lean_object* v___x_2337_; 
v___f_2336_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2336_, 0, v___f_2332_);
lean_closure_set(v___f_2336_, 1, v_waiter_2334_);
v___x_2337_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_2333_, v___f_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object* v___f_2338_, lean_object* v_ch_2339_, lean_object* v_waiter_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2338_, v_ch_2339_, v_waiter_2340_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object* v___y_2343_, lean_object* v___f_2344_, lean_object* v_x_2345_){
_start:
{
if (lean_obj_tag(v_x_2345_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref(v___f_2344_);
v_a_2347_ = lean_ctor_get(v_x_2345_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_x_2345_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2349_ = v_x_2345_;
v_isShared_2350_ = v_isSharedCheck_2355_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v_x_2345_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2355_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; 
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
}
}
else
{
lean_object* v_a_2356_; uint8_t v___x_2357_; 
v_a_2356_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v_x_2345_, 1);
v___x_2357_ = lean_unbox(v_a_2356_);
lean_dec(v_a_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
lean_dec_ref(v___f_2344_);
v___x_2358_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_2358_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2359_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2343_);
v___x_2360_ = lean_unsigned_to_nat(0u);
v___x_2361_ = 0;
v___x_2362_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2360_, v___x_2361_, v___x_2359_, v___f_2344_);
return v___x_2362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object* v___y_2363_, lean_object* v___f_2364_, lean_object* v_x_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2363_, v___f_2364_, v_x_2365_);
lean_dec(v___y_2363_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object* v___f_2368_, lean_object* v___f_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___f_2378_; lean_object* v___x_2379_; 
v___x_2372_ = lean_st_ref_get(v___y_2370_);
v___x_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
v___x_2375_ = lean_unsigned_to_nat(0u);
v___x_2376_ = 0;
v___x_2377_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2375_, v___x_2376_, v___x_2374_, v___f_2368_);
lean_inc(v___y_2370_);
v___f_2378_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2378_, 0, v___y_2370_);
lean_closure_set(v___f_2378_, 1, v___f_2369_);
v___x_2379_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2375_, v___x_2376_, v___x_2377_, v___f_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object* v___f_2380_, lean_object* v___f_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2380_, v___f_2381_, v___y_2382_);
lean_dec(v___y_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object* v_producers_2385_, uint8_t v_closed_2386_, lean_object* v___y_2387_, lean_object* v_x_2388_){
_start:
{
if (lean_obj_tag(v_x_2388_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v_producers_2385_);
v_a_2390_ = lean_ctor_get(v_x_2388_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_x_2388_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2392_ = v_x_2388_;
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v_x_2388_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_a_2399_ = lean_ctor_get(v_x_2388_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v_x_2388_, 1);
v___x_2400_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2400_, 0, v_producers_2385_);
lean_ctor_set(v___x_2400_, 1, v_a_2399_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*2, v_closed_2386_);
v___x_2401_ = lean_st_ref_swap(v___y_2387_, v___x_2400_);
lean_dec(v___x_2401_);
v___x_2402_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object* v_producers_2403_, lean_object* v_closed_2404_, lean_object* v___y_2405_, lean_object* v_x_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v_closed_boxed_2408_; lean_object* v_res_2409_; 
v_closed_boxed_2408_ = lean_unbox(v_closed_2404_);
v_res_2409_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2403_, v_closed_boxed_2408_, v___y_2405_, v_x_2406_);
lean_dec(v___y_2405_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_2410_, lean_object* v_x_2411_, lean_object* v_head_2412_, lean_object* v_x_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2410_, v_x_2411_, v_head_2412_, v_x_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object* v_x_2416_, lean_object* v_x_2417_){
_start:
{
if (lean_obj_tag(v_x_2416_) == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2419_, 0, v_x_2417_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
else
{
lean_object* v_head_2421_; lean_object* v_tail_2422_; lean_object* v___f_2423_; lean_object* v_val_2425_; 
v_head_2421_ = lean_ctor_get(v_x_2416_, 0);
lean_inc_n(v_head_2421_, 2);
v_tail_2422_ = lean_ctor_get(v_x_2416_, 1);
lean_inc(v_tail_2422_);
lean_dec_ref_known(v_x_2416_, 2);
v___f_2423_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2423_, 0, v_tail_2422_);
lean_closure_set(v___f_2423_, 1, v_x_2417_);
lean_closure_set(v___f_2423_, 2, v_head_2421_);
if (lean_obj_tag(v_head_2421_) == 0)
{
lean_object* v___x_2429_; 
lean_dec_ref_known(v_head_2421_, 1);
v___x_2429_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_2425_ = v___x_2429_;
goto v___jp_2424_;
}
else
{
lean_object* v_finished_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2444_; 
v_finished_2430_ = lean_ctor_get(v_head_2421_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_head_2421_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2432_ = v_head_2421_;
v_isShared_2433_ = v_isSharedCheck_2444_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_finished_2430_);
lean_dec(v_head_2421_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2444_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_finished_2434_; lean_object* v___x_2435_; lean_object* v___f_2436_; lean_object* v___x_2438_; 
v_finished_2434_ = lean_ctor_get(v_finished_2430_, 0);
lean_inc(v_finished_2434_);
lean_dec_ref(v_finished_2430_);
v___x_2435_ = lean_st_ref_get(v_finished_2434_);
lean_dec(v_finished_2434_);
v___f_2436_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2435_);
v___x_2438_ = v___x_2432_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2435_);
v___x_2438_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; 
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = 0;
v___x_2442_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2440_, v___x_2441_, v___x_2439_, v___f_2436_);
v_val_2425_ = v___x_2442_;
goto v___jp_2424_;
}
}
}
v___jp_2424_:
{
lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = 0;
v___x_2428_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2426_, v___x_2427_, v_val_2425_, v___f_2423_);
return v___x_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_2445_, lean_object* v_x_2446_, lean_object* v_head_2447_, lean_object* v_x_2448_){
_start:
{
if (lean_obj_tag(v_x_2448_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v_head_2447_);
lean_dec(v_x_2446_);
lean_dec(v_tail_2445_);
v_a_2450_ = lean_ctor_get(v_x_2448_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_x_2448_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2452_ = v_x_2448_;
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v_x_2448_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
}
}
else
{
lean_object* v_a_2459_; uint8_t v___x_2460_; 
v_a_2459_ = lean_ctor_get(v_x_2448_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v_x_2448_, 1);
v___x_2460_ = lean_unbox(v_a_2459_);
lean_dec(v_a_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
lean_dec_ref(v_head_2447_);
v___x_2461_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2445_, v_x_2446_);
return v___x_2461_;
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_head_2447_);
lean_ctor_set(v___x_2462_, 1, v_x_2446_);
v___x_2463_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2445_, v___x_2462_);
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object* v_x_2464_, lean_object* v_x_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2464_, v_x_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object* v_eList_2468_, lean_object* v___x_2469_, lean_object* v___f_2470_, lean_object* v_x_2471_){
_start:
{
if (lean_obj_tag(v_x_2471_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v___f_2470_);
lean_dec(v___x_2469_);
lean_dec(v_eList_2468_);
v_a_2473_ = lean_ctor_get(v_x_2471_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_x_2471_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2475_ = v_x_2471_;
v_isShared_2476_ = v_isSharedCheck_2481_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v_x_2471_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2481_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; 
v_a_2482_ = lean_ctor_get(v_x_2471_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v_x_2471_, 1);
lean_inc(v___x_2469_);
v___x_2483_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_2468_, v___x_2469_);
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = 0;
v___x_2486_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2484_, v___x_2485_, v___x_2483_, v___f_2470_);
v___f_2487_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2487_, 0, v_a_2482_);
lean_closure_set(v___f_2487_, 1, v___x_2469_);
v___x_2488_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2484_, v___x_2485_, v___x_2486_, v___f_2487_);
return v___x_2488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_eList_2489_, lean_object* v___x_2490_, lean_object* v___f_2491_, lean_object* v_x_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v_eList_2489_, v___x_2490_, v___f_2491_, v_x_2492_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object* v_q_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_eList_2498_; lean_object* v_dList_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___f_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; 
v_eList_2498_ = lean_ctor_get(v_q_2495_, 0);
lean_inc(v_eList_2498_);
v_dList_2499_ = lean_ctor_get(v_q_2495_, 1);
lean_inc(v_dList_2499_);
lean_dec_ref(v_q_2495_);
v___x_2500_ = lean_box(0);
v___x_2501_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_2499_, v___x_2500_);
v___f_2502_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = 0;
v___x_2505_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2503_, v___x_2504_, v___x_2501_, v___f_2502_);
v___f_2506_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2506_, 0, v_eList_2498_);
lean_closure_set(v___f_2506_, 1, v___x_2500_);
lean_closure_set(v___f_2506_, 2, v___f_2502_);
v___x_2507_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2503_, v___x_2504_, v___x_2505_, v___f_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object* v_q_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2508_, v___y_2509_);
lean_dec(v___y_2509_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object* v___y_2512_, lean_object* v_x_2513_){
_start:
{
if (lean_obj_tag(v_x_2513_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2523_; 
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
lean_object* v_a_2524_; lean_object* v_producers_2525_; lean_object* v_consumers_2526_; uint8_t v_closed_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___f_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; 
v_a_2524_ = lean_ctor_get(v_x_2513_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v_x_2513_, 1);
v_producers_2525_ = lean_ctor_get(v_a_2524_, 0);
lean_inc_ref(v_producers_2525_);
v_consumers_2526_ = lean_ctor_get(v_a_2524_, 1);
lean_inc_ref(v_consumers_2526_);
v_closed_2527_ = lean_ctor_get_uint8(v_a_2524_, sizeof(void*)*2);
lean_dec(v_a_2524_);
v___x_2528_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_2526_, v___y_2512_);
v___x_2529_ = lean_box(v_closed_2527_);
lean_inc(v___y_2512_);
v___f_2530_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2530_, 0, v_producers_2525_);
lean_closure_set(v___f_2530_, 1, v___x_2529_);
lean_closure_set(v___f_2530_, 2, v___y_2512_);
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = 0;
v___x_2533_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2531_, v___x_2532_, v___x_2528_, v___f_2530_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object* v___y_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2534_, v_x_2535_);
lean_dec(v___y_2534_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; lean_object* v___f_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2540_ = lean_st_ref_get(v___y_2538_);
lean_inc(v___y_2538_);
v___f_2541_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2541_, 0, v___y_2538_);
v___x_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = 0;
v___x_2546_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2544_, v___x_2545_, v___x_2543_, v___f_2541_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2547_);
lean_dec(v___y_2547_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object* v_ch_2555_){
_start:
{
lean_object* v___f_2556_; lean_object* v___f_2557_; lean_object* v___f_2558_; lean_object* v___f_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___f_2556_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0));
lean_inc_ref_n(v_ch_2555_, 2);
v___f_2557_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2557_, 0, v___f_2556_);
lean_closure_set(v___f_2557_, 1, v_ch_2555_);
v___f_2558_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1));
v___f_2559_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2));
v___x_2560_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2560_, 0, lean_box(0));
lean_closure_set(v___x_2560_, 1, lean_box(0));
lean_closure_set(v___x_2560_, 2, v_ch_2555_);
lean_closure_set(v___x_2560_, 3, v___f_2558_);
v___x_2561_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2561_, 0, lean_box(0));
lean_closure_set(v___x_2561_, 1, lean_box(0));
lean_closure_set(v___x_2561_, 2, v_ch_2555_);
lean_closure_set(v___x_2561_, 3, v___f_2559_);
v___x_2562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2560_);
lean_ctor_set(v___x_2562_, 1, v___f_2557_);
lean_ctor_set(v___x_2562_, 2, v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object* v_00_u03b1_2563_, lean_object* v_ch_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object* v_00_u03b1_2566_, lean_object* v_q_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2567_, v___y_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_2571_, lean_object* v_q_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_2571_, v_q_2572_, v___y_2573_);
lean_dec(v___y_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object* v_00_u03b1_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2577_, v_x_2578_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_2582_, v_x_2583_, v_x_2584_, v___y_2585_);
lean_dec(v___y_2585_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object* v_c_2588_, uint8_t v_b_2589_){
_start:
{
lean_object* v_promise_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v_promise_2591_ = lean_ctor_get(v_c_2588_, 0);
v___x_2592_ = lean_box(v_b_2589_);
v___x_2593_ = lean_io_promise_resolve(v___x_2592_, v_promise_2591_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object* v_c_2594_, lean_object* v_b_2595_, lean_object* v_a_2596_){
_start:
{
uint8_t v_b_boxed_2597_; lean_object* v_res_2598_; 
v_b_boxed_2597_ = lean_unbox(v_b_2595_);
v_res_2598_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2594_, v_b_boxed_2597_);
lean_dec_ref(v_c_2594_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object* v_00_u03b1_2599_, lean_object* v_c_2600_, uint8_t v_b_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2600_, v_b_2601_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object* v_00_u03b1_2604_, lean_object* v_c_2605_, lean_object* v_b_2606_, lean_object* v_a_2607_){
_start:
{
uint8_t v_b_boxed_2608_; lean_object* v_res_2609_; 
v_b_boxed_2608_ = lean_unbox(v_b_2606_);
v_res_2609_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(v_00_u03b1_2604_, v_c_2605_, v_b_boxed_2608_);
lean_dec_ref(v_c_2605_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object* v_x_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_st_mk_ref(v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2614_);
lean_dec(v_x_2614_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object* v_n_2617_, lean_object* v_f_2618_, lean_object* v_xs_2619_, lean_object* v_k_2620_, lean_object* v_acc_2621_){
_start:
{
uint8_t v___x_2623_; 
v___x_2623_ = lean_nat_dec_lt(v_k_2620_, v_n_2617_);
if (v___x_2623_ == 0)
{
lean_dec(v_k_2620_);
lean_dec_ref(v_f_2618_);
return v_acc_2621_;
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2624_ = lean_array_fget_borrowed(v_xs_2619_, v_k_2620_);
lean_inc_ref(v_f_2618_);
lean_inc(v___x_2624_);
v___x_2625_ = lean_apply_2(v_f_2618_, v___x_2624_, lean_box(0));
v___x_2626_ = lean_unsigned_to_nat(1u);
v___x_2627_ = lean_nat_add(v_k_2620_, v___x_2626_);
lean_dec(v_k_2620_);
v___x_2628_ = lean_array_push(v_acc_2621_, v___x_2625_);
v_k_2620_ = v___x_2627_;
v_acc_2621_ = v___x_2628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_2630_, lean_object* v_f_2631_, lean_object* v_xs_2632_, lean_object* v_k_2633_, lean_object* v_acc_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2630_, v_f_2631_, v_xs_2632_, v_k_2633_, v_acc_2634_);
lean_dec_ref(v_xs_2632_);
lean_dec(v_n_2630_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object* v_capacity_2640_){
_start:
{
lean_object* v___f_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___f_2642_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0));
lean_inc(v_capacity_2640_);
v___x_2643_ = l_Array_range(v_capacity_2640_);
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1));
v___x_2646_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_2640_, v___f_2642_, v___x_2643_, v___x_2644_, v___x_2645_);
lean_dec_ref(v___x_2643_);
v___x_2647_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2648_ = 0;
v___x_2649_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2647_);
lean_ctor_set(v___x_2649_, 2, v_capacity_2640_);
lean_ctor_set(v___x_2649_, 3, v___x_2646_);
lean_ctor_set(v___x_2649_, 4, v___x_2644_);
lean_ctor_set(v___x_2649_, 5, v___x_2644_);
lean_ctor_set(v___x_2649_, 6, v___x_2644_);
lean_ctor_set_uint8(v___x_2649_, sizeof(void*)*7, v___x_2648_);
v___x_2650_ = l_Std_Mutex_new___redArg(v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object* v_capacity_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2651_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object* v_00_u03b1_2654_, lean_object* v_capacity_2655_, lean_object* v_hcap_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2655_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object* v_00_u03b1_2659_, lean_object* v_capacity_2660_, lean_object* v_hcap_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(v_00_u03b1_2659_, v_capacity_2660_, v_hcap_2661_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object* v_00_u03b1_2664_, lean_object* v_00_u03b2_2665_, lean_object* v_n_2666_, lean_object* v_f_2667_, lean_object* v_xs_2668_, lean_object* v_k_2669_, lean_object* v_h_2670_, lean_object* v_acc_2671_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2666_, v_f_2667_, v_xs_2668_, v_k_2669_, v_acc_2671_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_2674_, lean_object* v_00_u03b2_2675_, lean_object* v_n_2676_, lean_object* v_f_2677_, lean_object* v_xs_2678_, lean_object* v_k_2679_, lean_object* v_h_2680_, lean_object* v_acc_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_2674_, v_00_u03b2_2675_, v_n_2676_, v_f_2677_, v_xs_2678_, v_k_2679_, v_h_2680_, v_acc_2681_);
lean_dec_ref(v_xs_2678_);
lean_dec(v_n_2676_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object* v_idx_2684_, lean_object* v_cap_2685_){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2686_ = lean_unsigned_to_nat(1u);
v___x_2687_ = lean_nat_add(v_idx_2684_, v___x_2686_);
v___x_2688_ = lean_nat_dec_eq(v___x_2687_, v_cap_2685_);
if (v___x_2688_ == 0)
{
return v___x_2687_;
}
else
{
lean_object* v___x_2689_; 
lean_dec(v___x_2687_);
v___x_2689_ = lean_unsigned_to_nat(0u);
return v___x_2689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object* v_idx_2690_, lean_object* v_cap_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(v_idx_2690_, v_cap_2691_);
lean_dec(v_cap_2691_);
lean_dec(v_idx_2690_);
return v_res_2692_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object* v_v_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_st_2697_; lean_object* v___y_2698_; lean_object* v___x_2701_; lean_object* v_producers_2702_; lean_object* v_consumers_2703_; lean_object* v_capacity_2704_; lean_object* v_buf_2705_; lean_object* v_bufCount_2706_; lean_object* v_sendIdx_2707_; lean_object* v_recvIdx_2708_; uint8_t v_closed_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2735_; 
v___x_2701_ = lean_st_ref_get(v_a_2694_);
v_producers_2702_ = lean_ctor_get(v___x_2701_, 0);
v_consumers_2703_ = lean_ctor_get(v___x_2701_, 1);
v_capacity_2704_ = lean_ctor_get(v___x_2701_, 2);
v_buf_2705_ = lean_ctor_get(v___x_2701_, 3);
v_bufCount_2706_ = lean_ctor_get(v___x_2701_, 4);
v_sendIdx_2707_ = lean_ctor_get(v___x_2701_, 5);
v_recvIdx_2708_ = lean_ctor_get(v___x_2701_, 6);
v_closed_2709_ = lean_ctor_get_uint8(v___x_2701_, sizeof(void*)*7);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2711_ = v___x_2701_;
v_isShared_2712_ = v_isSharedCheck_2735_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_recvIdx_2708_);
lean_inc(v_sendIdx_2707_);
lean_inc(v_bufCount_2706_);
lean_inc(v_buf_2705_);
lean_inc(v_capacity_2704_);
lean_inc(v_consumers_2703_);
lean_inc(v_producers_2702_);
lean_dec(v___x_2701_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2735_;
goto v_resetjp_2710_;
}
v___jp_2696_:
{
lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = lean_st_ref_swap(v___y_2698_, v_st_2697_);
lean_dec(v___x_2699_);
v___x_2700_ = 1;
return v___x_2700_;
}
v_resetjp_2710_:
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_nat_dec_eq(v_bufCount_2706_, v_capacity_2704_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___y_2720_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2714_ = lean_array_fget_borrowed(v_buf_2705_, v_sendIdx_2707_);
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v_v_2693_);
v___x_2716_ = lean_st_ref_swap(v___x_2714_, v___x_2715_);
lean_dec(v___x_2716_);
v___x_2717_ = lean_unsigned_to_nat(1u);
v___x_2718_ = lean_nat_add(v_bufCount_2706_, v___x_2717_);
lean_dec(v_bufCount_2706_);
v___x_2731_ = lean_nat_add(v_sendIdx_2707_, v___x_2717_);
lean_dec(v_sendIdx_2707_);
v___x_2732_ = lean_nat_dec_eq(v___x_2731_, v_capacity_2704_);
if (v___x_2732_ == 0)
{
v___y_2720_ = v___x_2731_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2733_; 
lean_dec(v___x_2731_);
v___x_2733_ = lean_unsigned_to_nat(0u);
v___y_2720_ = v___x_2733_;
goto v___jp_2719_;
}
v___jp_2719_:
{
lean_object* v___x_2722_; 
lean_inc(v_recvIdx_2708_);
lean_inc(v___y_2720_);
lean_inc(v___x_2718_);
lean_inc_ref(v_buf_2705_);
lean_inc(v_capacity_2704_);
lean_inc_ref(v_consumers_2703_);
lean_inc_ref(v_producers_2702_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 5, v___y_2720_);
lean_ctor_set(v___x_2711_, 4, v___x_2718_);
v___x_2722_ = v___x_2711_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_producers_2702_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_consumers_2703_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_capacity_2704_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_buf_2705_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2730_, 5, v___y_2720_);
lean_ctor_set(v_reuseFailAlloc_2730_, 6, v_recvIdx_2708_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*7, v_closed_2709_);
v___x_2722_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_2703_);
if (lean_obj_tag(v___x_2723_) == 1)
{
lean_object* v_val_2724_; lean_object* v_fst_2725_; lean_object* v_snd_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec_ref(v___x_2722_);
v_val_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_val_2724_);
lean_dec_ref_known(v___x_2723_, 1);
v_fst_2725_ = lean_ctor_get(v_val_2724_, 0);
lean_inc(v_fst_2725_);
v_snd_2726_ = lean_ctor_get(v_val_2724_, 1);
lean_inc(v_snd_2726_);
lean_dec(v_val_2724_);
v___x_2727_ = 1;
v___x_2728_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_2725_, v___x_2727_);
lean_dec(v_fst_2725_);
v___x_2729_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2729_, 0, v_producers_2702_);
lean_ctor_set(v___x_2729_, 1, v_snd_2726_);
lean_ctor_set(v___x_2729_, 2, v_capacity_2704_);
lean_ctor_set(v___x_2729_, 3, v_buf_2705_);
lean_ctor_set(v___x_2729_, 4, v___x_2718_);
lean_ctor_set(v___x_2729_, 5, v___y_2720_);
lean_ctor_set(v___x_2729_, 6, v_recvIdx_2708_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*7, v_closed_2709_);
v_st_2697_ = v___x_2729_;
v___y_2698_ = v_a_2694_;
goto v___jp_2696_;
}
else
{
lean_dec(v___x_2723_);
lean_dec(v___y_2720_);
lean_dec(v___x_2718_);
lean_dec(v_recvIdx_2708_);
lean_dec_ref(v_buf_2705_);
lean_dec(v_capacity_2704_);
lean_dec_ref(v_producers_2702_);
v_st_2697_ = v___x_2722_;
v___y_2698_ = v_a_2694_;
goto v___jp_2696_;
}
}
}
}
else
{
uint8_t v___x_2734_; 
lean_del_object(v___x_2711_);
lean_dec(v_recvIdx_2708_);
lean_dec(v_sendIdx_2707_);
lean_dec(v_bufCount_2706_);
lean_dec_ref(v_buf_2705_);
lean_dec(v_capacity_2704_);
lean_dec_ref(v_consumers_2703_);
lean_dec_ref(v_producers_2702_);
lean_dec(v_v_2693_);
v___x_2734_ = 0;
return v___x_2734_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
uint8_t v_res_2739_; lean_object* v_r_2740_; 
v_res_2739_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2736_, v_a_2737_);
lean_dec(v_a_2737_);
v_r_2740_ = lean_box(v_res_2739_);
return v_r_2740_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object* v_00_u03b1_2741_, lean_object* v_v_2742_, lean_object* v_a_2743_){
_start:
{
uint8_t v___x_2745_; 
v___x_2745_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2742_, v_a_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_2746_, lean_object* v_v_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
uint8_t v_res_2750_; lean_object* v_r_2751_; 
v_res_2750_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(v_00_u03b1_2746_, v_v_2747_, v_a_2748_);
lean_dec(v_a_2748_);
v_r_2751_ = lean_box(v_res_2750_);
return v_r_2751_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object* v_v_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; uint8_t v_closed_2756_; 
v___x_2755_ = lean_st_ref_get(v___y_2753_);
v_closed_2756_ = lean_ctor_get_uint8(v___x_2755_, sizeof(void*)*7);
lean_dec(v___x_2755_);
if (v_closed_2756_ == 0)
{
uint8_t v___x_2757_; 
v___x_2757_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2752_, v___y_2753_);
return v___x_2757_;
}
else
{
uint8_t v___x_2758_; 
lean_dec(v_v_2752_);
v___x_2758_ = 0;
return v___x_2758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v_res_2762_; lean_object* v_r_2763_; 
v_res_2762_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2759_, v___y_2760_);
lean_dec(v___y_2760_);
v_r_2763_ = lean_box(v_res_2762_);
return v_r_2763_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object* v_ch_2764_, lean_object* v_v_2765_){
_start:
{
lean_object* v___f_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___f_2767_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2767_, 0, v_v_2765_);
v___x_2768_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2764_, v___f_2767_);
v___x_2769_ = lean_unbox(v___x_2768_);
lean_dec(v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object* v_ch_2770_, lean_object* v_v_2771_, lean_object* v_a_2772_){
_start:
{
uint8_t v_res_2773_; lean_object* v_r_2774_; 
v_res_2773_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2770_, v_v_2771_);
v_r_2774_ = lean_box(v_res_2773_);
return v_r_2774_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object* v_00_u03b1_2775_, lean_object* v_ch_2776_, lean_object* v_v_2777_){
_start:
{
uint8_t v___x_2779_; 
v___x_2779_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2776_, v_v_2777_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(lean_object* v_00_u03b1_2780_, lean_object* v_ch_2781_, lean_object* v_v_2782_, lean_object* v_a_2783_){
_start:
{
uint8_t v_res_2784_; lean_object* v_r_2785_; 
v_res_2784_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(v_00_u03b1_2780_, v_ch_2781_, v_v_2782_);
v_r_2785_ = lean_box(v_res_2784_);
return v_r_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(lean_object* v_v_2786_, lean_object* v___f_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; uint8_t v_closed_2791_; 
v___x_2790_ = lean_st_ref_get(v___y_2788_);
v_closed_2791_ = lean_ctor_get_uint8(v___x_2790_, sizeof(void*)*7);
lean_dec(v___x_2790_);
if (v_closed_2791_ == 0)
{
uint8_t v___x_2792_; 
v___x_2792_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2786_, v___y_2788_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v_producers_2795_; lean_object* v_consumers_2796_; lean_object* v_capacity_2797_; lean_object* v_buf_2798_; lean_object* v_bufCount_2799_; lean_object* v_sendIdx_2800_; lean_object* v_recvIdx_2801_; uint8_t v_closed_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2814_; 
v___x_2793_ = lean_io_promise_new();
v___x_2794_ = lean_st_ref_take(v___y_2788_);
v_producers_2795_ = lean_ctor_get(v___x_2794_, 0);
v_consumers_2796_ = lean_ctor_get(v___x_2794_, 1);
v_capacity_2797_ = lean_ctor_get(v___x_2794_, 2);
v_buf_2798_ = lean_ctor_get(v___x_2794_, 3);
v_bufCount_2799_ = lean_ctor_get(v___x_2794_, 4);
v_sendIdx_2800_ = lean_ctor_get(v___x_2794_, 5);
v_recvIdx_2801_ = lean_ctor_get(v___x_2794_, 6);
v_closed_2802_ = lean_ctor_get_uint8(v___x_2794_, sizeof(void*)*7);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2804_ = v___x_2794_;
v_isShared_2805_ = v_isSharedCheck_2814_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_recvIdx_2801_);
lean_inc(v_sendIdx_2800_);
lean_inc(v_bufCount_2799_);
lean_inc(v_buf_2798_);
lean_inc(v_capacity_2797_);
lean_inc(v_consumers_2796_);
lean_inc(v_producers_2795_);
lean_dec(v___x_2794_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2814_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_inc(v___x_2793_);
v___x_2806_ = l_Std_Queue_enqueue___redArg(v___x_2793_, v_producers_2795_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2806_);
v___x_2808_ = v___x_2804_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_consumers_2796_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_capacity_2797_);
lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_buf_2798_);
lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_bufCount_2799_);
lean_ctor_set(v_reuseFailAlloc_2813_, 5, v_sendIdx_2800_);
lean_ctor_set(v_reuseFailAlloc_2813_, 6, v_recvIdx_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, sizeof(void*)*7, v_closed_2802_);
v___x_2808_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2809_ = lean_st_ref_put(v___y_2788_, v___x_2808_);
v___x_2810_ = lean_io_promise_result_opt(v___x_2793_);
lean_dec(v___x_2793_);
v___x_2811_ = lean_unsigned_to_nat(0u);
v___x_2812_ = lean_io_bind_task(v___x_2810_, v___f_2787_, v___x_2811_, v___x_2792_);
return v___x_2812_;
}
}
}
else
{
lean_object* v___x_2815_; 
lean_dec_ref(v___f_2787_);
v___x_2815_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_2815_;
}
}
else
{
lean_object* v___x_2816_; 
lean_dec_ref(v___f_2787_);
lean_dec(v_v_2786_);
v___x_2816_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_2817_, lean_object* v___f_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(v_v_2817_, v___f_2818_, v___y_2819_);
lean_dec(v___y_2819_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(lean_object* v_ch_2822_, lean_object* v_v_2823_, lean_object* v_res_2824_){
_start:
{
if (lean_obj_tag(v_res_2824_) == 0)
{
lean_dec(v_v_2823_);
lean_dec_ref(v_ch_2822_);
goto v___jp_2826_;
}
else
{
lean_object* v_val_2828_; uint8_t v___x_2829_; 
v_val_2828_ = lean_ctor_get(v_res_2824_, 0);
v___x_2829_ = lean_unbox(v_val_2828_);
if (v___x_2829_ == 0)
{
lean_dec(v_v_2823_);
lean_dec_ref(v_ch_2822_);
goto v___jp_2826_;
}
else
{
lean_object* v___x_2830_; 
v___x_2830_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2822_, v_v_2823_);
return v___x_2830_;
}
}
v___jp_2826_:
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_2831_, lean_object* v_v_2832_, lean_object* v_res_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(v_ch_2831_, v_v_2832_, v_res_2833_);
lean_dec(v_res_2833_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(lean_object* v_ch_2836_, lean_object* v_v_2837_){
_start:
{
lean_object* v___f_2839_; lean_object* v___f_2840_; lean_object* v___x_2841_; 
lean_inc(v_v_2837_);
lean_inc_ref(v_ch_2836_);
v___f_2839_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2839_, 0, v_ch_2836_);
lean_closure_set(v___f_2839_, 1, v_v_2837_);
v___f_2840_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2840_, 0, v_v_2837_);
lean_closure_set(v___f_2840_, 1, v___f_2839_);
v___x_2841_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2836_, v___f_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(lean_object* v_ch_2842_, lean_object* v_v_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2842_, v_v_2843_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_object* v_00_u03b1_2846_, lean_object* v_ch_2847_, lean_object* v_v_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2847_, v_v_2848_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(lean_object* v_00_u03b1_2851_, lean_object* v_ch_2852_, lean_object* v_v_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(v_00_u03b1_2851_, v_ch_2852_, v_v_2853_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t v___x_2856_, lean_object* v_as_2857_, size_t v_sz_2858_, size_t v_i_2859_, lean_object* v_b_2860_){
_start:
{
uint8_t v___x_2862_; 
v___x_2862_ = lean_usize_dec_lt(v_i_2859_, v_sz_2858_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; 
v___x_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2863_, 0, v_b_2860_);
return v___x_2863_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; size_t v___x_2867_; size_t v___x_2868_; 
v_a_2864_ = lean_array_uget_borrowed(v_as_2857_, v_i_2859_);
v___x_2865_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_2864_, v___x_2856_);
v___x_2866_ = lean_box(0);
v___x_2867_ = ((size_t)1ULL);
v___x_2868_ = lean_usize_add(v_i_2859_, v___x_2867_);
v_i_2859_ = v___x_2868_;
v_b_2860_ = v___x_2866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_2870_, lean_object* v_as_2871_, lean_object* v_sz_2872_, lean_object* v_i_2873_, lean_object* v_b_2874_, lean_object* v___y_2875_){
_start:
{
uint8_t v___x_1154__boxed_2876_; size_t v_sz_boxed_2877_; size_t v_i_boxed_2878_; lean_object* v_res_2879_; 
v___x_1154__boxed_2876_ = lean_unbox(v___x_2870_);
v_sz_boxed_2877_ = lean_unbox_usize(v_sz_2872_);
lean_dec(v_sz_2872_);
v_i_boxed_2878_ = lean_unbox_usize(v_i_2873_);
lean_dec(v_i_2873_);
v_res_2879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1154__boxed_2876_, v_as_2871_, v_sz_boxed_2877_, v_i_boxed_2878_, v_b_2874_);
lean_dec_ref(v_as_2871_);
return v_res_2879_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Std_Queue_empty(lean_box(0));
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2883_; uint8_t v_closed_2884_; 
v___x_2883_ = lean_st_ref_get(v___y_2881_);
v_closed_2884_ = lean_ctor_get_uint8(v___x_2883_, sizeof(void*)*7);
if (v_closed_2884_ == 0)
{
lean_object* v_producers_2885_; lean_object* v_consumers_2886_; lean_object* v_capacity_2887_; lean_object* v_buf_2888_; lean_object* v_bufCount_2889_; lean_object* v_sendIdx_2890_; lean_object* v_recvIdx_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2914_; 
v_producers_2885_ = lean_ctor_get(v___x_2883_, 0);
v_consumers_2886_ = lean_ctor_get(v___x_2883_, 1);
v_capacity_2887_ = lean_ctor_get(v___x_2883_, 2);
v_buf_2888_ = lean_ctor_get(v___x_2883_, 3);
v_bufCount_2889_ = lean_ctor_get(v___x_2883_, 4);
v_sendIdx_2890_ = lean_ctor_get(v___x_2883_, 5);
v_recvIdx_2891_ = lean_ctor_get(v___x_2883_, 6);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2893_ = v___x_2883_;
v_isShared_2894_ = v_isSharedCheck_2914_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_recvIdx_2891_);
lean_inc(v_sendIdx_2890_);
lean_inc(v_bufCount_2889_);
lean_inc(v_buf_2888_);
lean_inc(v_capacity_2887_);
lean_inc(v_consumers_2886_);
lean_inc(v_producers_2885_);
lean_dec(v___x_2883_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2914_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; size_t v_sz_2897_; size_t v___x_2898_; lean_object* v___x_2899_; 
v___x_2895_ = l_Std_Queue_toArray___redArg(v_consumers_2886_);
v___x_2896_ = lean_box(0);
v_sz_2897_ = lean_array_size(v___x_2895_);
v___x_2898_ = ((size_t)0ULL);
v___x_2899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_2884_, v___x_2895_, v_sz_2897_, v___x_2898_, v___x_2896_);
lean_dec_ref(v___x_2895_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2912_; 
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; 
v_unused_2913_ = lean_ctor_get(v___x_2899_, 0);
lean_dec(v_unused_2913_);
v___x_2901_ = v___x_2899_;
v_isShared_2902_ = v_isSharedCheck_2912_;
goto v_resetjp_2900_;
}
else
{
lean_dec(v___x_2899_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2912_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2906_; 
v___x_2903_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0);
v___x_2904_ = 1;
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 1, v___x_2903_);
v___x_2906_ = v___x_2893_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_producers_2885_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2911_, 2, v_capacity_2887_);
lean_ctor_set(v_reuseFailAlloc_2911_, 3, v_buf_2888_);
lean_ctor_set(v_reuseFailAlloc_2911_, 4, v_bufCount_2889_);
lean_ctor_set(v_reuseFailAlloc_2911_, 5, v_sendIdx_2890_);
lean_ctor_set(v_reuseFailAlloc_2911_, 6, v_recvIdx_2891_);
v___x_2906_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*7, v___x_2904_);
v___x_2907_ = lean_st_ref_swap(v___y_2881_, v___x_2906_);
lean_dec(v___x_2907_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2896_);
v___x_2909_ = v___x_2901_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2896_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_del_object(v___x_2893_);
lean_dec(v_recvIdx_2891_);
lean_dec(v_sendIdx_2890_);
lean_dec(v_bufCount_2889_);
lean_dec_ref(v_buf_2888_);
lean_dec(v_capacity_2887_);
lean_dec_ref(v_producers_2885_);
return v___x_2899_;
}
}
}
else
{
uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_dec(v___x_2883_);
v___x_2915_ = 1;
v___x_2916_ = lean_box(v___x_2915_);
v___x_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
return v___x_2917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_2918_);
lean_dec(v___y_2918_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_2922_){
_start:
{
lean_object* v___f_2924_; lean_object* v___x_2925_; 
v___f_2924_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_2925_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_2922_, v___f_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2926_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_2929_, lean_object* v_ch_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2930_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_2933_, lean_object* v_ch_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_2933_, v_ch_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_2937_, uint8_t v___x_2938_, lean_object* v_as_2939_, size_t v_sz_2940_, size_t v_i_2941_, lean_object* v_b_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_2938_, v_as_2939_, v_sz_2940_, v_i_2941_, v_b_2942_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_2946_, lean_object* v___x_2947_, lean_object* v_as_2948_, lean_object* v_sz_2949_, lean_object* v_i_2950_, lean_object* v_b_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
uint8_t v___x_1252__boxed_2954_; size_t v_sz_boxed_2955_; size_t v_i_boxed_2956_; lean_object* v_res_2957_; 
v___x_1252__boxed_2954_ = lean_unbox(v___x_2947_);
v_sz_boxed_2955_ = lean_unbox_usize(v_sz_2949_);
lean_dec(v_sz_2949_);
v_i_boxed_2956_ = lean_unbox_usize(v_i_2950_);
lean_dec(v_i_2950_);
v_res_2957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_2946_, v___x_1252__boxed_2954_, v_as_2948_, v_sz_boxed_2955_, v_i_boxed_2956_, v_b_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v_as_2948_);
return v_res_2957_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_2958_){
_start:
{
lean_object* v___x_2960_; uint8_t v_closed_2961_; 
v___x_2960_ = lean_st_ref_get(v___y_2958_);
v_closed_2961_ = lean_ctor_get_uint8(v___x_2960_, sizeof(void*)*7);
lean_dec(v___x_2960_);
return v_closed_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
uint8_t v_res_2964_; lean_object* v_r_2965_; 
v_res_2964_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_2962_);
lean_dec(v___y_2962_);
v_r_2965_ = lean_box(v_res_2964_);
return v_r_2965_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_2967_){
_start:
{
lean_object* v___f_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___f_2969_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_2970_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2967_, v___f_2969_);
v___x_2971_ = lean_unbox(v___x_2970_);
lean_dec(v___x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_2972_, lean_object* v_a_2973_){
_start:
{
uint8_t v_res_2974_; lean_object* v_r_2975_; 
v_res_2974_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_2972_);
v_r_2975_ = lean_box(v_res_2974_);
return v_r_2975_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_2976_, lean_object* v_ch_2977_){
_start:
{
uint8_t v___x_2979_; 
v___x_2979_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_2977_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_2980_, lean_object* v_ch_2981_, lean_object* v_a_2982_){
_start:
{
uint8_t v_res_2983_; lean_object* v_r_2984_; 
v_res_2983_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_2980_, v_ch_2981_);
v_r_2984_ = lean_box(v_res_2983_);
return v_r_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_toPure_2988_; lean_object* v___x_2989_; 
v_toPure_2988_ = lean_ctor_get(v_toApplicative_2985_, 1);
lean_inc(v_toPure_2988_);
lean_dec_ref(v_toApplicative_2985_);
v___x_2989_ = lean_apply_2(v_toPure_2988_, lean_box(0), v_a_2986_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_2990_, lean_object* v_toBind_2991_, lean_object* v___f_2992_, lean_object* v_____r_2993_, lean_object* v_st_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_inc(v___y_2995_);
v___x_2996_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_2996_, 0, lean_box(0));
lean_closure_set(v___x_2996_, 1, lean_box(0));
lean_closure_set(v___x_2996_, 2, v___y_2995_);
lean_closure_set(v___x_2996_, 3, v_st_2994_);
v___x_2997_ = lean_apply_2(v_inst_2990_, lean_box(0), v___x_2996_);
v___x_2998_ = lean_apply_4(v_toBind_2991_, lean_box(0), lean_box(0), v___x_2997_, v___f_2992_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_inst_2999_, lean_object* v_toBind_3000_, lean_object* v___f_3001_, lean_object* v_____r_3002_, lean_object* v_st_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_2999_, v_toBind_3000_, v___f_3001_, v_____r_3002_, v_st_3003_, v___y_3004_);
lean_dec(v___y_3004_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_3006_, lean_object* v_consumers_3007_, lean_object* v_capacity_3008_, lean_object* v_buf_3009_, lean_object* v___x_3010_, lean_object* v_sendIdx_3011_, lean_object* v___y_3012_, uint8_t v_closed_3013_, lean_object* v___f_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3017_, 0, v_snd_3006_);
lean_ctor_set(v___x_3017_, 1, v_consumers_3007_);
lean_ctor_set(v___x_3017_, 2, v_capacity_3008_);
lean_ctor_set(v___x_3017_, 3, v_buf_3009_);
lean_ctor_set(v___x_3017_, 4, v___x_3010_);
lean_ctor_set(v___x_3017_, 5, v_sendIdx_3011_);
lean_ctor_set(v___x_3017_, 6, v___y_3012_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*7, v_closed_3013_);
v___x_3018_ = lean_box(0);
lean_inc(v_a_3015_);
v___x_3019_ = lean_apply_3(v___f_3014_, v___x_3018_, v___x_3017_, v_a_3015_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_3020_, lean_object* v_consumers_3021_, lean_object* v_capacity_3022_, lean_object* v_buf_3023_, lean_object* v___x_3024_, lean_object* v_sendIdx_3025_, lean_object* v___y_3026_, lean_object* v_closed_3027_, lean_object* v___f_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
uint8_t v_closed_boxed_3031_; lean_object* v_res_3032_; 
v_closed_boxed_3031_ = lean_unbox(v_closed_3027_);
v_res_3032_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3020_, v_consumers_3021_, v_capacity_3022_, v_buf_3023_, v___x_3024_, v_sendIdx_3025_, v___y_3026_, v_closed_boxed_3031_, v___f_3028_, v_a_3029_, v_a_3030_);
lean_dec(v_a_3029_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3033_, lean_object* v_inst_3034_, lean_object* v_toBind_3035_, lean_object* v_bufCount_3036_, lean_object* v_producers_3037_, lean_object* v_consumers_3038_, lean_object* v_capacity_3039_, lean_object* v_buf_3040_, lean_object* v_sendIdx_3041_, uint8_t v_closed_3042_, lean_object* v_a_3043_, uint8_t v___x_3044_, lean_object* v_inst_3045_, lean_object* v_recvIdx_3046_, lean_object* v___x_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___f_3049_; lean_object* v___f_3050_; lean_object* v___y_3052_; lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v___f_3049_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3049_, 0, v_toApplicative_3033_);
lean_closure_set(v___f_3049_, 1, v_a_3048_);
lean_inc_ref(v___f_3049_);
lean_inc(v_toBind_3035_);
lean_inc(v_inst_3034_);
v___f_3050_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3050_, 0, v_inst_3034_);
lean_closure_set(v___f_3050_, 1, v_toBind_3035_);
lean_closure_set(v___f_3050_, 2, v___f_3049_);
v___x_3068_ = lean_unsigned_to_nat(1u);
v___x_3069_ = lean_nat_add(v_recvIdx_3046_, v___x_3068_);
v___x_3070_ = lean_nat_dec_eq(v___x_3069_, v_capacity_3039_);
if (v___x_3070_ == 0)
{
lean_dec(v___x_3047_);
v___y_3052_ = v___x_3069_;
goto v___jp_3051_;
}
else
{
lean_dec(v___x_3069_);
v___y_3052_ = v___x_3047_;
goto v___jp_3051_;
}
v___jp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3053_ = lean_unsigned_to_nat(1u);
v___x_3054_ = lean_nat_sub(v_bufCount_3036_, v___x_3053_);
lean_inc(v___y_3052_);
lean_inc(v_sendIdx_3041_);
lean_inc(v___x_3054_);
lean_inc_ref(v_buf_3040_);
lean_inc(v_capacity_3039_);
lean_inc_ref(v_consumers_3038_);
lean_inc_ref(v_producers_3037_);
v___x_3055_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3055_, 0, v_producers_3037_);
lean_ctor_set(v___x_3055_, 1, v_consumers_3038_);
lean_ctor_set(v___x_3055_, 2, v_capacity_3039_);
lean_ctor_set(v___x_3055_, 3, v_buf_3040_);
lean_ctor_set(v___x_3055_, 4, v___x_3054_);
lean_ctor_set(v___x_3055_, 5, v_sendIdx_3041_);
lean_ctor_set(v___x_3055_, 6, v___y_3052_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*7, v_closed_3042_);
v___x_3056_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3037_);
if (lean_obj_tag(v___x_3056_) == 1)
{
lean_object* v_val_3057_; lean_object* v_fst_3058_; lean_object* v_snd_3059_; lean_object* v___x_3060_; lean_object* v___f_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec_ref_known(v___x_3055_, 7);
lean_dec_ref(v___f_3049_);
lean_dec(v_inst_3034_);
v_val_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v_fst_3058_ = lean_ctor_get(v_val_3057_, 0);
lean_inc(v_fst_3058_);
v_snd_3059_ = lean_ctor_get(v_val_3057_, 1);
lean_inc(v_snd_3059_);
lean_dec(v_val_3057_);
v___x_3060_ = lean_box(v_closed_3042_);
lean_inc(v_a_3043_);
v___f_3061_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3061_, 0, v_snd_3059_);
lean_closure_set(v___f_3061_, 1, v_consumers_3038_);
lean_closure_set(v___f_3061_, 2, v_capacity_3039_);
lean_closure_set(v___f_3061_, 3, v_buf_3040_);
lean_closure_set(v___f_3061_, 4, v___x_3054_);
lean_closure_set(v___f_3061_, 5, v_sendIdx_3041_);
lean_closure_set(v___f_3061_, 6, v___y_3052_);
lean_closure_set(v___f_3061_, 7, v___x_3060_);
lean_closure_set(v___f_3061_, 8, v___f_3050_);
lean_closure_set(v___f_3061_, 9, v_a_3043_);
v___x_3062_ = lean_box(v___x_3044_);
v___x_3063_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3063_, 0, lean_box(0));
lean_closure_set(v___x_3063_, 1, v___x_3062_);
lean_closure_set(v___x_3063_, 2, v_fst_3058_);
v___x_3064_ = lean_apply_2(v_inst_3045_, lean_box(0), v___x_3063_);
v___x_3065_ = lean_apply_4(v_toBind_3035_, lean_box(0), lean_box(0), v___x_3064_, v___f_3061_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_dec(v___x_3056_);
lean_dec(v___x_3054_);
lean_dec(v___y_3052_);
lean_dec_ref(v___f_3050_);
lean_dec(v_inst_3045_);
lean_dec(v_sendIdx_3041_);
lean_dec_ref(v_buf_3040_);
lean_dec(v_capacity_3039_);
lean_dec_ref(v_consumers_3038_);
v___x_3066_ = lean_box(0);
v___x_3067_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3034_, v_toBind_3035_, v___f_3049_, v___x_3066_, v___x_3055_, v_a_3043_);
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3071_, lean_object* v_inst_3072_, lean_object* v_toBind_3073_, lean_object* v_bufCount_3074_, lean_object* v_producers_3075_, lean_object* v_consumers_3076_, lean_object* v_capacity_3077_, lean_object* v_buf_3078_, lean_object* v_sendIdx_3079_, lean_object* v_closed_3080_, lean_object* v_a_3081_, lean_object* v___x_3082_, lean_object* v_inst_3083_, lean_object* v_recvIdx_3084_, lean_object* v___x_3085_, lean_object* v_a_3086_){
_start:
{
uint8_t v_closed_boxed_3087_; uint8_t v___x_679__boxed_3088_; lean_object* v_res_3089_; 
v_closed_boxed_3087_ = lean_unbox(v_closed_3080_);
v___x_679__boxed_3088_ = lean_unbox(v___x_3082_);
v_res_3089_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3071_, v_inst_3072_, v_toBind_3073_, v_bufCount_3074_, v_producers_3075_, v_consumers_3076_, v_capacity_3077_, v_buf_3078_, v_sendIdx_3079_, v_closed_boxed_3087_, v_a_3081_, v___x_679__boxed_3088_, v_inst_3083_, v_recvIdx_3084_, v___x_3085_, v_a_3086_);
lean_dec(v_recvIdx_3084_);
lean_dec(v_a_3081_);
lean_dec(v_bufCount_3074_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3090_, lean_object* v_inst_3091_, lean_object* v_toBind_3092_, lean_object* v_a_3093_, lean_object* v_inst_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_producers_3096_; lean_object* v_consumers_3097_; lean_object* v_capacity_3098_; lean_object* v_buf_3099_; lean_object* v_bufCount_3100_; lean_object* v_sendIdx_3101_; lean_object* v_recvIdx_3102_; uint8_t v_closed_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v_producers_3096_ = lean_ctor_get(v_a_3095_, 0);
lean_inc_ref(v_producers_3096_);
v_consumers_3097_ = lean_ctor_get(v_a_3095_, 1);
lean_inc_ref(v_consumers_3097_);
v_capacity_3098_ = lean_ctor_get(v_a_3095_, 2);
lean_inc(v_capacity_3098_);
v_buf_3099_ = lean_ctor_get(v_a_3095_, 3);
lean_inc_ref(v_buf_3099_);
v_bufCount_3100_ = lean_ctor_get(v_a_3095_, 4);
lean_inc(v_bufCount_3100_);
v_sendIdx_3101_ = lean_ctor_get(v_a_3095_, 5);
lean_inc(v_sendIdx_3101_);
v_recvIdx_3102_ = lean_ctor_get(v_a_3095_, 6);
lean_inc(v_recvIdx_3102_);
v_closed_3103_ = lean_ctor_get_uint8(v_a_3095_, sizeof(void*)*7);
lean_dec_ref(v_a_3095_);
v___x_3104_ = lean_unsigned_to_nat(0u);
v___x_3105_ = lean_nat_dec_eq(v_bufCount_3100_, v___x_3104_);
if (v___x_3105_ == 0)
{
uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___f_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3106_ = 1;
v___x_3107_ = lean_box(v_closed_3103_);
v___x_3108_ = lean_box(v___x_3106_);
lean_inc(v_recvIdx_3102_);
lean_inc(v_a_3093_);
lean_inc_ref(v_buf_3099_);
lean_inc(v_toBind_3092_);
lean_inc(v_inst_3091_);
v___f_3109_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3109_, 0, v_toApplicative_3090_);
lean_closure_set(v___f_3109_, 1, v_inst_3091_);
lean_closure_set(v___f_3109_, 2, v_toBind_3092_);
lean_closure_set(v___f_3109_, 3, v_bufCount_3100_);
lean_closure_set(v___f_3109_, 4, v_producers_3096_);
lean_closure_set(v___f_3109_, 5, v_consumers_3097_);
lean_closure_set(v___f_3109_, 6, v_capacity_3098_);
lean_closure_set(v___f_3109_, 7, v_buf_3099_);
lean_closure_set(v___f_3109_, 8, v_sendIdx_3101_);
lean_closure_set(v___f_3109_, 9, v___x_3107_);
lean_closure_set(v___f_3109_, 10, v_a_3093_);
lean_closure_set(v___f_3109_, 11, v___x_3108_);
lean_closure_set(v___f_3109_, 12, v_inst_3094_);
lean_closure_set(v___f_3109_, 13, v_recvIdx_3102_);
lean_closure_set(v___f_3109_, 14, v___x_3104_);
v___x_3110_ = lean_array_fget(v_buf_3099_, v_recvIdx_3102_);
lean_dec(v_recvIdx_3102_);
lean_dec_ref(v_buf_3099_);
v___x_3111_ = lean_box(0);
v___x_3112_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3112_, 0, lean_box(0));
lean_closure_set(v___x_3112_, 1, lean_box(0));
lean_closure_set(v___x_3112_, 2, v___x_3110_);
lean_closure_set(v___x_3112_, 3, v___x_3111_);
v___x_3113_ = lean_apply_2(v_inst_3091_, lean_box(0), v___x_3112_);
v___x_3114_ = lean_apply_4(v_toBind_3092_, lean_box(0), lean_box(0), v___x_3113_, v___f_3109_);
return v___x_3114_;
}
else
{
lean_object* v_toPure_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec(v_recvIdx_3102_);
lean_dec(v_sendIdx_3101_);
lean_dec(v_bufCount_3100_);
lean_dec_ref(v_buf_3099_);
lean_dec(v_capacity_3098_);
lean_dec_ref(v_consumers_3097_);
lean_dec_ref(v_producers_3096_);
lean_dec(v_inst_3094_);
lean_dec(v_toBind_3092_);
lean_dec(v_inst_3091_);
v_toPure_3115_ = lean_ctor_get(v_toApplicative_3090_, 1);
lean_inc(v_toPure_3115_);
lean_dec_ref(v_toApplicative_3090_);
v___x_3116_ = lean_box(0);
v___x_3117_ = lean_apply_2(v_toPure_3115_, lean_box(0), v___x_3116_);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_3118_, lean_object* v_inst_3119_, lean_object* v_toBind_3120_, lean_object* v_a_3121_, lean_object* v_inst_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(v_toApplicative_3118_, v_inst_3119_, v_toBind_3120_, v_a_3121_, v_inst_3122_, v_a_3123_);
lean_dec(v_a_3121_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3125_, lean_object* v_inst_3126_, lean_object* v_inst_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_toApplicative_3129_; lean_object* v_toBind_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_toApplicative_3129_ = lean_ctor_get(v_inst_3125_, 0);
lean_inc_ref(v_toApplicative_3129_);
v_toBind_3130_ = lean_ctor_get(v_inst_3125_, 1);
lean_inc_n(v_toBind_3130_, 2);
lean_dec_ref(v_inst_3125_);
lean_inc_n(v_a_3128_, 2);
lean_inc(v_inst_3126_);
v___f_3131_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_3131_, 0, v_toApplicative_3129_);
lean_closure_set(v___f_3131_, 1, v_inst_3126_);
lean_closure_set(v___f_3131_, 2, v_toBind_3130_);
lean_closure_set(v___f_3131_, 3, v_a_3128_);
lean_closure_set(v___f_3131_, 4, v_inst_3127_);
v___x_3132_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3132_, 0, lean_box(0));
lean_closure_set(v___x_3132_, 1, lean_box(0));
lean_closure_set(v___x_3132_, 2, v_a_3128_);
v___x_3133_ = lean_apply_2(v_inst_3126_, lean_box(0), v___x_3132_);
v___x_3134_ = lean_apply_4(v_toBind_3130_, lean_box(0), lean_box(0), v___x_3133_, v___f_3131_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_3135_, lean_object* v_inst_3136_, lean_object* v_inst_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3135_, v_inst_3136_, v_inst_3137_, v_a_3138_);
lean_dec(v_a_3138_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3140_, lean_object* v_00_u03b1_3141_, lean_object* v_inst_3142_, lean_object* v_inst_3143_, lean_object* v_inst_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3142_, v_inst_3143_, v_inst_3144_, v_a_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object* v_m_3147_, lean_object* v_00_u03b1_3148_, lean_object* v_inst_3149_, lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(v_m_3147_, v_00_u03b1_3148_, v_inst_3149_, v_inst_3150_, v_inst_3151_, v_a_3152_);
lean_dec(v_a_3152_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3154_){
_start:
{
lean_object* v___x_3156_; lean_object* v_producers_3157_; lean_object* v_consumers_3158_; lean_object* v_capacity_3159_; lean_object* v_buf_3160_; lean_object* v_bufCount_3161_; lean_object* v_sendIdx_3162_; lean_object* v_recvIdx_3163_; uint8_t v_closed_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3196_; 
v___x_3156_ = lean_st_ref_get(v_a_3154_);
v_producers_3157_ = lean_ctor_get(v___x_3156_, 0);
v_consumers_3158_ = lean_ctor_get(v___x_3156_, 1);
v_capacity_3159_ = lean_ctor_get(v___x_3156_, 2);
v_buf_3160_ = lean_ctor_get(v___x_3156_, 3);
v_bufCount_3161_ = lean_ctor_get(v___x_3156_, 4);
v_sendIdx_3162_ = lean_ctor_get(v___x_3156_, 5);
v_recvIdx_3163_ = lean_ctor_get(v___x_3156_, 6);
v_closed_3164_ = lean_ctor_get_uint8(v___x_3156_, sizeof(void*)*7);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3166_ = v___x_3156_;
v_isShared_3167_ = v_isSharedCheck_3196_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_recvIdx_3163_);
lean_inc(v_sendIdx_3162_);
lean_inc(v_bufCount_3161_);
lean_inc(v_buf_3160_);
lean_inc(v_capacity_3159_);
lean_inc(v_consumers_3158_);
lean_inc(v_producers_3157_);
lean_dec(v___x_3156_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3196_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = lean_nat_dec_eq(v_bufCount_3161_, v___x_3168_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v_st_3174_; lean_object* v___y_3175_; uint8_t v___x_3177_; lean_object* v___y_3179_; lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v___x_3170_ = lean_array_fget_borrowed(v_buf_3160_, v_recvIdx_3163_);
v___x_3171_ = lean_box(0);
v___x_3172_ = lean_st_ref_swap(v___x_3170_, v___x_3171_);
v___x_3177_ = 1;
v___x_3192_ = lean_unsigned_to_nat(1u);
v___x_3193_ = lean_nat_add(v_recvIdx_3163_, v___x_3192_);
lean_dec(v_recvIdx_3163_);
v___x_3194_ = lean_nat_dec_eq(v___x_3193_, v_capacity_3159_);
if (v___x_3194_ == 0)
{
v___y_3179_ = v___x_3193_;
goto v___jp_3178_;
}
else
{
lean_dec(v___x_3193_);
v___y_3179_ = v___x_3168_;
goto v___jp_3178_;
}
v___jp_3173_:
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_st_ref_swap(v___y_3175_, v_st_3174_);
lean_dec(v___x_3176_);
return v___x_3172_;
}
v___jp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3183_; 
v___x_3180_ = lean_unsigned_to_nat(1u);
v___x_3181_ = lean_nat_sub(v_bufCount_3161_, v___x_3180_);
lean_dec(v_bufCount_3161_);
lean_inc(v___y_3179_);
lean_inc(v_sendIdx_3162_);
lean_inc(v___x_3181_);
lean_inc_ref(v_buf_3160_);
lean_inc(v_capacity_3159_);
lean_inc_ref(v_consumers_3158_);
lean_inc_ref(v_producers_3157_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 6, v___y_3179_);
lean_ctor_set(v___x_3166_, 4, v___x_3181_);
v___x_3183_ = v___x_3166_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_producers_3157_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_consumers_3158_);
lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_capacity_3159_);
lean_ctor_set(v_reuseFailAlloc_3191_, 3, v_buf_3160_);
lean_ctor_set(v_reuseFailAlloc_3191_, 4, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3191_, 5, v_sendIdx_3162_);
lean_ctor_set(v_reuseFailAlloc_3191_, 6, v___y_3179_);
lean_ctor_set_uint8(v_reuseFailAlloc_3191_, sizeof(void*)*7, v_closed_3164_);
v___x_3183_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3157_);
if (lean_obj_tag(v___x_3184_) == 1)
{
lean_object* v_val_3185_; lean_object* v_fst_3186_; lean_object* v_snd_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_dec_ref(v___x_3183_);
v_val_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_val_3185_);
lean_dec_ref_known(v___x_3184_, 1);
v_fst_3186_ = lean_ctor_get(v_val_3185_, 0);
lean_inc(v_fst_3186_);
v_snd_3187_ = lean_ctor_get(v_val_3185_, 1);
lean_inc(v_snd_3187_);
lean_dec(v_val_3185_);
v___x_3188_ = lean_box(v___x_3177_);
v___x_3189_ = lean_io_promise_resolve(v___x_3188_, v_fst_3186_);
lean_dec(v_fst_3186_);
v___x_3190_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3190_, 0, v_snd_3187_);
lean_ctor_set(v___x_3190_, 1, v_consumers_3158_);
lean_ctor_set(v___x_3190_, 2, v_capacity_3159_);
lean_ctor_set(v___x_3190_, 3, v_buf_3160_);
lean_ctor_set(v___x_3190_, 4, v___x_3181_);
lean_ctor_set(v___x_3190_, 5, v_sendIdx_3162_);
lean_ctor_set(v___x_3190_, 6, v___y_3179_);
lean_ctor_set_uint8(v___x_3190_, sizeof(void*)*7, v_closed_3164_);
v_st_3174_ = v___x_3190_;
v___y_3175_ = v_a_3154_;
goto v___jp_3173_;
}
else
{
lean_dec(v___x_3184_);
lean_dec(v___x_3181_);
lean_dec(v___y_3179_);
lean_dec(v_sendIdx_3162_);
lean_dec_ref(v_buf_3160_);
lean_dec(v_capacity_3159_);
lean_dec_ref(v_consumers_3158_);
v_st_3174_ = v___x_3183_;
v___y_3175_ = v_a_3154_;
goto v___jp_3173_;
}
}
}
}
else
{
lean_object* v___x_3195_; 
lean_del_object(v___x_3166_);
lean_dec(v_recvIdx_3163_);
lean_dec(v_sendIdx_3162_);
lean_dec(v_bufCount_3161_);
lean_dec_ref(v_buf_3160_);
lean_dec(v_capacity_3159_);
lean_dec_ref(v_consumers_3158_);
lean_dec_ref(v_producers_3157_);
v___x_3195_ = lean_box(0);
return v___x_3195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3197_);
lean_dec(v_a_3197_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3201_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3204_, lean_object* v_a_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3204_, v_a_3205_);
lean_dec(v_a_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3209_){
_start:
{
lean_object* v___f_3211_; lean_object* v___x_3212_; 
v___f_3211_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3212_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3209_, v___f_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3213_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3216_, lean_object* v_ch_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3217_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3220_, lean_object* v_ch_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3220_, v_ch_3221_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3225_);
if (lean_obj_tag(v___x_3227_) == 1)
{
lean_object* v___x_3228_; 
lean_dec_ref(v___f_3224_);
v___x_3228_ = lean_task_pure(v___x_3227_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; uint8_t v_closed_3230_; 
lean_dec(v___x_3227_);
v___x_3229_ = lean_st_ref_get(v___y_3225_);
v_closed_3230_ = lean_ctor_get_uint8(v___x_3229_, sizeof(void*)*7);
lean_dec(v___x_3229_);
if (v_closed_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v_producers_3233_; lean_object* v_consumers_3234_; lean_object* v_capacity_3235_; lean_object* v_buf_3236_; lean_object* v_bufCount_3237_; lean_object* v_sendIdx_3238_; lean_object* v_recvIdx_3239_; uint8_t v_closed_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3254_; 
v___x_3231_ = lean_io_promise_new();
v___x_3232_ = lean_st_ref_take(v___y_3225_);
v_producers_3233_ = lean_ctor_get(v___x_3232_, 0);
v_consumers_3234_ = lean_ctor_get(v___x_3232_, 1);
v_capacity_3235_ = lean_ctor_get(v___x_3232_, 2);
v_buf_3236_ = lean_ctor_get(v___x_3232_, 3);
v_bufCount_3237_ = lean_ctor_get(v___x_3232_, 4);
v_sendIdx_3238_ = lean_ctor_get(v___x_3232_, 5);
v_recvIdx_3239_ = lean_ctor_get(v___x_3232_, 6);
v_closed_3240_ = lean_ctor_get_uint8(v___x_3232_, sizeof(void*)*7);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3242_ = v___x_3232_;
v_isShared_3243_ = v_isSharedCheck_3254_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_recvIdx_3239_);
lean_inc(v_sendIdx_3238_);
lean_inc(v_bufCount_3237_);
lean_inc(v_buf_3236_);
lean_inc(v_capacity_3235_);
lean_inc(v_consumers_3234_);
lean_inc(v_producers_3233_);
lean_dec(v___x_3232_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3254_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3244_ = lean_box(0);
lean_inc(v___x_3231_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3231_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = l_Std_Queue_enqueue___redArg(v___x_3245_, v_consumers_3234_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 1, v___x_3246_);
v___x_3248_ = v___x_3242_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_producers_3233_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3253_, 2, v_capacity_3235_);
lean_ctor_set(v_reuseFailAlloc_3253_, 3, v_buf_3236_);
lean_ctor_set(v_reuseFailAlloc_3253_, 4, v_bufCount_3237_);
lean_ctor_set(v_reuseFailAlloc_3253_, 5, v_sendIdx_3238_);
lean_ctor_set(v_reuseFailAlloc_3253_, 6, v_recvIdx_3239_);
lean_ctor_set_uint8(v_reuseFailAlloc_3253_, sizeof(void*)*7, v_closed_3240_);
v___x_3248_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3249_ = lean_st_ref_put(v___y_3225_, v___x_3248_);
v___x_3250_ = lean_io_promise_result_opt(v___x_3231_);
lean_dec(v___x_3231_);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = lean_io_bind_task(v___x_3250_, v___f_3224_, v___x_3251_, v_closed_3230_);
return v___x_3252_;
}
}
}
else
{
lean_object* v___x_3255_; 
lean_dec_ref(v___f_3224_);
v___x_3255_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3255_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3256_, v___y_3257_);
lean_dec(v___y_3257_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3260_, lean_object* v_res_3261_){
_start:
{
if (lean_obj_tag(v_res_3261_) == 0)
{
lean_dec_ref(v_ch_3260_);
goto v___jp_3263_;
}
else
{
lean_object* v_val_3265_; uint8_t v___x_3266_; 
v_val_3265_ = lean_ctor_get(v_res_3261_, 0);
v___x_3266_ = lean_unbox(v_val_3265_);
if (v___x_3266_ == 0)
{
lean_dec_ref(v_ch_3260_);
goto v___jp_3263_;
}
else
{
lean_object* v___x_3267_; 
v___x_3267_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3260_);
return v___x_3267_;
}
}
v___jp_3263_:
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3268_, lean_object* v_res_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3268_, v_res_3269_);
lean_dec(v_res_3269_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3272_){
_start:
{
lean_object* v___f_3274_; lean_object* v___f_3275_; lean_object* v___x_3276_; 
lean_inc_ref(v_ch_3272_);
v___f_3274_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3274_, 0, v_ch_3272_);
v___f_3275_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3275_, 0, v___f_3274_);
v___x_3276_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3272_, v___f_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3277_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3280_, lean_object* v_ch_3281_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3281_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3284_, lean_object* v_ch_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3284_, v_ch_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3288_, lean_object* v_a_3289_){
_start:
{
uint8_t v___y_3291_; lean_object* v_bufCount_3295_; uint8_t v_closed_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v_bufCount_3295_ = lean_ctor_get(v_a_3289_, 4);
v_closed_3296_ = lean_ctor_get_uint8(v_a_3289_, sizeof(void*)*7);
v___x_3297_ = lean_unsigned_to_nat(0u);
v___x_3298_ = lean_nat_dec_eq(v_bufCount_3295_, v___x_3297_);
if (v___x_3298_ == 0)
{
uint8_t v___x_3299_; 
v___x_3299_ = 1;
v___y_3291_ = v___x_3299_;
goto v___jp_3290_;
}
else
{
v___y_3291_ = v_closed_3296_;
goto v___jp_3290_;
}
v___jp_3290_:
{
lean_object* v_toPure_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_toPure_3292_ = lean_ctor_get(v_toApplicative_3288_, 1);
lean_inc(v_toPure_3292_);
lean_dec_ref(v_toApplicative_3288_);
v___x_3293_ = lean_box(v___y_3291_);
v___x_3294_ = lean_apply_2(v_toPure_3292_, lean_box(0), v___x_3293_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3300_, v_a_3301_);
lean_dec_ref(v_a_3301_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_toApplicative_3306_; lean_object* v_toBind_3307_; lean_object* v___f_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_toApplicative_3306_ = lean_ctor_get(v_inst_3303_, 0);
lean_inc_ref(v_toApplicative_3306_);
v_toBind_3307_ = lean_ctor_get(v_inst_3303_, 1);
lean_inc(v_toBind_3307_);
lean_dec_ref(v_inst_3303_);
v___f_3308_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3308_, 0, v_toApplicative_3306_);
lean_inc(v_a_3305_);
v___x_3309_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3309_, 0, lean_box(0));
lean_closure_set(v___x_3309_, 1, lean_box(0));
lean_closure_set(v___x_3309_, 2, v_a_3305_);
v___x_3310_ = lean_apply_2(v_inst_3304_, lean_box(0), v___x_3309_);
v___x_3311_ = lean_apply_4(v_toBind_3307_, lean_box(0), lean_box(0), v___x_3310_, v___f_3308_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(v_inst_3312_, v_inst_3313_, v_a_3314_);
lean_dec(v_a_3314_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3316_, lean_object* v_00_u03b1_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v_toApplicative_3321_; lean_object* v_toBind_3322_; lean_object* v___f_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_toApplicative_3321_ = lean_ctor_get(v_inst_3318_, 0);
lean_inc_ref(v_toApplicative_3321_);
v_toBind_3322_ = lean_ctor_get(v_inst_3318_, 1);
lean_inc(v_toBind_3322_);
lean_dec_ref(v_inst_3318_);
v___f_3323_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3323_, 0, v_toApplicative_3321_);
lean_inc(v_a_3320_);
v___x_3324_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3324_, 0, lean_box(0));
lean_closure_set(v___x_3324_, 1, lean_box(0));
lean_closure_set(v___x_3324_, 2, v_a_3320_);
v___x_3325_ = lean_apply_2(v_inst_3319_, lean_box(0), v___x_3324_);
v___x_3326_ = lean_apply_4(v_toBind_3322_, lean_box(0), lean_box(0), v___x_3325_, v___f_3323_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object* v_m_3327_, lean_object* v_00_u03b1_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(v_m_3327_, v_00_u03b1_3328_, v_inst_3329_, v_inst_3330_, v_a_3331_);
lean_dec(v_a_3331_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3333_){
_start:
{
lean_object* v___x_3335_; lean_object* v_producers_3336_; lean_object* v_consumers_3337_; lean_object* v_capacity_3338_; lean_object* v_buf_3339_; lean_object* v_bufCount_3340_; lean_object* v_sendIdx_3341_; lean_object* v_recvIdx_3342_; uint8_t v_closed_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3377_; 
v___x_3335_ = lean_st_ref_get(v_a_3333_);
v_producers_3336_ = lean_ctor_get(v___x_3335_, 0);
v_consumers_3337_ = lean_ctor_get(v___x_3335_, 1);
v_capacity_3338_ = lean_ctor_get(v___x_3335_, 2);
v_buf_3339_ = lean_ctor_get(v___x_3335_, 3);
v_bufCount_3340_ = lean_ctor_get(v___x_3335_, 4);
v_sendIdx_3341_ = lean_ctor_get(v___x_3335_, 5);
v_recvIdx_3342_ = lean_ctor_get(v___x_3335_, 6);
v_closed_3343_ = lean_ctor_get_uint8(v___x_3335_, sizeof(void*)*7);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3345_ = v___x_3335_;
v_isShared_3346_ = v_isSharedCheck_3377_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_recvIdx_3342_);
lean_inc(v_sendIdx_3341_);
lean_inc(v_bufCount_3340_);
lean_inc(v_buf_3339_);
lean_inc(v_capacity_3338_);
lean_inc(v_consumers_3337_);
lean_inc(v_producers_3336_);
lean_dec(v___x_3335_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3377_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = lean_unsigned_to_nat(0u);
v___x_3348_ = lean_nat_dec_eq(v_bufCount_3340_, v___x_3347_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v_st_3353_; lean_object* v___y_3354_; uint8_t v___x_3357_; lean_object* v___y_3359_; lean_object* v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3349_ = lean_array_fget_borrowed(v_buf_3339_, v_recvIdx_3342_);
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_st_ref_swap(v___x_3349_, v___x_3350_);
v___x_3357_ = 1;
v___x_3372_ = lean_unsigned_to_nat(1u);
v___x_3373_ = lean_nat_add(v_recvIdx_3342_, v___x_3372_);
lean_dec(v_recvIdx_3342_);
v___x_3374_ = lean_nat_dec_eq(v___x_3373_, v_capacity_3338_);
if (v___x_3374_ == 0)
{
v___y_3359_ = v___x_3373_;
goto v___jp_3358_;
}
else
{
lean_dec(v___x_3373_);
v___y_3359_ = v___x_3347_;
goto v___jp_3358_;
}
v___jp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = lean_st_ref_swap(v___y_3354_, v_st_3353_);
lean_dec(v___x_3355_);
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3351_);
return v___x_3356_;
}
v___jp_3358_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3360_ = lean_unsigned_to_nat(1u);
v___x_3361_ = lean_nat_sub(v_bufCount_3340_, v___x_3360_);
lean_dec(v_bufCount_3340_);
lean_inc(v___y_3359_);
lean_inc(v_sendIdx_3341_);
lean_inc(v___x_3361_);
lean_inc_ref(v_buf_3339_);
lean_inc(v_capacity_3338_);
lean_inc_ref(v_consumers_3337_);
lean_inc_ref(v_producers_3336_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 6, v___y_3359_);
lean_ctor_set(v___x_3345_, 4, v___x_3361_);
v___x_3363_ = v___x_3345_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_producers_3336_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_consumers_3337_);
lean_ctor_set(v_reuseFailAlloc_3371_, 2, v_capacity_3338_);
lean_ctor_set(v_reuseFailAlloc_3371_, 3, v_buf_3339_);
lean_ctor_set(v_reuseFailAlloc_3371_, 4, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3371_, 5, v_sendIdx_3341_);
lean_ctor_set(v_reuseFailAlloc_3371_, 6, v___y_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3371_, sizeof(void*)*7, v_closed_3343_);
v___x_3363_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3336_);
if (lean_obj_tag(v___x_3364_) == 1)
{
lean_object* v_val_3365_; lean_object* v_fst_3366_; lean_object* v_snd_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec_ref(v___x_3363_);
v_val_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v_fst_3366_ = lean_ctor_get(v_val_3365_, 0);
lean_inc(v_fst_3366_);
v_snd_3367_ = lean_ctor_get(v_val_3365_, 1);
lean_inc(v_snd_3367_);
lean_dec(v_val_3365_);
v___x_3368_ = lean_box(v___x_3357_);
v___x_3369_ = lean_io_promise_resolve(v___x_3368_, v_fst_3366_);
lean_dec(v_fst_3366_);
v___x_3370_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3370_, 0, v_snd_3367_);
lean_ctor_set(v___x_3370_, 1, v_consumers_3337_);
lean_ctor_set(v___x_3370_, 2, v_capacity_3338_);
lean_ctor_set(v___x_3370_, 3, v_buf_3339_);
lean_ctor_set(v___x_3370_, 4, v___x_3361_);
lean_ctor_set(v___x_3370_, 5, v_sendIdx_3341_);
lean_ctor_set(v___x_3370_, 6, v___y_3359_);
lean_ctor_set_uint8(v___x_3370_, sizeof(void*)*7, v_closed_3343_);
v_st_3353_ = v___x_3370_;
v___y_3354_ = v_a_3333_;
goto v___jp_3352_;
}
else
{
lean_dec(v___x_3364_);
lean_dec(v___x_3361_);
lean_dec(v___y_3359_);
lean_dec(v_sendIdx_3341_);
lean_dec_ref(v_buf_3339_);
lean_dec(v_capacity_3338_);
lean_dec_ref(v_consumers_3337_);
v_st_3353_ = v___x_3363_;
v___y_3354_ = v_a_3333_;
goto v___jp_3352_;
}
}
}
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
lean_del_object(v___x_3345_);
lean_dec(v_recvIdx_3342_);
lean_dec(v_sendIdx_3341_);
lean_dec(v_bufCount_3340_);
lean_dec_ref(v_buf_3339_);
lean_dec(v_capacity_3338_);
lean_dec_ref(v_consumers_3337_);
lean_dec_ref(v_producers_3336_);
v___x_3375_ = lean_box(0);
v___x_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
return v___x_3376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3378_);
lean_dec(v_a_3378_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3382_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3385_, lean_object* v_a_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3385_, v_a_3386_);
lean_dec(v_a_3386_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3389_, lean_object* v_lose_3390_){
_start:
{
lean_object* v_finished_3392_; lean_object* v_promise_3393_; lean_object* v___x_3394_; uint8_t v___y_3396_; uint8_t v___x_3404_; 
v_finished_3392_ = lean_ctor_get(v_w_3389_, 0);
v_promise_3393_ = lean_ctor_get(v_w_3389_, 1);
v___x_3394_ = lean_st_ref_take(v_finished_3392_);
v___x_3404_ = lean_unbox(v___x_3394_);
lean_dec(v___x_3394_);
if (v___x_3404_ == 0)
{
uint8_t v___x_3405_; 
v___x_3405_ = 1;
v___y_3396_ = v___x_3405_;
goto v___jp_3395_;
}
else
{
uint8_t v___x_3406_; 
v___x_3406_ = 0;
v___y_3396_ = v___x_3406_;
goto v___jp_3395_;
}
v___jp_3395_:
{
uint8_t v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = 1;
v___x_3398_ = lean_box(v___x_3397_);
v___x_3399_ = lean_st_ref_put(v_finished_3392_, v___x_3398_);
if (v___y_3396_ == 0)
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_apply_1(v_lose_3390_, lean_box(0));
return v___x_3400_;
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v_lose_3390_);
v___x_3401_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__2));
v___x_3402_ = lean_io_promise_resolve(v___x_3401_, v_promise_3393_);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3407_, lean_object* v_lose_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3407_, v_lose_3408_);
lean_dec_ref(v_w_3407_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3411_, lean_object* v_w_3412_, lean_object* v_lose_3413_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3412_, v_lose_3413_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3416_, lean_object* v_w_3417_, lean_object* v_lose_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3416_, v_w_3417_, v_lose_3418_);
lean_dec_ref(v_w_3417_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3421_, lean_object* v_lose_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_finished_3425_; lean_object* v_promise_3426_; lean_object* v___x_3427_; uint8_t v___y_3429_; uint8_t v___x_3445_; 
v_finished_3425_ = lean_ctor_get(v_w_3421_, 0);
v_promise_3426_ = lean_ctor_get(v_w_3421_, 1);
v___x_3427_ = lean_st_ref_take(v_finished_3425_);
v___x_3445_ = lean_unbox(v___x_3427_);
lean_dec(v___x_3427_);
if (v___x_3445_ == 0)
{
uint8_t v___x_3446_; 
v___x_3446_ = 1;
v___y_3429_ = v___x_3446_;
goto v___jp_3428_;
}
else
{
uint8_t v___x_3447_; 
v___x_3447_ = 0;
v___y_3429_ = v___x_3447_;
goto v___jp_3428_;
}
v___jp_3428_:
{
uint8_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3430_ = 1;
v___x_3431_ = lean_box(v___x_3430_);
v___x_3432_ = lean_st_ref_put(v_finished_3425_, v___x_3431_);
if (v___y_3429_ == 0)
{
lean_object* v___x_3433_; 
lean_inc(v___y_3423_);
v___x_3433_ = lean_apply_2(v_lose_3422_, v___y_3423_, lean_box(0));
return v___x_3433_;
}
else
{
lean_object* v___x_3434_; lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3444_; 
lean_dec_ref(v_lose_3422_);
v___x_3434_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3423_);
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3444_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3444_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3439_, 0, v_a_3435_);
v___x_3440_ = lean_io_promise_resolve(v___x_3439_, v_promise_3426_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3440_);
v___x_3442_ = v___x_3437_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3448_, lean_object* v_lose_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3448_, v_lose_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v_w_3448_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3453_, lean_object* v_w_3454_, lean_object* v_lose_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3454_, v_lose_3455_, v___y_3456_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3459_, lean_object* v_w_3460_, lean_object* v_lose_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3459_, v_w_3460_, v_lose_3461_, v___y_3462_);
lean_dec(v___y_3462_);
lean_dec_ref(v_w_3460_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3465_, lean_object* v_k_3466_){
_start:
{
lean_object* v_ref_3468_; lean_object* v_mutex_3469_; lean_object* v___x_3470_; lean_object* v_r_3471_; 
v_ref_3468_ = lean_ctor_get(v_mutex_3465_, 0);
lean_inc(v_ref_3468_);
v_mutex_3469_ = lean_ctor_get(v_mutex_3465_, 1);
lean_inc(v_mutex_3469_);
lean_dec_ref(v_mutex_3465_);
v___x_3470_ = lean_io_basemutex_lock(v_mutex_3469_);
v_r_3471_ = lean_apply_2(v_k_3466_, v_ref_3468_, lean_box(0));
if (lean_obj_tag(v_r_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3480_; 
v_a_3472_ = lean_ctor_get(v_r_3471_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_r_3471_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3474_ = v_r_3471_;
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v_r_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = lean_io_basemutex_unlock(v_mutex_3469_);
lean_dec(v_mutex_3469_);
if (v_isShared_3475_ == 0)
{
v___x_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3472_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3489_; 
v_a_3481_ = lean_ctor_get(v_r_3471_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v_r_3471_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3483_ = v_r_3471_;
v_isShared_3484_ = v_isSharedCheck_3489_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v_r_3471_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3489_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3485_ = lean_io_basemutex_unlock(v_mutex_3469_);
lean_dec(v_mutex_3469_);
if (v_isShared_3484_ == 0)
{
v___x_3487_ = v___x_3483_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3481_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3490_, lean_object* v_k_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3490_, v_k_3491_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3494_, lean_object* v_00_u03b2_3495_, lean_object* v_mutex_3496_, lean_object* v_k_3497_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3496_, v_k_3497_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3500_, lean_object* v_00_u03b2_3501_, lean_object* v_mutex_3502_, lean_object* v_k_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3500_, v_00_u03b2_3501_, v_mutex_3502_, v_k_3503_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3506_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3506_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3509_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; lean_object* v_producers_3516_; lean_object* v_consumers_3517_; lean_object* v_capacity_3518_; lean_object* v_buf_3519_; lean_object* v_bufCount_3520_; lean_object* v_sendIdx_3521_; lean_object* v_recvIdx_3522_; uint8_t v_closed_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3546_; 
v___x_3515_ = lean_st_ref_get(v___y_3513_);
v_producers_3516_ = lean_ctor_get(v___x_3515_, 0);
v_consumers_3517_ = lean_ctor_get(v___x_3515_, 1);
v_capacity_3518_ = lean_ctor_get(v___x_3515_, 2);
v_buf_3519_ = lean_ctor_get(v___x_3515_, 3);
v_bufCount_3520_ = lean_ctor_get(v___x_3515_, 4);
v_sendIdx_3521_ = lean_ctor_get(v___x_3515_, 5);
v_recvIdx_3522_ = lean_ctor_get(v___x_3515_, 6);
v_closed_3523_ = lean_ctor_get_uint8(v___x_3515_, sizeof(void*)*7);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3525_ = v___x_3515_;
v_isShared_3526_ = v_isSharedCheck_3546_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_recvIdx_3522_);
lean_inc(v_sendIdx_3521_);
lean_inc(v_bufCount_3520_);
lean_inc(v_buf_3519_);
lean_inc(v_capacity_3518_);
lean_inc(v_consumers_3517_);
lean_inc(v_producers_3516_);
lean_dec(v___x_3515_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3546_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; 
v___x_3527_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3517_);
if (lean_obj_tag(v___x_3527_) == 1)
{
lean_object* v_val_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3543_; 
v_val_3528_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3530_ = v___x_3527_;
v_isShared_3531_ = v_isSharedCheck_3543_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_val_3528_);
lean_dec(v___x_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3543_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v_fst_3532_; lean_object* v_snd_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v_fst_3532_ = lean_ctor_get(v_val_3528_, 0);
lean_inc(v_fst_3532_);
v_snd_3533_ = lean_ctor_get(v_val_3528_, 1);
lean_inc(v_snd_3533_);
lean_dec(v_val_3528_);
v___x_3534_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3532_, v_____do__lift_3512_);
lean_dec(v_fst_3532_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 1, v_snd_3533_);
v___x_3536_ = v___x_3525_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_producers_3516_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_snd_3533_);
lean_ctor_set(v_reuseFailAlloc_3542_, 2, v_capacity_3518_);
lean_ctor_set(v_reuseFailAlloc_3542_, 3, v_buf_3519_);
lean_ctor_set(v_reuseFailAlloc_3542_, 4, v_bufCount_3520_);
lean_ctor_set(v_reuseFailAlloc_3542_, 5, v_sendIdx_3521_);
lean_ctor_set(v_reuseFailAlloc_3542_, 6, v_recvIdx_3522_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, sizeof(void*)*7, v_closed_3523_);
v___x_3536_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3537_ = lean_st_ref_swap(v___y_3513_, v___x_3536_);
lean_dec(v___x_3537_);
v___x_3538_ = lean_box(0);
if (v_isShared_3531_ == 0)
{
lean_ctor_set_tag(v___x_3530_, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3538_);
v___x_3540_ = v___x_3530_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
else
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec(v___x_3527_);
lean_del_object(v___x_3525_);
lean_dec(v_recvIdx_3522_);
lean_dec(v_sendIdx_3521_);
lean_dec(v_bufCount_3520_);
lean_dec_ref(v_buf_3519_);
lean_dec(v_capacity_3518_);
lean_dec_ref(v_producers_3516_);
v___x_3544_ = lean_box(0);
v___x_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
return v___x_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
uint8_t v_____do__lift_3966__boxed_3550_; lean_object* v_res_3551_; 
v_____do__lift_3966__boxed_3550_ = lean_unbox(v_____do__lift_3547_);
v_res_3551_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3966__boxed_3550_, v___y_3548_);
lean_dec(v___y_3548_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3552_, lean_object* v___f_3553_, uint8_t v_____do__lift_3554_, lean_object* v___y_3555_){
_start:
{
if (v_____do__lift_3554_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_producers_3559_; lean_object* v_consumers_3560_; lean_object* v_capacity_3561_; lean_object* v_buf_3562_; lean_object* v_bufCount_3563_; lean_object* v_sendIdx_3564_; lean_object* v_recvIdx_3565_; uint8_t v_closed_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3580_; 
v___x_3557_ = lean_io_promise_new();
v___x_3558_ = lean_st_ref_take(v___y_3555_);
v_producers_3559_ = lean_ctor_get(v___x_3558_, 0);
v_consumers_3560_ = lean_ctor_get(v___x_3558_, 1);
v_capacity_3561_ = lean_ctor_get(v___x_3558_, 2);
v_buf_3562_ = lean_ctor_get(v___x_3558_, 3);
v_bufCount_3563_ = lean_ctor_get(v___x_3558_, 4);
v_sendIdx_3564_ = lean_ctor_get(v___x_3558_, 5);
v_recvIdx_3565_ = lean_ctor_get(v___x_3558_, 6);
v_closed_3566_ = lean_ctor_get_uint8(v___x_3558_, sizeof(void*)*7);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3568_ = v___x_3558_;
v_isShared_3569_ = v_isSharedCheck_3580_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_recvIdx_3565_);
lean_inc(v_sendIdx_3564_);
lean_inc(v_bufCount_3563_);
lean_inc(v_buf_3562_);
lean_inc(v_capacity_3561_);
lean_inc(v_consumers_3560_);
lean_inc(v_producers_3559_);
lean_dec(v___x_3558_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3580_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3570_, 0, v_waiter_3552_);
lean_inc(v___x_3557_);
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3557_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = l_Std_Queue_enqueue___redArg(v___x_3571_, v_consumers_3560_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 1, v___x_3572_);
v___x_3574_ = v___x_3568_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_producers_3559_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3579_, 2, v_capacity_3561_);
lean_ctor_set(v_reuseFailAlloc_3579_, 3, v_buf_3562_);
lean_ctor_set(v_reuseFailAlloc_3579_, 4, v_bufCount_3563_);
lean_ctor_set(v_reuseFailAlloc_3579_, 5, v_sendIdx_3564_);
lean_ctor_set(v_reuseFailAlloc_3579_, 6, v_recvIdx_3565_);
lean_ctor_set_uint8(v_reuseFailAlloc_3579_, sizeof(void*)*7, v_closed_3566_);
v___x_3574_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3575_ = lean_st_ref_put(v___y_3555_, v___x_3574_);
v___x_3576_ = lean_io_promise_result_opt(v___x_3557_);
lean_dec(v___x_3557_);
v___x_3577_ = lean_unsigned_to_nat(0u);
v___x_3578_ = l_EIO_chainTask___redArg(v___x_3576_, v___f_3553_, v___x_3577_, v_____do__lift_3554_);
return v___x_3578_;
}
}
}
else
{
lean_object* v___x_3581_; lean_object* v_lose_3582_; lean_object* v___x_3583_; 
lean_dec_ref(v___f_3553_);
v___x_3581_ = lean_box(v_____do__lift_3554_);
v_lose_3582_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3582_, 0, v___x_3581_);
v___x_3583_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3552_, v_lose_3582_, v___y_3555_);
lean_dec_ref(v_waiter_3552_);
return v___x_3583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3584_, lean_object* v___f_3585_, lean_object* v_____do__lift_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
uint8_t v_____do__lift_4024__boxed_3589_; lean_object* v_res_3590_; 
v_____do__lift_4024__boxed_3589_ = lean_unbox(v_____do__lift_3586_);
v_res_3590_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3584_, v___f_3585_, v_____do__lift_4024__boxed_3589_, v___y_3587_);
lean_dec(v___y_3587_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; lean_object* v_bufCount_3595_; uint8_t v_closed_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3594_ = lean_st_ref_get(v___y_3592_);
v_bufCount_3595_ = lean_ctor_get(v___x_3594_, 4);
lean_inc(v_bufCount_3595_);
v_closed_3596_ = lean_ctor_get_uint8(v___x_3594_, sizeof(void*)*7);
lean_dec(v___x_3594_);
v___x_3597_ = lean_unsigned_to_nat(0u);
v___x_3598_ = lean_nat_dec_eq(v_bufCount_3595_, v___x_3597_);
lean_dec(v_bufCount_3595_);
if (v___x_3598_ == 0)
{
uint8_t v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3599_ = 1;
v___x_3600_ = lean_box(v___x_3599_);
lean_inc(v___y_3592_);
v___x_3601_ = lean_apply_3(v___f_3591_, v___x_3600_, v___y_3592_, lean_box(0));
return v___x_3601_;
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = lean_box(v_closed_3596_);
lean_inc(v___y_3592_);
v___x_3603_ = lean_apply_3(v___f_3591_, v___x_3602_, v___y_3592_, lean_box(0));
return v___x_3603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3604_, v___y_3605_);
lean_dec(v___y_3605_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3610_, lean_object* v_ch_3611_, lean_object* v_x_3612_){
_start:
{
if (lean_obj_tag(v_x_3612_) == 0)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec_ref(v_ch_3611_);
lean_dec_ref(v_waiter_3610_);
v___x_3614_ = lean_box(0);
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
else
{
lean_object* v_val_3616_; uint8_t v___x_3617_; 
v_val_3616_ = lean_ctor_get(v_x_3612_, 0);
v___x_3617_ = lean_unbox(v_val_3616_);
if (v___x_3617_ == 0)
{
lean_object* v___f_3618_; lean_object* v___x_3619_; 
lean_dec_ref(v_ch_3611_);
v___f_3618_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3619_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3610_, v___f_3618_);
lean_dec_ref(v_waiter_3610_);
return v___x_3619_;
}
else
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3611_, v_waiter_3610_);
return v___x_3620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3621_, lean_object* v_ch_3622_, lean_object* v_x_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3621_, v_ch_3622_, v_x_3623_);
lean_dec(v_x_3623_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3626_, lean_object* v_waiter_3627_){
_start:
{
lean_object* v___f_3629_; lean_object* v___f_3630_; lean_object* v___f_3631_; lean_object* v___x_3632_; 
lean_inc_ref(v_ch_3626_);
lean_inc_ref(v_waiter_3627_);
v___f_3629_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3629_, 0, v_waiter_3627_);
lean_closure_set(v___f_3629_, 1, v_ch_3626_);
v___f_3630_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3630_, 0, v_waiter_3627_);
lean_closure_set(v___f_3630_, 1, v___f_3629_);
v___f_3631_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3631_, 0, v___f_3630_);
v___x_3632_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3626_, v___f_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3633_, lean_object* v_waiter_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3633_, v_waiter_3634_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3637_, lean_object* v_ch_3638_, lean_object* v_waiter_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3638_, v_waiter_3639_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3642_, lean_object* v_ch_3643_, lean_object* v_waiter_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3642_, v_ch_3643_, v_waiter_3644_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3647_, lean_object* v_x_3648_){
_start:
{
if (lean_obj_tag(v_x_3648_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3658_; 
lean_dec_ref(v_x_3647_);
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
lean_object* v___x_3659_; 
lean_dec_ref_known(v_x_3648_, 1);
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v_x_3647_);
return v___x_3659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3660_, lean_object* v_x_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3660_, v_x_3661_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3664_, uint8_t v___x_3665_, lean_object* v___f_3666_, lean_object* v_____r_3667_, lean_object* v_st_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = lean_st_ref_swap(v___y_3669_, v_st_3668_);
lean_dec(v___x_3671_);
v___x_3672_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_3673_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3664_, v___x_3665_, v___x_3672_, v___f_3666_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3674_, lean_object* v___x_3675_, lean_object* v___f_3676_, lean_object* v_____r_3677_, lean_object* v_st_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
uint8_t v___x_6434__boxed_3681_; lean_object* v_res_3682_; 
v___x_6434__boxed_3681_ = lean_unbox(v___x_3675_);
v_res_3682_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3674_, v___x_6434__boxed_3681_, v___f_3676_, v_____r_3677_, v_st_3678_, v___y_3679_);
lean_dec(v___y_3679_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3683_, lean_object* v_consumers_3684_, lean_object* v_capacity_3685_, lean_object* v_buf_3686_, lean_object* v___x_3687_, lean_object* v_sendIdx_3688_, lean_object* v___y_3689_, uint8_t v_closed_3690_, lean_object* v___f_3691_, lean_object* v_a_3692_, lean_object* v_x_3693_){
_start:
{
if (lean_obj_tag(v_x_3693_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v___f_3691_);
lean_dec(v___y_3689_);
lean_dec(v_sendIdx_3688_);
lean_dec(v___x_3687_);
lean_dec_ref(v_buf_3686_);
lean_dec(v_capacity_3685_);
lean_dec_ref(v_consumers_3684_);
lean_dec_ref(v_snd_3683_);
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
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_dec_ref_known(v_x_3693_, 1);
v___x_3704_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3704_, 0, v_snd_3683_);
lean_ctor_set(v___x_3704_, 1, v_consumers_3684_);
lean_ctor_set(v___x_3704_, 2, v_capacity_3685_);
lean_ctor_set(v___x_3704_, 3, v_buf_3686_);
lean_ctor_set(v___x_3704_, 4, v___x_3687_);
lean_ctor_set(v___x_3704_, 5, v_sendIdx_3688_);
lean_ctor_set(v___x_3704_, 6, v___y_3689_);
lean_ctor_set_uint8(v___x_3704_, sizeof(void*)*7, v_closed_3690_);
v___x_3705_ = lean_box(0);
lean_inc(v_a_3692_);
v___x_3706_ = lean_apply_4(v___f_3691_, v___x_3705_, v___x_3704_, v_a_3692_, lean_box(0));
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3707_, lean_object* v_consumers_3708_, lean_object* v_capacity_3709_, lean_object* v_buf_3710_, lean_object* v___x_3711_, lean_object* v_sendIdx_3712_, lean_object* v___y_3713_, lean_object* v_closed_3714_, lean_object* v___f_3715_, lean_object* v_a_3716_, lean_object* v_x_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v_closed_boxed_3719_; lean_object* v_res_3720_; 
v_closed_boxed_3719_ = lean_unbox(v_closed_3714_);
v_res_3720_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3707_, v_consumers_3708_, v_capacity_3709_, v_buf_3710_, v___x_3711_, v_sendIdx_3712_, v___y_3713_, v_closed_boxed_3719_, v___f_3715_, v_a_3716_, v_x_3717_);
lean_dec(v_a_3716_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3721_, uint8_t v___x_3722_, lean_object* v_bufCount_3723_, lean_object* v_producers_3724_, lean_object* v_consumers_3725_, lean_object* v_capacity_3726_, lean_object* v_buf_3727_, lean_object* v_sendIdx_3728_, uint8_t v_closed_3729_, uint8_t v___x_3730_, lean_object* v_a_3731_, lean_object* v_recvIdx_3732_, lean_object* v_x_3733_){
_start:
{
if (lean_obj_tag(v_x_3733_) == 0)
{
lean_object* v___x_3735_; 
lean_dec(v_sendIdx_3728_);
lean_dec_ref(v_buf_3727_);
lean_dec(v_capacity_3726_);
lean_dec_ref(v_consumers_3725_);
lean_dec_ref(v_producers_3724_);
lean_dec(v___x_3721_);
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v_x_3733_);
return v___x_3735_;
}
else
{
lean_object* v___f_3736_; lean_object* v___x_3737_; lean_object* v___f_3738_; lean_object* v___y_3740_; lean_object* v___x_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___f_3736_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3736_, 0, v_x_3733_);
v___x_3737_ = lean_box(v___x_3722_);
lean_inc_ref(v___f_3736_);
lean_inc(v___x_3721_);
v___f_3738_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3738_, 0, v___x_3721_);
lean_closure_set(v___f_3738_, 1, v___x_3737_);
lean_closure_set(v___f_3738_, 2, v___f_3736_);
v___x_3763_ = lean_unsigned_to_nat(1u);
v___x_3764_ = lean_nat_add(v_recvIdx_3732_, v___x_3763_);
v___x_3765_ = lean_nat_dec_eq(v___x_3764_, v_capacity_3726_);
if (v___x_3765_ == 0)
{
v___y_3740_ = v___x_3764_;
goto v___jp_3739_;
}
else
{
lean_dec(v___x_3764_);
lean_inc(v___x_3721_);
v___y_3740_ = v___x_3721_;
goto v___jp_3739_;
}
v___jp_3739_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3741_ = lean_unsigned_to_nat(1u);
v___x_3742_ = lean_nat_sub(v_bufCount_3723_, v___x_3741_);
lean_inc(v___y_3740_);
lean_inc(v_sendIdx_3728_);
lean_inc(v___x_3742_);
lean_inc_ref(v_buf_3727_);
lean_inc(v_capacity_3726_);
lean_inc_ref(v_consumers_3725_);
lean_inc_ref(v_producers_3724_);
v___x_3743_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3743_, 0, v_producers_3724_);
lean_ctor_set(v___x_3743_, 1, v_consumers_3725_);
lean_ctor_set(v___x_3743_, 2, v_capacity_3726_);
lean_ctor_set(v___x_3743_, 3, v_buf_3727_);
lean_ctor_set(v___x_3743_, 4, v___x_3742_);
lean_ctor_set(v___x_3743_, 5, v_sendIdx_3728_);
lean_ctor_set(v___x_3743_, 6, v___y_3740_);
lean_ctor_set_uint8(v___x_3743_, sizeof(void*)*7, v_closed_3729_);
v___x_3744_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3724_);
if (lean_obj_tag(v___x_3744_) == 1)
{
lean_object* v_val_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3760_; 
lean_dec_ref_known(v___x_3743_, 7);
lean_dec_ref(v___f_3736_);
v_val_3745_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3747_ = v___x_3744_;
v_isShared_3748_ = v_isSharedCheck_3760_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_val_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3760_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v_fst_3749_; lean_object* v_snd_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___f_3754_; lean_object* v___x_3756_; 
v_fst_3749_ = lean_ctor_get(v_val_3745_, 0);
lean_inc(v_fst_3749_);
v_snd_3750_ = lean_ctor_get(v_val_3745_, 1);
lean_inc(v_snd_3750_);
lean_dec(v_val_3745_);
v___x_3751_ = lean_box(v___x_3730_);
v___x_3752_ = lean_io_promise_resolve(v___x_3751_, v_fst_3749_);
lean_dec(v_fst_3749_);
v___x_3753_ = lean_box(v_closed_3729_);
lean_inc(v_a_3731_);
v___f_3754_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3754_, 0, v_snd_3750_);
lean_closure_set(v___f_3754_, 1, v_consumers_3725_);
lean_closure_set(v___f_3754_, 2, v_capacity_3726_);
lean_closure_set(v___f_3754_, 3, v_buf_3727_);
lean_closure_set(v___f_3754_, 4, v___x_3742_);
lean_closure_set(v___f_3754_, 5, v_sendIdx_3728_);
lean_closure_set(v___f_3754_, 6, v___y_3740_);
lean_closure_set(v___f_3754_, 7, v___x_3753_);
lean_closure_set(v___f_3754_, 8, v___f_3738_);
lean_closure_set(v___f_3754_, 9, v_a_3731_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3752_);
v___x_3756_ = v___x_3747_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3752_);
v___x_3756_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
v___x_3758_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3721_, v___x_3722_, v___x_3757_, v___f_3754_);
return v___x_3758_;
}
}
}
else
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
lean_dec(v___x_3744_);
lean_dec(v___x_3742_);
lean_dec(v___y_3740_);
lean_dec_ref(v___f_3738_);
lean_dec(v_sendIdx_3728_);
lean_dec_ref(v_buf_3727_);
lean_dec(v_capacity_3726_);
lean_dec_ref(v_consumers_3725_);
v___x_3761_ = lean_box(0);
v___x_3762_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3721_, v___x_3722_, v___f_3736_, v___x_3761_, v___x_3743_, v_a_3731_);
return v___x_3762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3766_, lean_object* v___x_3767_, lean_object* v_bufCount_3768_, lean_object* v_producers_3769_, lean_object* v_consumers_3770_, lean_object* v_capacity_3771_, lean_object* v_buf_3772_, lean_object* v_sendIdx_3773_, lean_object* v_closed_3774_, lean_object* v___x_3775_, lean_object* v_a_3776_, lean_object* v_recvIdx_3777_, lean_object* v_x_3778_, lean_object* v___y_3779_){
_start:
{
uint8_t v___x_6503__boxed_3780_; uint8_t v_closed_boxed_3781_; uint8_t v___x_6504__boxed_3782_; lean_object* v_res_3783_; 
v___x_6503__boxed_3780_ = lean_unbox(v___x_3767_);
v_closed_boxed_3781_ = lean_unbox(v_closed_3774_);
v___x_6504__boxed_3782_ = lean_unbox(v___x_3775_);
v_res_3783_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3766_, v___x_6503__boxed_3780_, v_bufCount_3768_, v_producers_3769_, v_consumers_3770_, v_capacity_3771_, v_buf_3772_, v_sendIdx_3773_, v_closed_boxed_3781_, v___x_6504__boxed_3782_, v_a_3776_, v_recvIdx_3777_, v_x_3778_);
lean_dec(v_recvIdx_3777_);
lean_dec(v_a_3776_);
lean_dec(v_bufCount_3768_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3784_, lean_object* v_x_3785_){
_start:
{
if (lean_obj_tag(v_x_3785_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3795_; 
v_a_3787_ = lean_ctor_get(v_x_3785_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_x_3785_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3789_ = v_x_3785_;
v_isShared_3790_ = v_isSharedCheck_3795_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v_x_3785_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3795_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
return v___x_3793_;
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3824_; 
v_a_3796_ = lean_ctor_get(v_x_3785_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_x_3785_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3798_ = v_x_3785_;
v_isShared_3799_ = v_isSharedCheck_3824_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v_x_3785_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3824_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v_producers_3800_; lean_object* v_consumers_3801_; lean_object* v_capacity_3802_; lean_object* v_buf_3803_; lean_object* v_bufCount_3804_; lean_object* v_sendIdx_3805_; lean_object* v_recvIdx_3806_; uint8_t v_closed_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v_producers_3800_ = lean_ctor_get(v_a_3796_, 0);
lean_inc_ref(v_producers_3800_);
v_consumers_3801_ = lean_ctor_get(v_a_3796_, 1);
lean_inc_ref(v_consumers_3801_);
v_capacity_3802_ = lean_ctor_get(v_a_3796_, 2);
lean_inc(v_capacity_3802_);
v_buf_3803_ = lean_ctor_get(v_a_3796_, 3);
lean_inc_ref(v_buf_3803_);
v_bufCount_3804_ = lean_ctor_get(v_a_3796_, 4);
lean_inc(v_bufCount_3804_);
v_sendIdx_3805_ = lean_ctor_get(v_a_3796_, 5);
lean_inc(v_sendIdx_3805_);
v_recvIdx_3806_ = lean_ctor_get(v_a_3796_, 6);
lean_inc(v_recvIdx_3806_);
v_closed_3807_ = lean_ctor_get_uint8(v_a_3796_, sizeof(void*)*7);
lean_dec(v_a_3796_);
v___x_3808_ = lean_unsigned_to_nat(0u);
v___x_3809_ = lean_nat_dec_eq(v_bufCount_3804_, v___x_3808_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___f_3817_; lean_object* v___x_3819_; 
v___x_3810_ = lean_array_fget_borrowed(v_buf_3803_, v_recvIdx_3806_);
v___x_3811_ = lean_box(0);
v___x_3812_ = lean_st_ref_swap(v___x_3810_, v___x_3811_);
v___x_3813_ = 1;
v___x_3814_ = lean_box(v___x_3809_);
v___x_3815_ = lean_box(v_closed_3807_);
v___x_3816_ = lean_box(v___x_3813_);
lean_inc(v_a_3784_);
v___f_3817_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_3817_, 0, v___x_3808_);
lean_closure_set(v___f_3817_, 1, v___x_3814_);
lean_closure_set(v___f_3817_, 2, v_bufCount_3804_);
lean_closure_set(v___f_3817_, 3, v_producers_3800_);
lean_closure_set(v___f_3817_, 4, v_consumers_3801_);
lean_closure_set(v___f_3817_, 5, v_capacity_3802_);
lean_closure_set(v___f_3817_, 6, v_buf_3803_);
lean_closure_set(v___f_3817_, 7, v_sendIdx_3805_);
lean_closure_set(v___f_3817_, 8, v___x_3815_);
lean_closure_set(v___f_3817_, 9, v___x_3816_);
lean_closure_set(v___f_3817_, 10, v_a_3784_);
lean_closure_set(v___f_3817_, 11, v_recvIdx_3806_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v___x_3812_);
v___x_3819_ = v___x_3798_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3812_);
v___x_3819_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
v___x_3821_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3808_, v___x_3809_, v___x_3820_, v___f_3817_);
return v___x_3821_;
}
}
else
{
lean_object* v___x_3823_; 
lean_dec(v_recvIdx_3806_);
lean_dec(v_sendIdx_3805_);
lean_dec(v_bufCount_3804_);
lean_dec_ref(v_buf_3803_);
lean_dec(v_capacity_3802_);
lean_dec_ref(v_consumers_3801_);
lean_dec_ref(v_producers_3800_);
lean_del_object(v___x_3798_);
v___x_3823_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_3823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_3825_, lean_object* v_x_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3825_, v_x_3826_);
lean_dec(v_a_3825_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_3829_){
_start:
{
lean_object* v___x_3831_; lean_object* v___f_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; lean_object* v___x_3837_; 
v___x_3831_ = lean_st_ref_get(v_a_3829_);
lean_inc(v_a_3829_);
v___f_3832_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3832_, 0, v_a_3829_);
v___x_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3831_);
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
v___x_3835_ = lean_unsigned_to_nat(0u);
v___x_3836_ = 0;
v___x_3837_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3835_, v___x_3836_, v___x_3834_, v___f_3832_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3838_);
lean_dec(v_a_3838_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3842_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_3845_, lean_object* v_a_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_3845_, v_a_3846_);
lean_dec(v_a_3846_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_3849_, lean_object* v_x_3850_){
_start:
{
lean_object* v_val_3853_; lean_object* v___x_3855_; 
v___x_3855_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3849_, v_x_3850_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3855_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
lean_ctor_set_tag(v___x_3858_, 1);
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
v_val_3853_ = v___x_3861_;
goto v___jp_3852_;
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
v_a_3864_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3855_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3855_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
lean_ctor_set_tag(v___x_3866_, 0);
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
v_val_3853_ = v___x_3869_;
goto v___jp_3852_;
}
}
}
v___jp_3852_:
{
lean_object* v___x_3854_; 
v___x_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3854_, 0, v_val_3853_);
return v___x_3854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_3872_, lean_object* v_x_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_3872_, v_x_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v_x_3876_){
_start:
{
uint8_t v___y_3879_; 
if (lean_obj_tag(v_x_3876_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3891_; 
v_a_3883_ = lean_ctor_get(v_x_3876_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_x_3876_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3885_ = v_x_3876_;
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v_x_3876_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
return v___x_3889_;
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v_bufCount_3893_; uint8_t v_closed_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; 
v_a_3892_ = lean_ctor_get(v_x_3876_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v_x_3876_, 1);
v_bufCount_3893_ = lean_ctor_get(v_a_3892_, 4);
lean_inc(v_bufCount_3893_);
v_closed_3894_ = lean_ctor_get_uint8(v_a_3892_, sizeof(void*)*7);
lean_dec(v_a_3892_);
v___x_3895_ = lean_unsigned_to_nat(0u);
v___x_3896_ = lean_nat_dec_eq(v_bufCount_3893_, v___x_3895_);
lean_dec(v_bufCount_3893_);
if (v___x_3896_ == 0)
{
uint8_t v___x_3897_; 
v___x_3897_ = 1;
v___y_3879_ = v___x_3897_;
goto v___jp_3878_;
}
else
{
v___y_3879_ = v_closed_3894_;
goto v___jp_3878_;
}
}
v___jp_3878_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_box(v___y_3879_);
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
return v___x_3882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v_x_3898_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___y_3901_, lean_object* v___f_3902_, lean_object* v_x_3903_){
_start:
{
if (lean_obj_tag(v_x_3903_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3913_; 
lean_dec_ref(v___f_3902_);
v_a_3905_ = lean_ctor_get(v_x_3903_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_x_3903_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3907_ = v_x_3903_;
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v_x_3903_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
return v___x_3911_;
}
}
}
else
{
lean_object* v_a_3914_; uint8_t v___x_3915_; 
v_a_3914_ = lean_ctor_get(v_x_3903_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v_x_3903_, 1);
v___x_3915_ = lean_unbox(v_a_3914_);
lean_dec(v_a_3914_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; 
lean_dec_ref(v___f_3902_);
v___x_3916_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_3916_;
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; 
v___x_3917_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_3901_);
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = 0;
v___x_3920_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3918_, v___x_3919_, v___x_3917_, v___f_3902_);
return v___x_3920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___y_3921_, lean_object* v___f_3922_, lean_object* v_x_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___y_3921_, v___f_3922_, v_x_3923_);
lean_dec(v___y_3921_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_3926_, lean_object* v___f_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; uint8_t v___x_3934_; lean_object* v___x_3935_; lean_object* v___f_3936_; lean_object* v___x_3937_; 
v___x_3930_ = lean_st_ref_get(v___y_3928_);
v___x_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
v___x_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
v___x_3933_ = lean_unsigned_to_nat(0u);
v___x_3934_ = 0;
v___x_3935_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3933_, v___x_3934_, v___x_3932_, v___f_3926_);
lean_inc(v___y_3928_);
v___f_3936_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3936_, 0, v___y_3928_);
lean_closure_set(v___f_3936_, 1, v___f_3927_);
v___x_3937_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3933_, v___x_3934_, v___x_3935_, v___f_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_3938_, lean_object* v___f_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_3938_, v___f_3939_, v___y_3940_);
lean_dec(v___y_3940_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_3943_, lean_object* v_capacity_3944_, lean_object* v_buf_3945_, lean_object* v_bufCount_3946_, lean_object* v_sendIdx_3947_, lean_object* v_recvIdx_3948_, uint8_t v_closed_3949_, lean_object* v___y_3950_, lean_object* v_x_3951_){
_start:
{
if (lean_obj_tag(v_x_3951_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v_recvIdx_3948_);
lean_dec(v_sendIdx_3947_);
lean_dec(v_bufCount_3946_);
lean_dec_ref(v_buf_3945_);
lean_dec(v_capacity_3944_);
lean_dec_ref(v_producers_3943_);
v_a_3953_ = lean_ctor_get(v_x_3951_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_x_3951_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3955_ = v_x_3951_;
v_isShared_3956_ = v_isSharedCheck_3961_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v_x_3951_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3961_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3959_; 
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_a_3962_ = lean_ctor_get(v_x_3951_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v_x_3951_, 1);
v___x_3963_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3963_, 0, v_producers_3943_);
lean_ctor_set(v___x_3963_, 1, v_a_3962_);
lean_ctor_set(v___x_3963_, 2, v_capacity_3944_);
lean_ctor_set(v___x_3963_, 3, v_buf_3945_);
lean_ctor_set(v___x_3963_, 4, v_bufCount_3946_);
lean_ctor_set(v___x_3963_, 5, v_sendIdx_3947_);
lean_ctor_set(v___x_3963_, 6, v_recvIdx_3948_);
lean_ctor_set_uint8(v___x_3963_, sizeof(void*)*7, v_closed_3949_);
v___x_3964_ = lean_st_ref_swap(v___y_3950_, v___x_3963_);
lean_dec(v___x_3964_);
v___x_3965_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_3966_, lean_object* v_capacity_3967_, lean_object* v_buf_3968_, lean_object* v_bufCount_3969_, lean_object* v_sendIdx_3970_, lean_object* v_recvIdx_3971_, lean_object* v_closed_3972_, lean_object* v___y_3973_, lean_object* v_x_3974_, lean_object* v___y_3975_){
_start:
{
uint8_t v_closed_boxed_3976_; lean_object* v_res_3977_; 
v_closed_boxed_3976_ = lean_unbox(v_closed_3972_);
v_res_3977_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_3966_, v_capacity_3967_, v_buf_3968_, v_bufCount_3969_, v_sendIdx_3970_, v_recvIdx_3971_, v_closed_boxed_3976_, v___y_3973_, v_x_3974_);
lean_dec(v___y_3973_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_3978_, lean_object* v_x_3979_, lean_object* v_head_3980_, lean_object* v_x_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_3978_, v_x_3979_, v_head_3980_, v_x_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_3984_, lean_object* v_x_3985_){
_start:
{
if (lean_obj_tag(v_x_3984_) == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3987_, 0, v_x_3985_);
v___x_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
return v___x_3988_;
}
else
{
lean_object* v_head_3989_; lean_object* v_tail_3990_; lean_object* v_waiter_3991_; lean_object* v___f_3992_; lean_object* v_val_3994_; 
v_head_3989_ = lean_ctor_get(v_x_3984_, 0);
lean_inc(v_head_3989_);
v_tail_3990_ = lean_ctor_get(v_x_3984_, 1);
lean_inc(v_tail_3990_);
lean_dec_ref_known(v_x_3984_, 2);
v_waiter_3991_ = lean_ctor_get(v_head_3989_, 1);
lean_inc(v_waiter_3991_);
v___f_3992_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3992_, 0, v_tail_3990_);
lean_closure_set(v___f_3992_, 1, v_x_3985_);
lean_closure_set(v___f_3992_, 2, v_head_3989_);
if (lean_obj_tag(v_waiter_3991_) == 0)
{
lean_object* v___x_3998_; 
v___x_3998_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_3994_ = v___x_3998_;
goto v___jp_3993_;
}
else
{
lean_object* v_val_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4013_; 
v_val_3999_ = lean_ctor_get(v_waiter_3991_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_waiter_3991_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4001_ = v_waiter_3991_;
v_isShared_4002_ = v_isSharedCheck_4013_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_val_3999_);
lean_dec(v_waiter_3991_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4013_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v_finished_4003_; lean_object* v___x_4004_; lean_object* v___f_4005_; lean_object* v___x_4007_; 
v_finished_4003_ = lean_ctor_get(v_val_3999_, 0);
lean_inc(v_finished_4003_);
lean_dec(v_val_3999_);
v___x_4004_ = lean_st_ref_get(v_finished_4003_);
lean_dec(v_finished_4003_);
v___f_4005_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_4004_);
v___x_4007_ = v___x_4001_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4004_);
v___x_4007_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; lean_object* v___x_4011_; 
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
v___x_4009_ = lean_unsigned_to_nat(0u);
v___x_4010_ = 0;
v___x_4011_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4009_, v___x_4010_, v___x_4008_, v___f_4005_);
v_val_3994_ = v___x_4011_;
goto v___jp_3993_;
}
}
}
v___jp_3993_:
{
lean_object* v___x_3995_; uint8_t v___x_3996_; lean_object* v___x_3997_; 
v___x_3995_ = lean_unsigned_to_nat(0u);
v___x_3996_ = 0;
v___x_3997_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3995_, v___x_3996_, v_val_3994_, v___f_3992_);
return v___x_3997_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_4014_, lean_object* v_x_4015_, lean_object* v_head_4016_, lean_object* v_x_4017_){
_start:
{
if (lean_obj_tag(v_x_4017_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4027_; 
lean_dec_ref(v_head_4016_);
lean_dec(v_x_4015_);
lean_dec(v_tail_4014_);
v_a_4019_ = lean_ctor_get(v_x_4017_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v_x_4017_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4021_ = v_x_4017_;
v_isShared_4022_ = v_isSharedCheck_4027_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v_x_4017_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4027_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
return v___x_4025_;
}
}
}
else
{
lean_object* v_a_4028_; uint8_t v___x_4029_; 
v_a_4028_ = lean_ctor_get(v_x_4017_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v_x_4017_, 1);
v___x_4029_ = lean_unbox(v_a_4028_);
lean_dec(v_a_4028_);
if (v___x_4029_ == 0)
{
lean_object* v___x_4030_; 
lean_dec_ref(v_head_4016_);
v___x_4030_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4014_, v_x_4015_);
return v___x_4030_;
}
else
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4031_, 0, v_head_4016_);
lean_ctor_set(v___x_4031_, 1, v_x_4015_);
v___x_4032_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4014_, v___x_4031_);
return v___x_4032_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_4033_, lean_object* v_x_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4033_, v_x_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_4037_){
_start:
{
if (lean_obj_tag(v_x_4037_) == 0)
{
lean_object* v___x_4039_; 
v___x_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4039_, 0, v_x_4037_);
return v___x_4039_;
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4049_; 
v_a_4040_ = lean_ctor_get(v_x_4037_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v_x_4037_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4042_ = v_x_4037_;
v_isShared_4043_ = v_isSharedCheck_4049_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v_x_4037_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4049_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4044_; lean_object* v___x_4046_; 
v___x_4044_ = l_List_reverse___redArg(v_a_4040_);
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v___x_4044_);
v___x_4046_ = v___x_4042_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4044_);
v___x_4046_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4050_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4053_, lean_object* v___x_4054_, lean_object* v_x_4055_){
_start:
{
if (lean_obj_tag(v_x_4055_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4065_; 
lean_dec(v___x_4054_);
lean_dec(v_a_4053_);
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
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4082_; 
v_a_4066_ = lean_ctor_get(v_x_4055_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v_x_4055_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4068_ = v_x_4055_;
v_isShared_4069_ = v_isSharedCheck_4082_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v_x_4055_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4082_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
uint8_t v___x_4070_; 
v___x_4070_ = l_List_isEmpty___redArg(v_a_4053_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4073_; 
lean_dec(v___x_4054_);
v___x_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4071_, 0, v_a_4066_);
lean_ctor_set(v___x_4071_, 1, v_a_4053_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 0, v___x_4071_);
v___x_4073_ = v___x_4068_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4071_);
v___x_4073_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
}
else
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
lean_dec(v_a_4053_);
v___x_4076_ = l_List_reverse___redArg(v_a_4066_);
v___x_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4054_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 0, v___x_4077_);
v___x_4079_ = v___x_4068_;
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
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4083_, lean_object* v___x_4084_, lean_object* v_x_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4083_, v___x_4084_, v_x_4085_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_eList_4088_, lean_object* v___x_4089_, lean_object* v___f_4090_, lean_object* v_x_4091_){
_start:
{
if (lean_obj_tag(v_x_4091_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4101_; 
lean_dec_ref(v___f_4090_);
lean_dec(v___x_4089_);
lean_dec(v_eList_4088_);
v_a_4093_ = lean_ctor_get(v_x_4091_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_x_4091_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4095_ = v_x_4091_;
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v_x_4091_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
lean_object* v___x_4099_; 
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
return v___x_4099_;
}
}
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; lean_object* v___x_4106_; lean_object* v___f_4107_; lean_object* v___x_4108_; 
v_a_4102_ = lean_ctor_get(v_x_4091_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v_x_4091_, 1);
lean_inc(v___x_4089_);
v___x_4103_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4088_, v___x_4089_);
v___x_4104_ = lean_unsigned_to_nat(0u);
v___x_4105_ = 0;
v___x_4106_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4104_, v___x_4105_, v___x_4103_, v___f_4090_);
v___f_4107_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4107_, 0, v_a_4102_);
lean_closure_set(v___f_4107_, 1, v___x_4089_);
v___x_4108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4104_, v___x_4105_, v___x_4106_, v___f_4107_);
return v___x_4108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_eList_4109_, lean_object* v___x_4110_, lean_object* v___f_4111_, lean_object* v_x_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v_eList_4109_, v___x_4110_, v___f_4111_, v_x_4112_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_eList_4119_; lean_object* v_dList_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___f_4123_; lean_object* v___x_4124_; uint8_t v___x_4125_; lean_object* v___x_4126_; lean_object* v___f_4127_; lean_object* v___x_4128_; 
v_eList_4119_ = lean_ctor_get(v_q_4116_, 0);
lean_inc(v_eList_4119_);
v_dList_4120_ = lean_ctor_get(v_q_4116_, 1);
lean_inc(v_dList_4120_);
lean_dec_ref(v_q_4116_);
v___x_4121_ = lean_box(0);
v___x_4122_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4120_, v___x_4121_);
v___f_4123_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4124_ = lean_unsigned_to_nat(0u);
v___x_4125_ = 0;
v___x_4126_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4124_, v___x_4125_, v___x_4122_, v___f_4123_);
v___f_4127_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4127_, 0, v_eList_4119_);
lean_closure_set(v___f_4127_, 1, v___x_4121_);
lean_closure_set(v___f_4127_, 2, v___f_4123_);
v___x_4128_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4124_, v___x_4125_, v___x_4126_, v___f_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4129_, v___y_4130_);
lean_dec(v___y_4130_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4133_, lean_object* v_x_4134_){
_start:
{
if (lean_obj_tag(v_x_4134_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4144_; 
v_a_4136_ = lean_ctor_get(v_x_4134_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_x_4134_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4138_ = v_x_4134_;
v_isShared_4139_ = v_isSharedCheck_4144_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v_x_4134_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4144_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
lean_object* v___x_4142_; 
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
return v___x_4142_;
}
}
}
else
{
lean_object* v_a_4145_; lean_object* v_producers_4146_; lean_object* v_consumers_4147_; lean_object* v_capacity_4148_; lean_object* v_buf_4149_; lean_object* v_bufCount_4150_; lean_object* v_sendIdx_4151_; lean_object* v_recvIdx_4152_; uint8_t v_closed_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___f_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; lean_object* v___x_4159_; 
v_a_4145_ = lean_ctor_get(v_x_4134_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v_x_4134_, 1);
v_producers_4146_ = lean_ctor_get(v_a_4145_, 0);
lean_inc_ref(v_producers_4146_);
v_consumers_4147_ = lean_ctor_get(v_a_4145_, 1);
lean_inc_ref(v_consumers_4147_);
v_capacity_4148_ = lean_ctor_get(v_a_4145_, 2);
lean_inc(v_capacity_4148_);
v_buf_4149_ = lean_ctor_get(v_a_4145_, 3);
lean_inc_ref(v_buf_4149_);
v_bufCount_4150_ = lean_ctor_get(v_a_4145_, 4);
lean_inc(v_bufCount_4150_);
v_sendIdx_4151_ = lean_ctor_get(v_a_4145_, 5);
lean_inc(v_sendIdx_4151_);
v_recvIdx_4152_ = lean_ctor_get(v_a_4145_, 6);
lean_inc(v_recvIdx_4152_);
v_closed_4153_ = lean_ctor_get_uint8(v_a_4145_, sizeof(void*)*7);
lean_dec(v_a_4145_);
v___x_4154_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4147_, v___y_4133_);
v___x_4155_ = lean_box(v_closed_4153_);
lean_inc(v___y_4133_);
v___f_4156_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4156_, 0, v_producers_4146_);
lean_closure_set(v___f_4156_, 1, v_capacity_4148_);
lean_closure_set(v___f_4156_, 2, v_buf_4149_);
lean_closure_set(v___f_4156_, 3, v_bufCount_4150_);
lean_closure_set(v___f_4156_, 4, v_sendIdx_4151_);
lean_closure_set(v___f_4156_, 5, v_recvIdx_4152_);
lean_closure_set(v___f_4156_, 6, v___x_4155_);
lean_closure_set(v___f_4156_, 7, v___y_4133_);
v___x_4157_ = lean_unsigned_to_nat(0u);
v___x_4158_ = 0;
v___x_4159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4157_, v___x_4158_, v___x_4154_, v___f_4156_);
return v___x_4159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4160_, lean_object* v_x_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4160_, v_x_4161_);
lean_dec(v___y_4160_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4164_){
_start:
{
lean_object* v___x_4166_; lean_object* v___f_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; lean_object* v___x_4172_; 
v___x_4166_ = lean_st_ref_get(v___y_4164_);
lean_inc(v___y_4164_);
v___f_4167_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4167_, 0, v___y_4164_);
v___x_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
v___x_4170_ = lean_unsigned_to_nat(0u);
v___x_4171_ = 0;
v___x_4172_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4170_, v___x_4171_, v___x_4169_, v___f_4167_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4173_);
lean_dec(v___y_4173_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4181_){
_start:
{
lean_object* v___f_4182_; lean_object* v___f_4183_; lean_object* v___f_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_inc_ref_n(v_ch_4181_, 2);
v___f_4182_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4182_, 0, v_ch_4181_);
v___f_4183_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___f_4184_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2));
v___x_4185_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4185_, 0, lean_box(0));
lean_closure_set(v___x_4185_, 1, lean_box(0));
lean_closure_set(v___x_4185_, 2, v_ch_4181_);
lean_closure_set(v___x_4185_, 3, v___f_4183_);
v___x_4186_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4186_, 0, lean_box(0));
lean_closure_set(v___x_4186_, 1, lean_box(0));
lean_closure_set(v___x_4186_, 2, v_ch_4181_);
lean_closure_set(v___x_4186_, 3, v___f_4184_);
v___x_4187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4185_);
lean_ctor_set(v___x_4187_, 1, v___f_4182_);
lean_ctor_set(v___x_4187_, 2, v___x_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4188_, lean_object* v_ch_4189_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4191_, lean_object* v_q_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4192_, v___y_4193_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4196_, lean_object* v_q_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4196_, v_q_4197_, v___y_4198_);
lean_dec(v___y_4198_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4201_, lean_object* v_x_4202_, lean_object* v_x_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4202_, v_x_4203_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4207_, lean_object* v_x_4208_, lean_object* v_x_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4207_, v_x_4208_, v_x_4209_, v___y_4210_);
lean_dec(v___y_4210_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg(lean_object* v_x_4213_){
_start:
{
switch(lean_obj_tag(v_x_4213_))
{
case 0:
{
lean_object* v___x_4214_; 
v___x_4214_ = lean_unsigned_to_nat(0u);
return v___x_4214_;
}
case 1:
{
lean_object* v___x_4215_; 
v___x_4215_ = lean_unsigned_to_nat(1u);
return v___x_4215_;
}
default: 
{
lean_object* v___x_4216_; 
v___x_4216_ = lean_unsigned_to_nat(2u);
return v___x_4216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(lean_object* v_x_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4217_);
lean_dec_ref(v_x_4217_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx(lean_object* v_00_u03b1_4219_, lean_object* v_x_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___boxed(lean_object* v_00_u03b1_4222_, lean_object* v_x_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Std_CloseableChannel_Flavors_ctorIdx(v_00_u03b1_4222_, v_x_4223_);
lean_dec_ref(v_x_4223_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4225_, lean_object* v_k_4226_){
_start:
{
lean_object* v_ch_4227_; lean_object* v___x_4228_; 
v_ch_4227_ = lean_ctor_get(v_t_4225_, 0);
lean_inc_ref(v_ch_4227_);
lean_dec_ref(v_t_4225_);
v___x_4228_ = lean_apply_1(v_k_4226_, v_ch_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4229_, lean_object* v_motive_4230_, lean_object* v_ctorIdx_4231_, lean_object* v_t_4232_, lean_object* v_h_4233_, lean_object* v_k_4234_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4232_, v_k_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4236_, lean_object* v_motive_4237_, lean_object* v_ctorIdx_4238_, lean_object* v_t_4239_, lean_object* v_h_4240_, lean_object* v_k_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4236_, v_motive_4237_, v_ctorIdx_4238_, v_t_4239_, v_h_4240_, v_k_4241_);
lean_dec(v_ctorIdx_4238_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4243_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4244_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4243_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4246_, lean_object* v_motive_4247_, lean_object* v_t_4248_, lean_object* v_h_4249_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4250_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4248_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4252_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4252_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4255_, lean_object* v_motive_4256_, lean_object* v_t_4257_, lean_object* v_h_4258_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4259_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4257_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4259_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4261_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4262_){
_start:
{
lean_object* v___x_4263_; 
v___x_4263_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4261_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4262_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4264_, lean_object* v_motive_4265_, lean_object* v_t_4266_, lean_object* v_h_4267_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4268_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4266_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4268_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4270_){
_start:
{
if (lean_obj_tag(v_capacity_4270_) == 0)
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
return v___x_4273_;
}
else
{
lean_object* v_val_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4291_; 
v_val_4274_ = lean_ctor_get(v_capacity_4270_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_capacity_4270_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4276_ = v_capacity_4270_;
v_isShared_4277_ = v_isSharedCheck_4291_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_val_4274_);
lean_dec(v_capacity_4270_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4291_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v_zero_4278_; uint8_t v_isZero_4279_; 
v_zero_4278_ = lean_unsigned_to_nat(0u);
v_isZero_4279_ = lean_nat_dec_eq(v_val_4274_, v_zero_4278_);
if (v_isZero_4279_ == 1)
{
lean_object* v___x_4280_; lean_object* v___x_4282_; 
lean_dec(v_val_4274_);
v___x_4280_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 0, v___x_4280_);
v___x_4282_ = v___x_4276_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
else
{
lean_object* v_one_4284_; lean_object* v_n_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4289_; 
v_one_4284_ = lean_unsigned_to_nat(1u);
v_n_4285_ = lean_nat_sub(v_val_4274_, v_one_4284_);
lean_dec(v_val_4274_);
v___x_4286_ = lean_nat_add(v_n_4285_, v_one_4284_);
lean_dec(v_n_4285_);
v___x_4287_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4286_);
if (v_isShared_4277_ == 0)
{
lean_ctor_set_tag(v___x_4276_, 2);
lean_ctor_set(v___x_4276_, 0, v___x_4287_);
v___x_4289_ = v___x_4276_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Std_CloseableChannel_new___redArg(v_capacity_4292_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4295_, lean_object* v_capacity_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Std_CloseableChannel_new___redArg(v_capacity_4296_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4299_, lean_object* v_capacity_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Std_CloseableChannel_new(v_00_u03b1_4299_, v_capacity_4300_);
return v_res_4302_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4303_, lean_object* v_v_4304_){
_start:
{
switch(lean_obj_tag(v_ch_4303_))
{
case 0:
{
lean_object* v_ch_4306_; uint8_t v___x_4307_; 
v_ch_4306_ = lean_ctor_get(v_ch_4303_, 0);
lean_inc_ref(v_ch_4306_);
lean_dec_ref_known(v_ch_4303_, 1);
v___x_4307_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4306_, v_v_4304_);
return v___x_4307_;
}
case 1:
{
lean_object* v_ch_4308_; uint8_t v___x_4309_; 
v_ch_4308_ = lean_ctor_get(v_ch_4303_, 0);
lean_inc_ref(v_ch_4308_);
lean_dec_ref_known(v_ch_4303_, 1);
v___x_4309_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4308_, v_v_4304_);
return v___x_4309_;
}
default: 
{
lean_object* v_ch_4310_; uint8_t v___x_4311_; 
v_ch_4310_ = lean_ctor_get(v_ch_4303_, 0);
lean_inc_ref(v_ch_4310_);
lean_dec_ref_known(v_ch_4303_, 1);
v___x_4311_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4310_, v_v_4304_);
return v___x_4311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4312_, lean_object* v_v_4313_, lean_object* v_a_4314_){
_start:
{
uint8_t v_res_4315_; lean_object* v_r_4316_; 
v_res_4315_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4312_, v_v_4313_);
v_r_4316_ = lean_box(v_res_4315_);
return v_r_4316_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4317_, lean_object* v_ch_4318_, lean_object* v_v_4319_){
_start:
{
uint8_t v___x_4321_; 
v___x_4321_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4318_, v_v_4319_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4322_, lean_object* v_ch_4323_, lean_object* v_v_4324_, lean_object* v_a_4325_){
_start:
{
uint8_t v_res_4326_; lean_object* v_r_4327_; 
v_res_4326_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4322_, v_ch_4323_, v_v_4324_);
v_r_4327_ = lean_box(v_res_4326_);
return v_r_4327_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4328_, lean_object* v_v_4329_){
_start:
{
switch(lean_obj_tag(v_ch_4328_))
{
case 0:
{
lean_object* v_ch_4331_; lean_object* v___x_4332_; 
v_ch_4331_ = lean_ctor_get(v_ch_4328_, 0);
lean_inc_ref(v_ch_4331_);
lean_dec_ref_known(v_ch_4328_, 1);
v___x_4332_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4331_, v_v_4329_);
return v___x_4332_;
}
case 1:
{
lean_object* v_ch_4333_; lean_object* v___x_4334_; 
v_ch_4333_ = lean_ctor_get(v_ch_4328_, 0);
lean_inc_ref(v_ch_4333_);
lean_dec_ref_known(v_ch_4328_, 1);
v___x_4334_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4333_, v_v_4329_);
return v___x_4334_;
}
default: 
{
lean_object* v_ch_4335_; lean_object* v___x_4336_; 
v_ch_4335_ = lean_ctor_get(v_ch_4328_, 0);
lean_inc_ref(v_ch_4335_);
lean_dec_ref_known(v_ch_4328_, 1);
v___x_4336_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4335_, v_v_4329_);
return v___x_4336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4337_, lean_object* v_v_4338_, lean_object* v_a_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_Std_CloseableChannel_send___redArg(v_ch_4337_, v_v_4338_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4341_, lean_object* v_ch_4342_, lean_object* v_v_4343_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = l_Std_CloseableChannel_send___redArg(v_ch_4342_, v_v_4343_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4346_, lean_object* v_ch_4347_, lean_object* v_v_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Std_CloseableChannel_send(v_00_u03b1_4346_, v_ch_4347_, v_v_4348_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4351_){
_start:
{
switch(lean_obj_tag(v_ch_4351_))
{
case 0:
{
lean_object* v_ch_4353_; lean_object* v___x_4354_; 
v_ch_4353_ = lean_ctor_get(v_ch_4351_, 0);
lean_inc_ref(v_ch_4353_);
lean_dec_ref_known(v_ch_4351_, 1);
v___x_4354_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4353_);
return v___x_4354_;
}
case 1:
{
lean_object* v_ch_4355_; lean_object* v___x_4356_; 
v_ch_4355_ = lean_ctor_get(v_ch_4351_, 0);
lean_inc_ref(v_ch_4355_);
lean_dec_ref_known(v_ch_4351_, 1);
v___x_4356_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4355_);
return v___x_4356_;
}
default: 
{
lean_object* v_ch_4357_; lean_object* v___x_4358_; 
v_ch_4357_ = lean_ctor_get(v_ch_4351_, 0);
lean_inc_ref(v_ch_4357_);
lean_dec_ref_known(v_ch_4351_, 1);
v___x_4358_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4357_);
return v___x_4358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Std_CloseableChannel_close___redArg(v_ch_4359_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4362_, lean_object* v_ch_4363_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Std_CloseableChannel_close___redArg(v_ch_4363_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4366_, lean_object* v_ch_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Std_CloseableChannel_close(v_00_u03b1_4366_, v_ch_4367_);
return v_res_4369_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4370_){
_start:
{
switch(lean_obj_tag(v_ch_4370_))
{
case 0:
{
lean_object* v_ch_4372_; uint8_t v___x_4373_; 
v_ch_4372_ = lean_ctor_get(v_ch_4370_, 0);
lean_inc_ref(v_ch_4372_);
lean_dec_ref_known(v_ch_4370_, 1);
v___x_4373_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4372_);
return v___x_4373_;
}
case 1:
{
lean_object* v_ch_4374_; uint8_t v___x_4375_; 
v_ch_4374_ = lean_ctor_get(v_ch_4370_, 0);
lean_inc_ref(v_ch_4374_);
lean_dec_ref_known(v_ch_4370_, 1);
v___x_4375_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4374_);
return v___x_4375_;
}
default: 
{
lean_object* v_ch_4376_; uint8_t v___x_4377_; 
v_ch_4376_ = lean_ctor_get(v_ch_4370_, 0);
lean_inc_ref(v_ch_4376_);
lean_dec_ref_known(v_ch_4370_, 1);
v___x_4377_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4376_);
return v___x_4377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4378_, lean_object* v_a_4379_){
_start:
{
uint8_t v_res_4380_; lean_object* v_r_4381_; 
v_res_4380_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4378_);
v_r_4381_ = lean_box(v_res_4380_);
return v_r_4381_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4382_, lean_object* v_ch_4383_){
_start:
{
uint8_t v___x_4385_; 
v___x_4385_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4383_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4386_, lean_object* v_ch_4387_, lean_object* v_a_4388_){
_start:
{
uint8_t v_res_4389_; lean_object* v_r_4390_; 
v_res_4389_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4386_, v_ch_4387_);
v_r_4390_ = lean_box(v_res_4389_);
return v_r_4390_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4391_){
_start:
{
switch(lean_obj_tag(v_ch_4391_))
{
case 0:
{
lean_object* v_ch_4393_; lean_object* v___x_4394_; 
v_ch_4393_ = lean_ctor_get(v_ch_4391_, 0);
lean_inc_ref(v_ch_4393_);
lean_dec_ref_known(v_ch_4391_, 1);
v___x_4394_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4393_);
return v___x_4394_;
}
case 1:
{
lean_object* v_ch_4395_; lean_object* v___x_4396_; 
v_ch_4395_ = lean_ctor_get(v_ch_4391_, 0);
lean_inc_ref(v_ch_4395_);
lean_dec_ref_known(v_ch_4391_, 1);
v___x_4396_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4395_);
return v___x_4396_;
}
default: 
{
lean_object* v_ch_4397_; lean_object* v___x_4398_; 
v_ch_4397_ = lean_ctor_get(v_ch_4391_, 0);
lean_inc_ref(v_ch_4397_);
lean_dec_ref_known(v_ch_4391_, 1);
v___x_4398_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4397_);
return v___x_4398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4399_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4402_, lean_object* v_ch_4403_){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4403_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4406_, lean_object* v_ch_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4406_, v_ch_4407_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4410_){
_start:
{
switch(lean_obj_tag(v_ch_4410_))
{
case 0:
{
lean_object* v_ch_4412_; lean_object* v___x_4413_; 
v_ch_4412_ = lean_ctor_get(v_ch_4410_, 0);
lean_inc_ref(v_ch_4412_);
lean_dec_ref_known(v_ch_4410_, 1);
v___x_4413_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4412_);
return v___x_4413_;
}
case 1:
{
lean_object* v_ch_4414_; lean_object* v___x_4415_; 
v_ch_4414_ = lean_ctor_get(v_ch_4410_, 0);
lean_inc_ref(v_ch_4414_);
lean_dec_ref_known(v_ch_4410_, 1);
v___x_4415_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4414_);
return v___x_4415_;
}
default: 
{
lean_object* v_ch_4416_; lean_object* v___x_4417_; 
v_ch_4416_ = lean_ctor_get(v_ch_4410_, 0);
lean_inc_ref(v_ch_4416_);
lean_dec_ref_known(v_ch_4410_, 1);
v___x_4417_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4416_);
return v___x_4417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4418_, lean_object* v_a_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l_Std_CloseableChannel_recv___redArg(v_ch_4418_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4421_, lean_object* v_ch_4422_){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Std_CloseableChannel_recv___redArg(v_ch_4422_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4425_, lean_object* v_ch_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Std_CloseableChannel_recv(v_00_u03b1_4425_, v_ch_4426_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4429_){
_start:
{
switch(lean_obj_tag(v_ch_4429_))
{
case 0:
{
lean_object* v_ch_4430_; lean_object* v___x_4431_; 
v_ch_4430_ = lean_ctor_get(v_ch_4429_, 0);
lean_inc_ref(v_ch_4430_);
lean_dec_ref_known(v_ch_4429_, 1);
v___x_4431_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4430_);
return v___x_4431_;
}
case 1:
{
lean_object* v_ch_4432_; lean_object* v___x_4433_; 
v_ch_4432_ = lean_ctor_get(v_ch_4429_, 0);
lean_inc_ref(v_ch_4432_);
lean_dec_ref_known(v_ch_4429_, 1);
v___x_4433_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4432_);
return v___x_4433_;
}
default: 
{
lean_object* v_ch_4434_; lean_object* v___x_4435_; 
v_ch_4434_ = lean_ctor_get(v_ch_4429_, 0);
lean_inc_ref(v_ch_4434_);
lean_dec_ref_known(v_ch_4429_, 1);
v___x_4435_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4434_);
return v___x_4435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4436_, lean_object* v_ch_4437_){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4437_);
return v___x_4438_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = lean_box(0);
v___x_4440_ = lean_task_pure(v___x_4439_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4441_, lean_object* v_ch_4442_, lean_object* v_prio_4443_, lean_object* v_x_4444_){
_start:
{
if (lean_obj_tag(v_x_4444_) == 0)
{
lean_object* v___x_4446_; 
lean_dec(v_prio_4443_);
lean_dec_ref(v_ch_4442_);
lean_dec_ref(v_f_4441_);
v___x_4446_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4446_;
}
else
{
lean_object* v_val_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v_val_4447_ = lean_ctor_get(v_x_4444_, 0);
lean_inc(v_val_4447_);
lean_dec_ref_known(v_x_4444_, 1);
lean_inc_ref(v_f_4441_);
v___x_4448_ = lean_apply_2(v_f_4441_, v_val_4447_, lean_box(0));
v___x_4449_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4441_, v_ch_4442_, v_prio_4443_);
return v___x_4449_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4450_, lean_object* v_ch_4451_, lean_object* v_prio_4452_, lean_object* v_x_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4450_, v_ch_4451_, v_prio_4452_, v_x_4453_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4456_, lean_object* v_ch_4457_, lean_object* v_prio_4458_){
_start:
{
lean_object* v___x_4460_; lean_object* v___f_4461_; uint8_t v___x_4462_; lean_object* v___x_4463_; 
lean_inc_ref(v_ch_4457_);
v___x_4460_ = l_Std_CloseableChannel_recv___redArg(v_ch_4457_);
lean_inc(v_prio_4458_);
v___f_4461_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4461_, 0, v_f_4456_);
lean_closure_set(v___f_4461_, 1, v_ch_4457_);
lean_closure_set(v___f_4461_, 2, v_prio_4458_);
v___x_4462_ = 0;
v___x_4463_ = lean_io_bind_task(v___x_4460_, v___f_4461_, v_prio_4458_, v___x_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4464_, lean_object* v_ch_4465_, lean_object* v_prio_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4464_, v_ch_4465_, v_prio_4466_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4469_, lean_object* v_f_4470_, lean_object* v_ch_4471_, lean_object* v_prio_4472_){
_start:
{
lean_object* v___x_4474_; 
v___x_4474_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4470_, v_ch_4471_, v_prio_4472_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4475_, lean_object* v_f_4476_, lean_object* v_ch_4477_, lean_object* v_prio_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4475_, v_f_4476_, v_ch_4477_, v_prio_4478_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(lean_object* v_x_4481_){
_start:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4483_ = lean_box(0);
v___x_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed(lean_object* v_x_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(v_x_4485_);
lean_dec_ref(v_x_4485_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4493_, lean_object* v_inst_4494_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4496_, lean_object* v_inst_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4496_, v_inst_4497_);
lean_dec(v_inst_4497_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_4499_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4500_, 0, v_a_4499_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_4501_, lean_object* v_x_4502_){
_start:
{
if (lean_obj_tag(v_x_4502_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4512_; 
lean_dec_ref(v___f_4501_);
v_a_4504_ = lean_ctor_get(v_x_4502_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_x_4502_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4506_ = v_x_4502_;
v_isShared_4507_ = v_isSharedCheck_4512_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v_x_4502_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4512_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
lean_object* v___x_4510_; 
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
}
}
else
{
lean_object* v_a_4513_; 
v_a_4513_ = lean_ctor_get(v_x_4502_, 0);
lean_inc(v_a_4513_);
lean_dec_ref_known(v_x_4502_, 1);
if (lean_obj_tag(v_a_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4522_; 
lean_dec_ref(v___f_4501_);
v_a_4514_ = lean_ctor_get(v_a_4513_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v_a_4513_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4516_ = v_a_4513_;
v_isShared_4517_ = v_isSharedCheck_4522_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v_a_4513_);
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
lean_object* v_a_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v_a_4523_ = lean_ctor_get(v_a_4513_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v_a_4513_, 1);
v___x_4524_ = lean_unsigned_to_nat(0u);
v___x_4525_ = 0;
v___x_4526_ = lean_task_map(v___f_4501_, v_a_4523_, v___x_4524_, v___x_4525_);
v___x_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
return v___x_4527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_4528_, lean_object* v_x_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(v___f_4528_, v_x_4529_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_4532_, lean_object* v_receiver_4533_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; lean_object* v___x_4541_; 
v___x_4535_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4533_);
v___x_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
v___x_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
v___x_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4537_);
v___x_4539_ = lean_unsigned_to_nat(0u);
v___x_4540_ = 0;
v___x_4541_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4539_, v___x_4540_, v___x_4538_, v___f_4532_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_4542_, lean_object* v_receiver_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(v___f_4542_, v_receiver_4543_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4551_, lean_object* v_inst_4552_){
_start:
{
lean_object* v___f_4553_; 
v___f_4553_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2));
return v___f_4553_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4554_, lean_object* v_inst_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4554_, v_inst_4555_);
lean_dec(v_inst_4555_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_4558_, lean_object* v_x_4559_){
_start:
{
if (lean_obj_tag(v_x_4559_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref(v___f_4558_);
v_a_4561_ = lean_ctor_get(v_x_4559_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_x_4559_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4563_ = v_x_4559_;
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v_x_4559_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
lean_object* v___x_4567_; 
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
return v___x_4567_;
}
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; uint8_t v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v_a_4570_ = lean_ctor_get(v_x_4559_, 0);
lean_inc(v_a_4570_);
lean_dec_ref_known(v_x_4559_, 1);
v___x_4571_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0));
v___x_4572_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4572_, 0, lean_box(0));
lean_closure_set(v___x_4572_, 1, lean_box(0));
lean_closure_set(v___x_4572_, 2, lean_box(0));
lean_closure_set(v___x_4572_, 3, v___x_4571_);
lean_closure_set(v___x_4572_, 4, v___f_4558_);
v___x_4573_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4573_, 0, lean_box(0));
lean_closure_set(v___x_4573_, 1, lean_box(0));
lean_closure_set(v___x_4573_, 2, lean_box(0));
lean_closure_set(v___x_4573_, 3, v___x_4572_);
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = 0;
v___x_4576_ = lean_task_map(v___x_4573_, v_a_4570_, v___x_4574_, v___x_4575_);
v___x_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
return v___x_4577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_4578_, lean_object* v_x_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(v___f_4578_, v_x_4579_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_4582_, lean_object* v_receiver_4583_, lean_object* v_x_4584_){
_start:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; lean_object* v___x_4591_; 
v___x_4586_ = l_Std_CloseableChannel_send___redArg(v_receiver_4583_, v_x_4584_);
v___x_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
v___x_4589_ = lean_unsigned_to_nat(0u);
v___x_4590_ = 0;
v___x_4591_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4589_, v___x_4590_, v___x_4588_, v___f_4582_);
return v___x_4591_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_4592_, lean_object* v_receiver_4593_, lean_object* v_x_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(v___f_4592_, v_receiver_4593_, v_x_4594_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(lean_object* v_x_4597_){
_start:
{
lean_object* v___x_4599_; 
v___x_4599_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v_x_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(v_x_4600_);
lean_dec_ref(v_x_4600_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(lean_object* v___f_4603_, lean_object* v_socket_4604_, lean_object* v_x_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_apply_3(v___f_4603_, v_socket_4604_, v___y_4606_, lean_box(0));
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v___f_4609_, lean_object* v_socket_4610_, lean_object* v_x_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(v___f_4609_, v_socket_4610_, v_x_4611_, v___y_4612_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_4615_, lean_object* v___x_4616_, lean_object* v_socket_4617_, lean_object* v_data_4618_){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; uint8_t v___x_4623_; 
v___x_4620_ = lean_unsigned_to_nat(0u);
v___x_4621_ = lean_array_get_size(v_data_4618_);
v___x_4622_ = lean_box(0);
v___x_4623_ = lean_nat_dec_lt(v___x_4620_, v___x_4621_);
if (v___x_4623_ == 0)
{
lean_object* v___x_4624_; 
lean_dec_ref(v_data_4618_);
lean_dec_ref(v_socket_4617_);
lean_dec_ref(v___x_4616_);
lean_dec_ref(v___f_4615_);
v___x_4624_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4624_;
}
else
{
lean_object* v___f_4625_; uint8_t v___x_4626_; 
v___f_4625_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4625_, 0, v___f_4615_);
lean_closure_set(v___f_4625_, 1, v_socket_4617_);
v___x_4626_ = lean_nat_dec_le(v___x_4621_, v___x_4621_);
if (v___x_4626_ == 0)
{
if (v___x_4623_ == 0)
{
lean_object* v___x_4627_; 
lean_dec_ref(v___f_4625_);
lean_dec_ref(v_data_4618_);
lean_dec_ref(v___x_4616_);
v___x_4627_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4627_;
}
else
{
size_t v___x_4628_; size_t v___x_4629_; lean_object* v___x_753__overap_4630_; lean_object* v___x_4631_; 
v___x_4628_ = ((size_t)0ULL);
v___x_4629_ = lean_usize_of_nat(v___x_4621_);
v___x_753__overap_4630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4616_, v___f_4625_, v_data_4618_, v___x_4628_, v___x_4629_, v___x_4622_);
v___x_4631_ = lean_apply_1(v___x_753__overap_4630_, lean_box(0));
return v___x_4631_;
}
}
else
{
size_t v___x_4632_; size_t v___x_4633_; lean_object* v___x_756__overap_4634_; lean_object* v___x_4635_; 
v___x_4632_ = ((size_t)0ULL);
v___x_4633_ = lean_usize_of_nat(v___x_4621_);
v___x_756__overap_4634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4616_, v___f_4625_, v_data_4618_, v___x_4632_, v___x_4633_, v___x_4622_);
v___x_4635_ = lean_apply_1(v___x_756__overap_4634_, lean_box(0));
return v___x_4635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_4636_, lean_object* v___x_4637_, lean_object* v_socket_4638_, lean_object* v_data_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(v___f_4636_, v___x_4637_, v_socket_4638_, v_data_4639_);
return v_res_4641_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_4647_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_4648_; lean_object* v___f_4649_; lean_object* v___f_4650_; 
v___x_4648_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_4649_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___f_4650_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4650_, 0, v___f_4649_);
lean_closure_set(v___f_4650_, 1, v___x_4648_);
return v___f_4650_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___f_4651_; lean_object* v___f_4652_; lean_object* v___f_4653_; lean_object* v___x_4654_; 
v___f_4651_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_4652_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4);
v___f_4653_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___x_4654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4654_, 0, v___f_4653_);
lean_ctor_set(v___x_4654_, 1, v___f_4652_);
lean_ctor_set(v___x_4654_, 2, v___f_4651_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4655_, lean_object* v_inst_4656_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4658_, lean_object* v_inst_4659_){
_start:
{
lean_object* v_res_4660_; 
v_res_4660_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4658_, v_inst_4659_);
lean_dec(v_inst_4659_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4661_){
_start:
{
lean_inc_ref(v_ch_4661_);
return v_ch_4661_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l_Std_CloseableChannel_sync___redArg(v_ch_4662_);
lean_dec_ref(v_ch_4662_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4664_, lean_object* v_ch_4665_){
_start:
{
lean_inc_ref(v_ch_4665_);
return v_ch_4665_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4666_, lean_object* v_ch_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l_Std_CloseableChannel_sync(v_00_u03b1_4666_, v_ch_4667_);
lean_dec_ref(v_ch_4667_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4669_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l_Std_CloseableChannel_new___redArg(v_capacity_4669_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4672_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4675_, lean_object* v_capacity_4676_){
_start:
{
lean_object* v___x_4678_; 
v___x_4678_ = l_Std_CloseableChannel_new___redArg(v_capacity_4676_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4679_, lean_object* v_capacity_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4679_, v_capacity_4680_);
return v_res_4682_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4683_, lean_object* v_v_4684_){
_start:
{
uint8_t v___x_4686_; 
v___x_4686_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4683_, v_v_4684_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4687_, lean_object* v_v_4688_, lean_object* v_a_4689_){
_start:
{
uint8_t v_res_4690_; lean_object* v_r_4691_; 
v_res_4690_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4687_, v_v_4688_);
v_r_4691_ = lean_box(v_res_4690_);
return v_r_4691_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4692_, lean_object* v_ch_4693_, lean_object* v_v_4694_){
_start:
{
uint8_t v___x_4696_; 
v___x_4696_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4693_, v_v_4694_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4697_, lean_object* v_ch_4698_, lean_object* v_v_4699_, lean_object* v_a_4700_){
_start:
{
uint8_t v_res_4701_; lean_object* v_r_4702_; 
v_res_4701_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4697_, v_ch_4698_, v_v_4699_);
v_r_4702_ = lean_box(v_res_4701_);
return v_r_4702_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4703_, lean_object* v_v_4704_){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = l_Std_CloseableChannel_send___redArg(v_ch_4703_, v_v_4704_);
v___x_4707_ = lean_io_wait(v___x_4706_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v___x_4707_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4707_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
lean_ctor_set_tag(v___x_4710_, 1);
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
else
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4723_; 
v_a_4716_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4718_ = v___x_4707_;
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v___x_4707_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4721_; 
if (v_isShared_4719_ == 0)
{
lean_ctor_set_tag(v___x_4718_, 0);
v___x_4721_ = v___x_4718_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4716_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_4724_, lean_object* v_v_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4724_, v_v_4725_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_4728_, lean_object* v_ch_4729_, lean_object* v_v_4730_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4729_, v_v_4730_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_4733_, lean_object* v_ch_4734_, lean_object* v_v_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_4733_, v_ch_4734_, v_v_4735_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_4738_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l_Std_CloseableChannel_close___redArg(v_ch_4738_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_4741_, lean_object* v_a_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_4741_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_4744_, lean_object* v_ch_4745_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l_Std_CloseableChannel_close___redArg(v_ch_4745_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_4748_, lean_object* v_ch_4749_, lean_object* v_a_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_4748_, v_ch_4749_);
return v_res_4751_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_4752_){
_start:
{
uint8_t v___x_4754_; 
v___x_4754_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4752_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_4755_, lean_object* v_a_4756_){
_start:
{
uint8_t v_res_4757_; lean_object* v_r_4758_; 
v_res_4757_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_4755_);
v_r_4758_ = lean_box(v_res_4757_);
return v_r_4758_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_4759_, lean_object* v_ch_4760_){
_start:
{
uint8_t v___x_4762_; 
v___x_4762_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4760_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_4763_, lean_object* v_ch_4764_, lean_object* v_a_4765_){
_start:
{
uint8_t v_res_4766_; lean_object* v_r_4767_; 
v_res_4766_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_4763_, v_ch_4764_);
v_r_4767_ = lean_box(v_res_4766_);
return v_r_4767_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_4771_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_4774_, lean_object* v_ch_4775_){
_start:
{
lean_object* v___x_4777_; 
v___x_4777_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4775_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_4778_, lean_object* v_ch_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_4778_, v_ch_4779_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_4782_){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = l_Std_CloseableChannel_recv___redArg(v_ch_4782_);
v___x_4785_ = lean_io_wait(v___x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_4786_, lean_object* v_a_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4786_);
return v_res_4788_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_4789_, lean_object* v_ch_4790_){
_start:
{
lean_object* v___x_4792_; 
v___x_4792_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4790_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_4793_, lean_object* v_ch_4794_, lean_object* v_a_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_4793_, v_ch_4794_);
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_4797_, lean_object* v_b_4798_, lean_object* v_f_4799_, lean_object* v_toBind_4800_, lean_object* v___f_4801_, lean_object* v_____do__lift_4802_){
_start:
{
if (lean_obj_tag(v_____do__lift_4802_) == 0)
{
lean_object* v___x_4803_; 
lean_dec(v___f_4801_);
lean_dec(v_toBind_4800_);
lean_dec(v_f_4799_);
v___x_4803_ = lean_apply_2(v_toPure_4797_, lean_box(0), v_b_4798_);
return v___x_4803_;
}
else
{
lean_object* v_val_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
lean_dec(v_toPure_4797_);
v_val_4804_ = lean_ctor_get(v_____do__lift_4802_, 0);
lean_inc(v_val_4804_);
lean_dec_ref_known(v_____do__lift_4802_, 1);
v___x_4805_ = lean_apply_2(v_f_4799_, v_val_4804_, v_b_4798_);
v___x_4806_ = lean_apply_4(v_toBind_4800_, lean_box(0), lean_box(0), v___x_4805_, v___f_4801_);
return v___x_4806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_4807_, lean_object* v_inst_4808_, lean_object* v_ch_4809_, lean_object* v_f_4810_, lean_object* v_b_4811_){
_start:
{
lean_object* v_toApplicative_4812_; lean_object* v_toBind_4813_; lean_object* v_toPure_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___f_4817_; lean_object* v___f_4818_; lean_object* v___x_4819_; 
v_toApplicative_4812_ = lean_ctor_get(v_inst_4807_, 0);
v_toBind_4813_ = lean_ctor_get(v_inst_4807_, 1);
lean_inc_n(v_toBind_4813_, 2);
v_toPure_4814_ = lean_ctor_get(v_toApplicative_4812_, 1);
lean_inc_n(v_toPure_4814_, 2);
lean_inc_ref(v_ch_4809_);
v___x_4815_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_4815_, 0, lean_box(0));
lean_closure_set(v___x_4815_, 1, v_ch_4809_);
lean_inc(v_inst_4808_);
v___x_4816_ = lean_apply_2(v_inst_4808_, lean_box(0), v___x_4815_);
lean_inc(v_f_4810_);
v___f_4817_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4817_, 0, v_toPure_4814_);
lean_closure_set(v___f_4817_, 1, v_inst_4807_);
lean_closure_set(v___f_4817_, 2, v_inst_4808_);
lean_closure_set(v___f_4817_, 3, v_ch_4809_);
lean_closure_set(v___f_4817_, 4, v_f_4810_);
v___f_4818_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_4818_, 0, v_toPure_4814_);
lean_closure_set(v___f_4818_, 1, v_b_4811_);
lean_closure_set(v___f_4818_, 2, v_f_4810_);
lean_closure_set(v___f_4818_, 3, v_toBind_4813_);
lean_closure_set(v___f_4818_, 4, v___f_4817_);
v___x_4819_ = lean_apply_4(v_toBind_4813_, lean_box(0), lean_box(0), v___x_4816_, v___f_4818_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_4820_, lean_object* v_inst_4821_, lean_object* v_inst_4822_, lean_object* v_ch_4823_, lean_object* v_f_4824_, lean_object* v_____do__lift_4825_){
_start:
{
if (lean_obj_tag(v_____do__lift_4825_) == 0)
{
lean_object* v_a_4826_; lean_object* v___x_4827_; 
lean_dec(v_f_4824_);
lean_dec_ref(v_ch_4823_);
lean_dec(v_inst_4822_);
lean_dec_ref(v_inst_4821_);
v_a_4826_ = lean_ctor_get(v_____do__lift_4825_, 0);
lean_inc(v_a_4826_);
lean_dec_ref_known(v_____do__lift_4825_, 1);
v___x_4827_ = lean_apply_2(v_toPure_4820_, lean_box(0), v_a_4826_);
return v___x_4827_;
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4829_; 
lean_dec(v_toPure_4820_);
v_a_4828_ = lean_ctor_get(v_____do__lift_4825_, 0);
lean_inc(v_a_4828_);
lean_dec_ref_known(v_____do__lift_4825_, 1);
v___x_4829_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4821_, v_inst_4822_, v_ch_4823_, v_f_4824_, v_a_4828_);
return v___x_4829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_4830_, lean_object* v_00_u03b1_4831_, lean_object* v_00_u03b2_4832_, lean_object* v_inst_4833_, lean_object* v_inst_4834_, lean_object* v_ch_4835_, lean_object* v_f_4836_, lean_object* v_b_4837_){
_start:
{
lean_object* v___x_4838_; 
v___x_4838_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4833_, v_inst_4834_, v_ch_4835_, v_f_4836_, v_b_4837_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_4839_, lean_object* v_inst_4840_, lean_object* v_ch_4841_, lean_object* v_b_4842_, lean_object* v_f_4843_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4839_, v_inst_4840_, v_ch_4841_, v_f_4843_, v_b_4842_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_4845_, lean_object* v_00_u03b1_4846_, lean_object* v_inst_4847_, lean_object* v_inst_4848_, lean_object* v_00_u03b2_4849_, lean_object* v_ch_4850_, lean_object* v_b_4851_, lean_object* v_f_4852_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4847_, v_inst_4848_, v_ch_4850_, v_f_4852_, v_b_4851_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_4854_, lean_object* v_inst_4855_, lean_object* v_00_u03b2_4856_, lean_object* v_ch_4857_, lean_object* v_b_4858_, lean_object* v_f_4859_){
_start:
{
lean_object* v___x_4860_; 
v___x_4860_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4854_, v_inst_4855_, v_ch_4857_, v_f_4859_, v_b_4858_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_4861_, lean_object* v_inst_4862_){
_start:
{
lean_object* v___f_4863_; 
v___f_4863_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4863_, 0, v_inst_4861_);
lean_closure_set(v___f_4863_, 1, v_inst_4862_);
return v___f_4863_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_4864_, lean_object* v_00_u03b1_4865_, lean_object* v_inst_4866_, lean_object* v_inst_4867_){
_start:
{
lean_object* v___f_4868_; 
v___f_4868_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4868_, 0, v_inst_4866_);
lean_closure_set(v___f_4868_, 1, v_inst_4867_);
return v___f_4868_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_4869_){
_start:
{
lean_object* v___x_4871_; 
v___x_4871_ = l_Std_CloseableChannel_new___redArg(v_capacity_4869_);
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Std_Channel_new___redArg(v_capacity_4872_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_4875_, lean_object* v_capacity_4876_){
_start:
{
lean_object* v___x_4878_; 
v___x_4878_ = l_Std_CloseableChannel_new___redArg(v_capacity_4876_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_4879_, lean_object* v_capacity_4880_, lean_object* v_a_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l_Std_Channel_new(v_00_u03b1_4879_, v_capacity_4880_);
return v_res_4882_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_4883_, lean_object* v_v_4884_){
_start:
{
uint8_t v___x_4886_; 
v___x_4886_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4883_, v_v_4884_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_4887_, lean_object* v_v_4888_, lean_object* v_a_4889_){
_start:
{
uint8_t v_res_4890_; lean_object* v_r_4891_; 
v_res_4890_ = l_Std_Channel_trySend___redArg(v_ch_4887_, v_v_4888_);
v_r_4891_ = lean_box(v_res_4890_);
return v_r_4891_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_4892_, lean_object* v_ch_4893_, lean_object* v_v_4894_){
_start:
{
uint8_t v___x_4896_; 
v___x_4896_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4893_, v_v_4894_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_4897_, lean_object* v_ch_4898_, lean_object* v_v_4899_, lean_object* v_a_4900_){
_start:
{
uint8_t v_res_4901_; lean_object* v_r_4902_; 
v_res_4901_ = l_Std_Channel_trySend(v_00_u03b1_4897_, v_ch_4898_, v_v_4899_);
v_r_4902_ = lean_box(v_res_4901_);
return v_r_4902_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4903_ = lean_box(0);
v___x_4904_ = lean_task_pure(v___x_4903_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_4905_){
_start:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_142__overap_4910_; lean_object* v___x_4911_; 
v___x_4907_ = l_instMonadBaseIO;
v___x_4908_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4909_ = l_instInhabitedOfMonad___redArg(v___x_4907_, v___x_4908_);
v___x_142__overap_4910_ = lean_panic_fn_borrowed(v___x_4909_, v_msg_4905_);
lean_dec(v___x_4909_);
v___x_4911_ = lean_apply_1(v___x_142__overap_4910_, lean_box(0));
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_4912_);
return v_res_4914_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4918_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4919_ = lean_unsigned_to_nat(21u);
v___x_4920_ = lean_unsigned_to_nat(869u);
v___x_4921_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_4922_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4923_ = l_mkPanicMessageWithDecl(v___x_4922_, v___x_4921_, v___x_4920_, v___x_4919_, v___x_4918_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_4924_){
_start:
{
if (lean_obj_tag(v_x_4924_) == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4926_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_4927_ = l_panic___at___00Std_Channel_send_spec__0(v___x_4926_);
return v___x_4927_;
}
else
{
lean_object* v___x_4928_; 
v___x_4928_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4928_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Std_Channel_send___redArg___lam__0(v_x_4929_);
lean_dec_ref(v_x_4929_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_4933_, lean_object* v_v_4934_){
_start:
{
lean_object* v___x_4936_; lean_object* v___f_4937_; lean_object* v___x_4938_; uint8_t v___x_4939_; lean_object* v___x_4940_; 
v___x_4936_ = l_Std_CloseableChannel_send___redArg(v_ch_4933_, v_v_4934_);
v___f_4937_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_4938_ = lean_unsigned_to_nat(0u);
v___x_4939_ = 1;
v___x_4940_ = lean_io_bind_task(v___x_4936_, v___f_4937_, v___x_4938_, v___x_4939_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_4941_, lean_object* v_v_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l_Std_Channel_send___redArg(v_ch_4941_, v_v_4942_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_4945_, lean_object* v_ch_4946_, lean_object* v_v_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Std_Channel_send___redArg(v_ch_4946_, v_v_4947_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_4950_, lean_object* v_ch_4951_, lean_object* v_v_4952_, lean_object* v_a_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l_Std_Channel_send(v_00_u03b1_4950_, v_ch_4951_, v_v_4952_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_4955_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4955_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l_Std_Channel_tryRecv___redArg(v_ch_4958_);
return v_res_4960_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_4961_, lean_object* v_ch_4962_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4962_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_4965_, lean_object* v_ch_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Std_Channel_tryRecv(v_00_u03b1_4965_, v_ch_4966_);
return v_res_4968_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4970_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4971_ = lean_unsigned_to_nat(16u);
v___x_4972_ = lean_unsigned_to_nat(880u);
v___x_4973_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_4974_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4975_ = l_mkPanicMessageWithDecl(v___x_4974_, v___x_4973_, v___x_4972_, v___x_4971_, v___x_4970_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_4976_, lean_object* v_x_4977_){
_start:
{
if (lean_obj_tag(v_x_4977_) == 0)
{
lean_object* v___x_4979_; lean_object* v___x_140__overap_4980_; lean_object* v___x_4981_; 
v___x_4979_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_140__overap_4980_ = l_panic___redArg(v___x_4976_, v___x_4979_);
v___x_4981_ = lean_apply_1(v___x_140__overap_4980_, lean_box(0));
return v___x_4981_;
}
else
{
lean_object* v_val_4982_; lean_object* v___x_4983_; 
v_val_4982_ = lean_ctor_get(v_x_4977_, 0);
lean_inc(v_val_4982_);
lean_dec_ref_known(v_x_4977_, 1);
v___x_4983_ = lean_task_pure(v_val_4982_);
return v___x_4983_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_4984_, lean_object* v_x_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Std_Channel_recv___redArg___lam__0(v___x_4984_, v_x_4985_);
lean_dec_ref(v___x_4984_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_4988_, lean_object* v_ch_4989_){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___f_4995_; lean_object* v___x_4996_; uint8_t v___x_4997_; lean_object* v___x_4998_; 
v___x_4991_ = l_instMonadBaseIO;
v___x_4992_ = l_Std_CloseableChannel_recv___redArg(v_ch_4989_);
v___x_4993_ = lean_task_pure(v_inst_4988_);
v___x_4994_ = l_instInhabitedOfMonad___redArg(v___x_4991_, v___x_4993_);
v___f_4995_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4995_, 0, v___x_4994_);
v___x_4996_ = lean_unsigned_to_nat(0u);
v___x_4997_ = 1;
v___x_4998_ = lean_io_bind_task(v___x_4992_, v___f_4995_, v___x_4996_, v___x_4997_);
return v___x_4998_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_4999_, lean_object* v_ch_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Std_Channel_recv___redArg(v_inst_4999_, v_ch_5000_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_5003_, lean_object* v_inst_5004_, lean_object* v_ch_5005_){
_start:
{
lean_object* v___x_5007_; 
v___x_5007_ = l_Std_Channel_recv___redArg(v_inst_5004_, v_ch_5005_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_5008_, lean_object* v_inst_5009_, lean_object* v_ch_5010_, lean_object* v_a_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Std_Channel_recv(v_00_u03b1_5008_, v_inst_5009_, v_ch_5010_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_5013_){
_start:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5015_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5013_);
v___x_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5016_, 0, v___x_5015_);
v___x_5017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5016_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5018_);
return v_res_5020_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5024_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_5025_ = lean_unsigned_to_nat(14u);
v___x_5026_ = lean_unsigned_to_nat(22u);
v___x_5027_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_5028_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_5029_ = l_mkPanicMessageWithDecl(v___x_5028_, v___x_5027_, v___x_5026_, v___x_5025_, v___x_5024_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_5030_, lean_object* v_inst_5031_, lean_object* v_x_5032_){
_start:
{
lean_object* v___y_5035_; lean_object* v___y_5039_; 
if (lean_obj_tag(v_x_5032_) == 0)
{
lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5041_ = lean_box(0);
v___x_5042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5042_, 0, v___x_5041_);
return v___x_5042_;
}
else
{
lean_object* v_val_5043_; 
v_val_5043_ = lean_ctor_get(v_x_5032_, 0);
lean_inc(v_val_5043_);
lean_dec_ref_known(v_x_5032_, 1);
if (lean_obj_tag(v_val_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
v_a_5044_ = lean_ctor_get(v_val_5043_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v_val_5043_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v_val_5043_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v_val_5043_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
v___y_5035_ = v___x_5049_;
goto v___jp_5034_;
}
}
}
else
{
lean_object* v_a_5052_; 
v_a_5052_ = lean_ctor_get(v_val_5043_, 0);
lean_inc(v_a_5052_);
lean_dec_ref_known(v_val_5043_, 1);
if (lean_obj_tag(v_a_5052_) == 0)
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5054_ = l_panic___redArg(v_inst_5031_, v___x_5053_);
v___y_5039_ = v___x_5054_;
goto v___jp_5038_;
}
else
{
lean_object* v_val_5055_; 
v_val_5055_ = lean_ctor_get(v_a_5052_, 0);
lean_inc(v_val_5055_);
lean_dec_ref_known(v_a_5052_, 1);
v___y_5039_ = v_val_5055_;
goto v___jp_5038_;
}
}
}
v___jp_5034_:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5036_ = lean_io_promise_resolve(v___y_5035_, v_promise_5030_);
v___x_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5036_);
return v___x_5037_;
}
v___jp_5038_:
{
lean_object* v___x_5040_; 
v___x_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5040_, 0, v___y_5039_);
v___y_5035_ = v___x_5040_;
goto v___jp_5034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5056_, lean_object* v_inst_5057_, lean_object* v_x_5058_, lean_object* v___y_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5056_, v_inst_5057_, v_x_5058_);
lean_dec(v_inst_5057_);
lean_dec(v_promise_5056_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5061_, lean_object* v___f_5062_, lean_object* v_x_5063_){
_start:
{
lean_object* v_val_5066_; 
if (lean_obj_tag(v_x_5063_) == 0)
{
lean_object* v___x_5068_; 
lean_dec_ref(v___f_5062_);
v___x_5068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5068_, 0, v_x_5063_);
return v___x_5068_;
}
else
{
lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5084_; 
v_isSharedCheck_5084_ = !lean_is_exclusive(v_x_5063_);
if (v_isSharedCheck_5084_ == 0)
{
lean_object* v_unused_5085_; 
v_unused_5085_ = lean_ctor_get(v_x_5063_, 0);
lean_dec(v_unused_5085_);
v___x_5070_ = v_x_5063_;
v_isShared_5071_ = v_isSharedCheck_5084_;
goto v_resetjp_5069_;
}
else
{
lean_dec(v_x_5063_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5084_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; uint8_t v___x_5074_; lean_object* v___x_5075_; 
v___x_5072_ = lean_io_promise_result_opt(v_a_5061_);
v___x_5073_ = lean_unsigned_to_nat(0u);
v___x_5074_ = 1;
v___x_5075_ = l_EIO_chainTask___redArg(v___x_5072_, v___f_5062_, v___x_5073_, v___x_5074_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_object* v_a_5076_; lean_object* v___x_5078_; 
v_a_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_a_5076_);
lean_dec_ref_known(v___x_5075_, 1);
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 0, v_a_5076_);
v___x_5078_ = v___x_5070_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5076_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
v_val_5066_ = v___x_5078_;
goto v___jp_5065_;
}
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; 
v_a_5080_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_a_5080_);
lean_dec_ref_known(v___x_5075_, 1);
if (v_isShared_5071_ == 0)
{
lean_ctor_set_tag(v___x_5070_, 0);
lean_ctor_set(v___x_5070_, 0, v_a_5080_);
v___x_5082_ = v___x_5070_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5080_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
v_val_5066_ = v___x_5082_;
goto v___jp_5065_;
}
}
}
}
v___jp_5065_:
{
lean_object* v___x_5067_; 
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v_val_5066_);
return v___x_5067_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5086_, lean_object* v___f_5087_, lean_object* v_x_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5086_, v___f_5087_, v_x_5088_);
lean_dec(v_a_5086_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5091_, lean_object* v_finished_5092_, lean_object* v___f_5093_, lean_object* v_x_5094_){
_start:
{
if (lean_obj_tag(v_x_5094_) == 0)
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5104_; 
lean_dec_ref(v___f_5093_);
lean_dec(v_finished_5092_);
lean_dec_ref(v_sel_5091_);
v_a_5096_ = lean_ctor_get(v_x_5094_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v_x_5094_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5098_ = v_x_5094_;
v_isShared_5099_ = v_isSharedCheck_5104_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v_x_5094_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5104_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5101_; 
if (v_isShared_5099_ == 0)
{
v___x_5101_ = v___x_5098_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5096_);
v___x_5101_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
lean_object* v___x_5102_; 
v___x_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5101_);
return v___x_5102_;
}
}
}
else
{
lean_object* v_a_5105_; lean_object* v_registerFn_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___f_5109_; lean_object* v___x_5110_; uint8_t v___x_5111_; lean_object* v___x_5112_; 
v_a_5105_ = lean_ctor_get(v_x_5094_, 0);
lean_inc_n(v_a_5105_, 2);
lean_dec_ref_known(v_x_5094_, 1);
v_registerFn_5106_ = lean_ctor_get(v_sel_5091_, 1);
lean_inc_ref(v_registerFn_5106_);
lean_dec_ref(v_sel_5091_);
v___x_5107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5107_, 0, v_finished_5092_);
lean_ctor_set(v___x_5107_, 1, v_a_5105_);
v___x_5108_ = lean_apply_2(v_registerFn_5106_, v___x_5107_, lean_box(0));
v___f_5109_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5109_, 0, v_a_5105_);
lean_closure_set(v___f_5109_, 1, v___f_5093_);
v___x_5110_ = lean_unsigned_to_nat(0u);
v___x_5111_ = 0;
v___x_5112_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5110_, v___x_5111_, v___x_5108_, v___f_5109_);
return v___x_5112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5113_, lean_object* v_finished_5114_, lean_object* v___f_5115_, lean_object* v_x_5116_, lean_object* v___y_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5113_, v_finished_5114_, v___f_5115_, v_x_5116_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5119_, lean_object* v_sel_5120_, lean_object* v_waiter_5121_){
_start:
{
lean_object* v___x_5123_; lean_object* v_finished_5124_; lean_object* v_promise_5125_; lean_object* v___f_5126_; lean_object* v___f_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; uint8_t v___x_5131_; lean_object* v___x_5132_; 
v___x_5123_ = lean_io_promise_new();
v_finished_5124_ = lean_ctor_get(v_waiter_5121_, 0);
lean_inc(v_finished_5124_);
v_promise_5125_ = lean_ctor_get(v_waiter_5121_, 1);
lean_inc(v_promise_5125_);
lean_dec_ref(v_waiter_5121_);
v___f_5126_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5126_, 0, v_promise_5125_);
lean_closure_set(v___f_5126_, 1, v_inst_5119_);
v___f_5127_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5127_, 0, v_sel_5120_);
lean_closure_set(v___f_5127_, 1, v_finished_5124_);
lean_closure_set(v___f_5127_, 2, v___f_5126_);
v___x_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5123_);
v___x_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
v___x_5130_ = lean_unsigned_to_nat(0u);
v___x_5131_ = 0;
v___x_5132_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5130_, v___x_5131_, v___x_5129_, v___f_5127_);
return v___x_5132_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5133_, lean_object* v_sel_5134_, lean_object* v_waiter_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v_res_5137_; 
v_res_5137_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5133_, v_sel_5134_, v_waiter_5135_);
return v_res_5137_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5138_, lean_object* v_ch_5139_){
_start:
{
lean_object* v_sel_5140_; lean_object* v_unregisterFn_5141_; lean_object* v___f_5142_; lean_object* v___f_5143_; lean_object* v___x_5144_; 
lean_inc_ref(v_ch_5139_);
v_sel_5140_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5139_);
v_unregisterFn_5141_ = lean_ctor_get(v_sel_5140_, 2);
lean_inc_ref(v_unregisterFn_5141_);
v___f_5142_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5142_, 0, v_ch_5139_);
v___f_5143_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5143_, 0, v_inst_5138_);
lean_closure_set(v___f_5143_, 1, v_sel_5140_);
v___x_5144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5144_, 0, v___f_5142_);
lean_ctor_set(v___x_5144_, 1, v___f_5143_);
lean_ctor_set(v___x_5144_, 2, v_unregisterFn_5141_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5145_, lean_object* v_inst_5146_, lean_object* v_ch_5147_){
_start:
{
lean_object* v___x_5148_; 
v___x_5148_ = l_Std_Channel_recvSelector___redArg(v_inst_5146_, v_ch_5147_);
return v___x_5148_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5149_, lean_object* v_inst_5150_, lean_object* v_ch_5151_, lean_object* v_prio_5152_, lean_object* v_v_5153_, lean_object* v___y_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5149_, v_inst_5150_, v_ch_5151_, v_prio_5152_, v_v_5153_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5156_, lean_object* v_f_5157_, lean_object* v_ch_5158_, lean_object* v_prio_5159_){
_start:
{
lean_object* v___x_5161_; lean_object* v___f_5162_; uint8_t v___x_5163_; lean_object* v___x_5164_; 
lean_inc_ref(v_ch_5158_);
lean_inc(v_inst_5156_);
v___x_5161_ = l_Std_Channel_recv___redArg(v_inst_5156_, v_ch_5158_);
lean_inc(v_prio_5159_);
v___f_5162_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5162_, 0, v_f_5157_);
lean_closure_set(v___f_5162_, 1, v_inst_5156_);
lean_closure_set(v___f_5162_, 2, v_ch_5158_);
lean_closure_set(v___f_5162_, 3, v_prio_5159_);
v___x_5163_ = 0;
v___x_5164_ = lean_io_bind_task(v___x_5161_, v___f_5162_, v_prio_5159_, v___x_5163_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5165_, lean_object* v_inst_5166_, lean_object* v_ch_5167_, lean_object* v_prio_5168_, lean_object* v_v_5169_){
_start:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; 
lean_inc_ref(v_f_5165_);
v___x_5171_ = lean_apply_2(v_f_5165_, v_v_5169_, lean_box(0));
v___x_5172_ = l_Std_Channel_forAsync___redArg(v_inst_5166_, v_f_5165_, v_ch_5167_, v_prio_5168_);
return v___x_5172_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5173_, lean_object* v_f_5174_, lean_object* v_ch_5175_, lean_object* v_prio_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Std_Channel_forAsync___redArg(v_inst_5173_, v_f_5174_, v_ch_5175_, v_prio_5176_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5179_, lean_object* v_inst_5180_, lean_object* v_f_5181_, lean_object* v_ch_5182_, lean_object* v_prio_5183_){
_start:
{
lean_object* v___x_5185_; 
v___x_5185_ = l_Std_Channel_forAsync___redArg(v_inst_5180_, v_f_5181_, v_ch_5182_, v_prio_5183_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5186_, lean_object* v_inst_5187_, lean_object* v_f_5188_, lean_object* v_ch_5189_, lean_object* v_prio_5190_, lean_object* v_a_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Std_Channel_forAsync(v_00_u03b1_5186_, v_inst_5187_, v_f_5188_, v_ch_5189_, v_prio_5190_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5193_, lean_object* v_channel_5194_){
_start:
{
lean_object* v___x_5195_; 
v___x_5195_ = l_Std_Channel_recvSelector___redArg(v_inst_5193_, v_channel_5194_);
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5196_){
_start:
{
lean_object* v___f_5197_; lean_object* v___f_5198_; lean_object* v___x_5199_; 
v___f_5197_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5197_, 0, v_inst_5196_);
v___f_5198_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1));
v___x_5199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5199_, 0, v___f_5197_);
lean_ctor_set(v___x_5199_, 1, v___f_5198_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5200_, lean_object* v_inst_5201_){
_start:
{
lean_object* v___x_5202_; 
v___x_5202_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5201_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5203_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5204_, 0, v_a_5203_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5205_, lean_object* v_x_5206_){
_start:
{
if (lean_obj_tag(v_x_5206_) == 0)
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5216_; 
lean_dec_ref(v___f_5205_);
v_a_5208_ = lean_ctor_get(v_x_5206_, 0);
v_isSharedCheck_5216_ = !lean_is_exclusive(v_x_5206_);
if (v_isSharedCheck_5216_ == 0)
{
v___x_5210_ = v_x_5206_;
v_isShared_5211_ = v_isSharedCheck_5216_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v_x_5206_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5216_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
lean_object* v___x_5214_; 
v___x_5214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5214_, 0, v___x_5213_);
return v___x_5214_;
}
}
}
else
{
lean_object* v_a_5217_; 
v_a_5217_ = lean_ctor_get(v_x_5206_, 0);
lean_inc(v_a_5217_);
lean_dec_ref_known(v_x_5206_, 1);
if (lean_obj_tag(v_a_5217_) == 0)
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5226_; 
lean_dec_ref(v___f_5205_);
v_a_5218_ = lean_ctor_get(v_a_5217_, 0);
v_isSharedCheck_5226_ = !lean_is_exclusive(v_a_5217_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5220_ = v_a_5217_;
v_isShared_5221_ = v_isSharedCheck_5226_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v_a_5217_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5226_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_a_5218_);
v___x_5223_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
lean_object* v___x_5224_; 
v___x_5224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5223_);
return v___x_5224_;
}
}
}
else
{
lean_object* v_a_5227_; lean_object* v___x_5228_; uint8_t v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; 
v_a_5227_ = lean_ctor_get(v_a_5217_, 0);
lean_inc(v_a_5227_);
lean_dec_ref_known(v_a_5217_, 1);
v___x_5228_ = lean_unsigned_to_nat(0u);
v___x_5229_ = 0;
v___x_5230_ = lean_task_map(v___f_5205_, v_a_5227_, v___x_5228_, v___x_5229_);
v___x_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5231_, 0, v___x_5230_);
return v___x_5231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5232_, lean_object* v_x_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5232_, v_x_5233_);
return v_res_5235_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5236_, lean_object* v___f_5237_, lean_object* v_receiver_5238_){
_start:
{
lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; uint8_t v___x_5245_; lean_object* v___x_5246_; 
v___x_5240_ = l_Std_Channel_recv___redArg(v_inst_5236_, v_receiver_5238_);
v___x_5241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5240_);
v___x_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5242_, 0, v___x_5241_);
v___x_5243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5242_);
v___x_5244_ = lean_unsigned_to_nat(0u);
v___x_5245_ = 0;
v___x_5246_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5244_, v___x_5245_, v___x_5243_, v___f_5237_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5247_, lean_object* v___f_5248_, lean_object* v_receiver_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5247_, v___f_5248_, v_receiver_5249_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5255_){
_start:
{
lean_object* v___f_5256_; lean_object* v___f_5257_; 
v___f_5256_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5257_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5257_, 0, v_inst_5255_);
lean_closure_set(v___f_5257_, 1, v___f_5256_);
return v___f_5257_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5258_, lean_object* v_inst_5259_){
_start:
{
lean_object* v___x_5260_; 
v___x_5260_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5259_);
return v___x_5260_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__0(lean_object* v_a_5261_){
_start:
{
lean_object* v___x_5262_; 
v___x_5262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5262_, 0, v_a_5261_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_5263_, lean_object* v_x_5264_){
_start:
{
if (lean_obj_tag(v_x_5264_) == 0)
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5274_; 
lean_dec_ref(v___f_5263_);
v_a_5266_ = lean_ctor_get(v_x_5264_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v_x_5264_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5268_ = v_x_5264_;
v_isShared_5269_ = v_isSharedCheck_5274_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v_x_5264_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5274_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5271_; 
if (v_isShared_5269_ == 0)
{
v___x_5271_ = v___x_5268_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5266_);
v___x_5271_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
lean_object* v___x_5272_; 
v___x_5272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5272_, 0, v___x_5271_);
return v___x_5272_;
}
}
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5276_; uint8_t v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v_a_5275_ = lean_ctor_get(v_x_5264_, 0);
lean_inc(v_a_5275_);
lean_dec_ref_known(v_x_5264_, 1);
v___x_5276_ = lean_unsigned_to_nat(0u);
v___x_5277_ = 0;
v___x_5278_ = lean_task_map(v___f_5263_, v_a_5275_, v___x_5276_, v___x_5277_);
v___x_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
return v___x_5279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_5280_, lean_object* v_x_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v_res_5283_; 
v_res_5283_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__1(v___f_5280_, v_x_5281_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5284_, lean_object* v_receiver_5285_, lean_object* v_x_5286_){
_start:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; uint8_t v___x_5292_; lean_object* v___x_5293_; 
v___x_5288_ = l_Std_Channel_send___redArg(v_receiver_5285_, v_x_5286_);
v___x_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5288_);
v___x_5290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5289_);
v___x_5291_ = lean_unsigned_to_nat(0u);
v___x_5292_ = 0;
v___x_5293_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5291_, v___x_5292_, v___x_5290_, v___f_5284_);
return v___x_5293_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5294_, lean_object* v_receiver_5295_, lean_object* v_x_5296_, lean_object* v___y_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__2(v___f_5294_, v_receiver_5295_, v_x_5296_);
return v_res_5298_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_5304_; lean_object* v___f_5305_; lean_object* v___f_5306_; 
v___x_5304_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_5305_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___f_5306_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5306_, 0, v___f_5305_);
lean_closure_set(v___f_5306_, 1, v___x_5304_);
return v___f_5306_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___f_5307_; lean_object* v___f_5308_; lean_object* v___f_5309_; lean_object* v___x_5310_; 
v___f_5307_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_5308_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3);
v___f_5309_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___x_5310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5310_, 0, v___f_5309_);
lean_ctor_set(v___x_5310_, 1, v___f_5308_);
lean_ctor_set(v___x_5310_, 2, v___f_5307_);
return v___x_5310_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5311_, lean_object* v_inst_5312_){
_start:
{
lean_object* v___x_5313_; 
v___x_5313_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5314_, lean_object* v_inst_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_5314_, v_inst_5315_);
lean_dec(v_inst_5315_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object* v_ch_5317_){
_start:
{
lean_inc_ref(v_ch_5317_);
return v_ch_5317_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object* v_ch_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l_Std_Channel_sync___redArg(v_ch_5318_);
lean_dec_ref(v_ch_5318_);
return v_res_5319_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object* v_00_u03b1_5320_, lean_object* v_ch_5321_){
_start:
{
lean_inc_ref(v_ch_5321_);
return v_ch_5321_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object* v_00_u03b1_5322_, lean_object* v_ch_5323_){
_start:
{
lean_object* v_res_5324_; 
v_res_5324_ = l_Std_Channel_sync(v_00_u03b1_5322_, v_ch_5323_);
lean_dec_ref(v_ch_5323_);
return v_res_5324_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg(lean_object* v_capacity_5325_){
_start:
{
lean_object* v___x_5327_; 
v___x_5327_ = l_Std_CloseableChannel_new___redArg(v_capacity_5325_);
return v___x_5327_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object* v_capacity_5328_, lean_object* v_a_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l_Std_Channel_Sync_new___redArg(v_capacity_5328_);
return v_res_5330_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new(lean_object* v_00_u03b1_5331_, lean_object* v_capacity_5332_){
_start:
{
lean_object* v___x_5334_; 
v___x_5334_ = l_Std_CloseableChannel_new___redArg(v_capacity_5332_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object* v_00_u03b1_5335_, lean_object* v_capacity_5336_, lean_object* v_a_5337_){
_start:
{
lean_object* v_res_5338_; 
v_res_5338_ = l_Std_Channel_Sync_new(v_00_u03b1_5335_, v_capacity_5336_);
return v_res_5338_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object* v_ch_5339_, lean_object* v_v_5340_){
_start:
{
uint8_t v___x_5342_; 
v___x_5342_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5339_, v_v_5340_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object* v_ch_5343_, lean_object* v_v_5344_, lean_object* v_a_5345_){
_start:
{
uint8_t v_res_5346_; lean_object* v_r_5347_; 
v_res_5346_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5343_, v_v_5344_);
v_r_5347_ = lean_box(v_res_5346_);
return v_r_5347_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend(lean_object* v_00_u03b1_5348_, lean_object* v_ch_5349_, lean_object* v_v_5350_){
_start:
{
uint8_t v___x_5352_; 
v___x_5352_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5349_, v_v_5350_);
return v___x_5352_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object* v_00_u03b1_5353_, lean_object* v_ch_5354_, lean_object* v_v_5355_, lean_object* v_a_5356_){
_start:
{
uint8_t v_res_5357_; lean_object* v_r_5358_; 
v_res_5357_ = l_Std_Channel_Sync_trySend(v_00_u03b1_5353_, v_ch_5354_, v_v_5355_);
v_r_5358_ = lean_box(v_res_5357_);
return v_r_5358_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg(lean_object* v_ch_5359_, lean_object* v_v_5360_){
_start:
{
lean_object* v___x_5362_; lean_object* v___x_5363_; 
v___x_5362_ = l_Std_Channel_send___redArg(v_ch_5359_, v_v_5360_);
v___x_5363_ = lean_io_wait(v___x_5362_);
return v___x_5363_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object* v_ch_5364_, lean_object* v_v_5365_, lean_object* v_a_5366_){
_start:
{
lean_object* v_res_5367_; 
v_res_5367_ = l_Std_Channel_Sync_send___redArg(v_ch_5364_, v_v_5365_);
return v_res_5367_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send(lean_object* v_00_u03b1_5368_, lean_object* v_ch_5369_, lean_object* v_v_5370_){
_start:
{
lean_object* v___x_5372_; 
v___x_5372_ = l_Std_Channel_Sync_send___redArg(v_ch_5369_, v_v_5370_);
return v___x_5372_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object* v_00_u03b1_5373_, lean_object* v_ch_5374_, lean_object* v_v_5375_, lean_object* v_a_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Std_Channel_Sync_send(v_00_u03b1_5373_, v_ch_5374_, v_v_5375_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object* v_ch_5378_){
_start:
{
lean_object* v___x_5380_; 
v___x_5380_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5378_);
return v___x_5380_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5381_, lean_object* v_a_5382_){
_start:
{
lean_object* v_res_5383_; 
v_res_5383_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5381_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv(lean_object* v_00_u03b1_5384_, lean_object* v_ch_5385_){
_start:
{
lean_object* v___x_5387_; 
v___x_5387_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5385_);
return v___x_5387_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5388_, lean_object* v_ch_5389_, lean_object* v_a_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_5388_, v_ch_5389_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg(lean_object* v_inst_5392_, lean_object* v_ch_5393_){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; 
v___x_5395_ = l_Std_Channel_recv___redArg(v_inst_5392_, v_ch_5393_);
v___x_5396_ = lean_io_wait(v___x_5395_);
return v___x_5396_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object* v_inst_5397_, lean_object* v_ch_5398_, lean_object* v_a_5399_){
_start:
{
lean_object* v_res_5400_; 
v_res_5400_ = l_Std_Channel_Sync_recv___redArg(v_inst_5397_, v_ch_5398_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv(lean_object* v_00_u03b1_5401_, lean_object* v_inst_5402_, lean_object* v_ch_5403_){
_start:
{
lean_object* v___x_5405_; 
v___x_5405_ = l_Std_Channel_Sync_recv___redArg(v_inst_5402_, v_ch_5403_);
return v___x_5405_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object* v_00_u03b1_5406_, lean_object* v_inst_5407_, lean_object* v_ch_5408_, lean_object* v_a_5409_){
_start:
{
lean_object* v_res_5410_; 
v_res_5410_ = l_Std_Channel_Sync_recv(v_00_u03b1_5406_, v_inst_5407_, v_ch_5408_);
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object* v_f_5411_, lean_object* v_b_5412_, lean_object* v_toBind_5413_, lean_object* v___f_5414_, lean_object* v_a_5415_){
_start:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5416_ = lean_apply_2(v_f_5411_, v_a_5415_, v_b_5412_);
v___x_5417_ = lean_apply_4(v_toBind_5413_, lean_box(0), lean_box(0), v___x_5416_, v___f_5414_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object* v_inst_5418_, lean_object* v_inst_5419_, lean_object* v_inst_5420_, lean_object* v_ch_5421_, lean_object* v_f_5422_, lean_object* v_b_5423_){
_start:
{
lean_object* v_toApplicative_5424_; lean_object* v_toBind_5425_; lean_object* v_toPure_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___f_5429_; lean_object* v___f_5430_; lean_object* v___x_5431_; 
v_toApplicative_5424_ = lean_ctor_get(v_inst_5419_, 0);
v_toBind_5425_ = lean_ctor_get(v_inst_5419_, 1);
lean_inc_n(v_toBind_5425_, 2);
v_toPure_5426_ = lean_ctor_get(v_toApplicative_5424_, 1);
lean_inc(v_toPure_5426_);
lean_inc_ref(v_ch_5421_);
lean_inc(v_inst_5418_);
v___x_5427_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_recv___boxed), 4, 3);
lean_closure_set(v___x_5427_, 0, lean_box(0));
lean_closure_set(v___x_5427_, 1, v_inst_5418_);
lean_closure_set(v___x_5427_, 2, v_ch_5421_);
lean_inc(v_inst_5420_);
v___x_5428_ = lean_apply_2(v_inst_5420_, lean_box(0), v___x_5427_);
lean_inc(v_f_5422_);
v___f_5429_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5429_, 0, v_toPure_5426_);
lean_closure_set(v___f_5429_, 1, v_inst_5418_);
lean_closure_set(v___f_5429_, 2, v_inst_5419_);
lean_closure_set(v___f_5429_, 3, v_inst_5420_);
lean_closure_set(v___f_5429_, 4, v_ch_5421_);
lean_closure_set(v___f_5429_, 5, v_f_5422_);
v___f_5430_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1), 5, 4);
lean_closure_set(v___f_5430_, 0, v_f_5422_);
lean_closure_set(v___f_5430_, 1, v_b_5423_);
lean_closure_set(v___f_5430_, 2, v_toBind_5425_);
lean_closure_set(v___f_5430_, 3, v___f_5429_);
v___x_5431_ = lean_apply_4(v_toBind_5425_, lean_box(0), lean_box(0), v___x_5428_, v___f_5430_);
return v___x_5431_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5432_, lean_object* v_inst_5433_, lean_object* v_inst_5434_, lean_object* v_inst_5435_, lean_object* v_ch_5436_, lean_object* v_f_5437_, lean_object* v_____do__lift_5438_){
_start:
{
if (lean_obj_tag(v_____do__lift_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v___x_5440_; 
lean_dec(v_f_5437_);
lean_dec_ref(v_ch_5436_);
lean_dec(v_inst_5435_);
lean_dec_ref(v_inst_5434_);
lean_dec(v_inst_5433_);
v_a_5439_ = lean_ctor_get(v_____do__lift_5438_, 0);
lean_inc(v_a_5439_);
lean_dec_ref_known(v_____do__lift_5438_, 1);
v___x_5440_ = lean_apply_2(v_toPure_5432_, lean_box(0), v_a_5439_);
return v___x_5440_;
}
else
{
lean_object* v_a_5441_; lean_object* v___x_5442_; 
lean_dec(v_toPure_5432_);
v_a_5441_ = lean_ctor_get(v_____do__lift_5438_, 0);
lean_inc(v_a_5441_);
lean_dec_ref_known(v_____do__lift_5438_, 1);
v___x_5442_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5433_, v_inst_5434_, v_inst_5435_, v_ch_5436_, v_f_5437_, v_a_5441_);
return v___x_5442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object* v_00_u03b1_5443_, lean_object* v_m_5444_, lean_object* v_00_u03b2_5445_, lean_object* v_inst_5446_, lean_object* v_inst_5447_, lean_object* v_inst_5448_, lean_object* v_ch_5449_, lean_object* v_f_5450_, lean_object* v_b_5451_){
_start:
{
lean_object* v___x_5452_; 
v___x_5452_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5446_, v_inst_5447_, v_inst_5448_, v_ch_5449_, v_f_5450_, v_b_5451_);
return v___x_5452_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5453_, lean_object* v_inst_5454_, lean_object* v_inst_5455_, lean_object* v_ch_5456_, lean_object* v_b_5457_, lean_object* v_f_5458_){
_start:
{
lean_object* v___x_5459_; 
v___x_5459_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5453_, v_inst_5454_, v_inst_5455_, v_ch_5456_, v_f_5458_, v_b_5457_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_00_u03b1_5460_, lean_object* v_m_5461_, lean_object* v_inst_5462_, lean_object* v_inst_5463_, lean_object* v_inst_5464_, lean_object* v_00_u03b2_5465_, lean_object* v_ch_5466_, lean_object* v_b_5467_, lean_object* v_f_5468_){
_start:
{
lean_object* v___x_5469_; 
v___x_5469_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5462_, v_inst_5463_, v_inst_5464_, v_ch_5466_, v_f_5468_, v_b_5467_);
return v___x_5469_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5470_, lean_object* v_inst_5471_, lean_object* v_inst_5472_, lean_object* v_00_u03b2_5473_, lean_object* v_ch_5474_, lean_object* v_b_5475_, lean_object* v_f_5476_){
_start:
{
lean_object* v___x_5477_; 
v___x_5477_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5470_, v_inst_5471_, v_inst_5472_, v_ch_5474_, v_f_5476_, v_b_5475_);
return v___x_5477_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5478_, lean_object* v_inst_5479_, lean_object* v_inst_5480_){
_start:
{
lean_object* v___f_5481_; 
v___f_5481_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5481_, 0, v_inst_5478_);
lean_closure_set(v___f_5481_, 1, v_inst_5479_);
lean_closure_set(v___f_5481_, 2, v_inst_5480_);
return v___f_5481_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5482_, lean_object* v_m_5483_, lean_object* v_inst_5484_, lean_object* v_inst_5485_, lean_object* v_inst_5486_){
_start:
{
lean_object* v___f_5487_; 
v___f_5487_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5487_, 0, v_inst_5484_);
lean_closure_set(v___f_5487_, 1, v_inst_5485_);
lean_closure_set(v___f_5487_, 2, v_inst_5486_);
return v___f_5487_;
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

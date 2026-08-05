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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0_value;
static const lean_ctor_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1_value;
static const lean_closure_object l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2 = (const lean_object*)&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2_value;
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
v___x_222_ = lean_st_ref_set(v_finished_215_, v___x_221_);
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
v___x_346_ = lean_st_ref_set(v___y_324_, v___x_345_);
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
v___x_354_ = lean_st_ref_set(v___y_324_, v___x_353_);
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
v___x_524_ = lean_st_ref_set(v___y_503_, v___x_523_);
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
v___x_680_ = lean_st_ref_set(v_a_662_, v___x_679_);
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
v___x_741_ = lean_st_ref_set(v___y_723_, v___x_740_);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_856_; 
v_a_848_ = lean_ctor_get(v_x_846_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_846_);
if (v_isSharedCheck_856_ == 0)
{
v___x_850_ = v_x_846_;
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v_x_846_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_855_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_891_; 
v_a_857_ = lean_ctor_get(v_x_846_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_x_846_);
if (v_isSharedCheck_891_ == 0)
{
v___x_859_ = v_x_846_;
v_isShared_860_ = v_isSharedCheck_891_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v_x_846_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_891_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_values_861_; lean_object* v_consumers_862_; uint8_t v_closed_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_890_; 
v_values_861_ = lean_ctor_get(v_a_857_, 0);
v_consumers_862_ = lean_ctor_get(v_a_857_, 1);
v_closed_863_ = lean_ctor_get_uint8(v_a_857_, sizeof(void*)*2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_a_857_);
if (v_isSharedCheck_890_ == 0)
{
v___x_865_ = v_a_857_;
v_isShared_866_ = v_isSharedCheck_890_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_consumers_862_);
lean_inc(v_values_861_);
lean_dec(v_a_857_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_890_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_Queue_dequeue_x3f___redArg(v_values_861_);
if (lean_obj_tag(v___x_867_) == 1)
{
lean_object* v_val_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_888_; 
v_val_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_888_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_888_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_val_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_888_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_fst_872_; lean_object* v_snd_873_; lean_object* v___x_875_; 
v_fst_872_ = lean_ctor_get(v_val_868_, 0);
lean_inc(v_fst_872_);
v_snd_873_ = lean_ctor_get(v_val_868_, 1);
lean_inc(v_snd_873_);
lean_dec(v_val_868_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v_snd_873_);
v___x_875_ = v___x_865_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_snd_873_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_consumers_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_887_, sizeof(void*)*2, v_closed_863_);
v___x_875_ = v_reuseFailAlloc_887_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___f_877_; lean_object* v___x_879_; 
v___x_876_ = lean_st_ref_set(v_a_845_, v___x_875_);
v___f_877_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_877_, 0, v_fst_872_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_876_);
v___x_879_ = v___x_859_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_876_);
v___x_879_ = v_reuseFailAlloc_886_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 0);
lean_ctor_set(v___x_870_, 0, v___x_879_);
v___x_881_ = v___x_870_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_885_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = 0;
v___x_884_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_882_, v___x_883_, v___x_881_, v___f_877_);
return v___x_884_;
}
}
}
}
}
else
{
lean_object* v___x_889_; 
lean_dec(v___x_867_);
lean_del_object(v___x_865_);
lean_dec_ref(v_consumers_862_);
lean_del_object(v___x_859_);
v___x_889_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_892_, lean_object* v_x_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_892_, v_x_893_);
lean_dec(v_a_892_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(lean_object* v_a_896_){
_start:
{
lean_object* v___x_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; 
v___x_898_ = lean_st_ref_get(v_a_896_);
lean_inc(v_a_896_);
v___f_899_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_899_, 0, v_a_896_);
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = 0;
v___x_904_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_902_, v___x_903_, v___x_901_, v___f_899_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_905_);
lean_dec(v_a_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_object* v_00_u03b1_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_912_, lean_object* v_a_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(v_00_u03b1_912_, v_a_913_);
lean_dec(v_a_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_promise_916_, lean_object* v_x_917_){
_start:
{
if (lean_obj_tag(v_x_917_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_927_; 
v_a_919_ = lean_ctor_get(v_x_917_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v_x_917_);
if (v_isSharedCheck_927_ == 0)
{
v___x_921_ = v_x_917_;
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v_x_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_926_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_925_; 
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_io_promise_resolve(v_x_917_, v_promise_916_);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_promise_931_, lean_object* v_x_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_931_, v_x_932_);
lean_dec(v_promise_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_935_, lean_object* v___y_936_, lean_object* v___f_937_, lean_object* v_x_938_){
_start:
{
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v___f_937_);
lean_dec_ref(v_lose_935_);
v_a_940_ = lean_ctor_get(v_x_938_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v_x_938_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v_x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
}
else
{
lean_object* v_a_949_; uint8_t v___x_950_; 
v_a_949_ = lean_ctor_get(v_x_938_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v_x_938_, 1);
v___x_950_ = lean_unbox(v_a_949_);
lean_dec(v_a_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_dec_ref(v___f_937_);
lean_inc(v___y_936_);
v___x_951_ = lean_apply_2(v_lose_935_, v___y_936_, lean_box(0));
return v___x_951_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; 
lean_dec_ref(v_lose_935_);
v___x_952_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_936_);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = 0;
v___x_955_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_953_, v___x_954_, v___x_952_, v___f_937_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_956_, lean_object* v___y_957_, lean_object* v___f_958_, lean_object* v_x_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_956_, v___y_957_, v___f_958_, v_x_959_);
lean_dec(v___y_957_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object* v_w_962_, lean_object* v_lose_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_finished_966_; lean_object* v_promise_967_; lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v___f_970_; uint8_t v___y_972_; uint8_t v___x_982_; 
v_finished_966_ = lean_ctor_get(v_w_962_, 0);
lean_inc(v_finished_966_);
v_promise_967_ = lean_ctor_get(v_w_962_, 1);
lean_inc(v_promise_967_);
lean_dec_ref(v_w_962_);
v___x_968_ = lean_st_ref_take(v_finished_966_);
v___f_969_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_969_, 0, v_promise_967_);
lean_inc(v___y_964_);
v___f_970_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_970_, 0, v_lose_963_);
lean_closure_set(v___f_970_, 1, v___y_964_);
lean_closure_set(v___f_970_, 2, v___f_969_);
v___x_982_ = lean_unbox(v___x_968_);
lean_dec(v___x_968_);
if (v___x_982_ == 0)
{
uint8_t v___x_983_; 
v___x_983_ = 1;
v___y_972_ = v___x_983_;
goto v___jp_971_;
}
else
{
uint8_t v___x_984_; 
v___x_984_ = 0;
v___y_972_ = v___x_984_;
goto v___jp_971_;
}
v___jp_971_:
{
uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; 
v___x_973_ = 1;
v___x_974_ = lean_box(v___x_973_);
v___x_975_ = lean_st_ref_set(v_finished_966_, v___x_974_);
lean_dec(v_finished_966_);
v___x_976_ = lean_box(v___y_972_);
v___x_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = 0;
v___x_981_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_979_, v___x_980_, v___x_978_, v___f_970_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object* v_w_985_, lean_object* v_lose_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_985_, v_lose_986_, v___y_987_);
lean_dec(v___y_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object* v_00_u03b1_990_, lean_object* v_w_991_, lean_object* v_lose_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_991_, v_lose_992_, v___y_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_996_, lean_object* v_w_997_, lean_object* v_lose_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(v_00_u03b1_996_, v_w_997_, v_lose_998_, v___y_999_);
lean_dec(v___y_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_1002_, lean_object* v_x_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_io_basemutex_unlock(v_mutex_1002_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(v_mutex_1008_, v_x_1009_);
lean_dec(v_x_1009_);
lean_dec(v_mutex_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_1012_, lean_object* v_ref_1013_, lean_object* v_x_1014_){
_start:
{
if (lean_obj_tag(v_x_1014_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v_ref_1013_);
lean_dec_ref(v_k_1012_);
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
lean_object* v___x_1025_; 
lean_dec_ref_known(v_x_1014_, 1);
v___x_1025_ = lean_apply_2(v_k_1012_, v_ref_1013_, lean_box(0));
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_1026_, lean_object* v_ref_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_k_1026_, v_ref_1027_, v_x_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_1031_, lean_object* v___f_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1034_ = lean_io_basemutex_lock(v_mutex_1031_);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = 0;
v___x_1039_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1037_, v___x_1038_, v___x_1036_, v___f_1032_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_1040_, lean_object* v___f_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_mutex_1040_, v___f_1041_);
lean_dec(v_mutex_1040_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_1044_){
_start:
{
if (lean_obj_tag(v___y_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___y_1044_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___y_1044_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___y_1044_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___y_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_a_1053_ = lean_ctor_get(v___y_1044_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___y_1044_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v___y_1044_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___y_1044_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_fst_1057_; lean_object* v___x_1059_; 
v_fst_1057_ = lean_ctor_get(v_a_1053_, 0);
lean_inc(v_fst_1057_);
lean_dec(v_a_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_fst_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_fst_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(lean_object* v_mutex_1063_, lean_object* v_k_1064_){
_start:
{
lean_object* v_ref_1066_; lean_object* v_mutex_1067_; lean_object* v___f_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___y_1075_; 
v_ref_1066_ = lean_ctor_get(v_mutex_1063_, 0);
lean_inc(v_ref_1066_);
v_mutex_1067_ = lean_ctor_get(v_mutex_1063_, 1);
lean_inc_n(v_mutex_1067_, 2);
lean_dec_ref(v_mutex_1063_);
v___f_1068_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1068_, 0, v_mutex_1067_);
v___f_1069_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1069_, 0, v_k_1064_);
lean_closure_set(v___f_1069_, 1, v_ref_1066_);
v___f_1070_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1070_, 0, v_mutex_1067_);
lean_closure_set(v___f_1070_, 1, v___f_1069_);
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = 0;
v___x_1073_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1070_, v___f_1068_, v___x_1071_, v___x_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1077_; 
v_a_1077_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1073_, 1);
if (lean_obj_tag(v_a_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v_a_1077_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_a_1077_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v_a_1077_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v_a_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
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
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
v___y_1075_ = v___x_1083_;
goto v___jp_1074_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1094_; 
v_a_1086_ = lean_ctor_get(v_a_1077_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_a_1077_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1088_ = v_a_1077_;
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v_a_1077_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_fst_1090_; lean_object* v___x_1092_; 
v_fst_1090_ = lean_ctor_get(v_a_1086_, 0);
lean_inc(v_fst_1090_);
lean_dec(v_a_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v_fst_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_fst_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
v___y_1075_ = v___x_1092_;
goto v___jp_1074_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1104_; 
v_a_1095_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1097_ = v___x_1073_;
v_isShared_1098_ = v_isSharedCheck_1104_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1073_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1104_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___f_1099_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0));
v___x_1100_ = lean_task_map(v___f_1099_, v_a_1095_, v___x_1071_, v___x_1072_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1100_);
v___x_1102_ = v___x_1097_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
v___jp_1074_:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___y_1075_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_1105_, lean_object* v_k_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1105_, v_k_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_mutex_1111_, lean_object* v_k_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1111_, v_k_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_1115_, lean_object* v_00_u03b2_1116_, lean_object* v_mutex_1117_, lean_object* v_k_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(v_00_u03b1_1115_, v_00_u03b2_1116_, v_mutex_1117_, v_k_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(lean_object* v_x_1121_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1131_; 
v_a_1123_ = lean_ctor_get(v_x_1121_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1125_ = v_x_1121_;
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v_x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1141_; 
v_a_1132_ = lean_ctor_get(v_x_1121_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1134_ = v_x_1121_;
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v_x_1121_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_a_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(lean_object* v_x_1145_){
_start:
{
uint8_t v___y_1148_; 
if (lean_obj_tag(v_x_1145_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v_a_1152_ = lean_ctor_get(v_x_1145_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_x_1145_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1154_ = v_x_1145_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v_x_1145_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v_values_1162_; uint8_t v_closed_1163_; uint8_t v___x_1164_; 
v_a_1161_ = lean_ctor_get(v_x_1145_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v_x_1145_, 1);
v_values_1162_ = lean_ctor_get(v_a_1161_, 0);
lean_inc_ref(v_values_1162_);
v_closed_1163_ = lean_ctor_get_uint8(v_a_1161_, sizeof(void*)*2);
lean_dec(v_a_1161_);
v___x_1164_ = l_Std_Queue_isEmpty___redArg(v_values_1162_);
lean_dec_ref(v_values_1162_);
if (v___x_1164_ == 0)
{
uint8_t v___x_1165_; 
v___x_1165_ = 1;
v___y_1148_ = v___x_1165_;
goto v___jp_1147_;
}
else
{
v___y_1148_ = v_closed_1163_;
goto v___jp_1147_;
}
}
v___jp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(v___y_1148_);
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(lean_object* v_x_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(lean_object* v___x_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1169_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_1174_, v___y_1175_);
lean_dec(v___y_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(lean_object* v___y_1184_, lean_object* v_waiter_1185_, lean_object* v_x_1186_){
_start:
{
if (lean_obj_tag(v_x_1186_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_waiter_1185_);
v_a_1188_ = lean_ctor_get(v_x_1186_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1190_ = v_x_1186_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v_x_1186_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
}
else
{
lean_object* v_a_1197_; uint8_t v___x_1198_; 
v_a_1197_ = lean_ctor_get(v_x_1186_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v_x_1186_, 1);
v___x_1198_ = lean_unbox(v_a_1197_);
lean_dec(v_a_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v_values_1200_; lean_object* v_consumers_1201_; uint8_t v_closed_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1213_; 
v___x_1199_ = lean_st_ref_take(v___y_1184_);
v_values_1200_ = lean_ctor_get(v___x_1199_, 0);
v_consumers_1201_ = lean_ctor_get(v___x_1199_, 1);
v_closed_1202_ = lean_ctor_get_uint8(v___x_1199_, sizeof(void*)*2);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1204_ = v___x_1199_;
v_isShared_1205_ = v_isSharedCheck_1213_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_consumers_1201_);
lean_inc(v_values_1200_);
lean_dec(v___x_1199_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1213_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_waiter_1185_);
v___x_1207_ = l_Std_Queue_enqueue___redArg(v___x_1206_, v_consumers_1201_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1207_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_values_1200_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*2, v_closed_1202_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_st_ref_set(v___y_1184_, v___x_1209_);
v___x_1211_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_1211_;
}
}
}
else
{
lean_object* v_lose_1214_; lean_object* v___x_1215_; 
v_lose_1214_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2));
v___x_1215_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_waiter_1185_, v_lose_1214_, v___y_1184_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(lean_object* v___y_1216_, lean_object* v_waiter_1217_, lean_object* v_x_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_1216_, v_waiter_1217_, v_x_1218_);
lean_dec(v___y_1216_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(lean_object* v___f_1221_, lean_object* v_waiter_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; 
v___x_1225_ = lean_st_ref_get(v___y_1223_);
v___x_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = 0;
v___x_1230_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1228_, v___x_1229_, v___x_1227_, v___f_1221_);
lean_inc(v___y_1223_);
v___f_1231_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1231_, 0, v___y_1223_);
lean_closure_set(v___f_1231_, 1, v_waiter_1222_);
v___x_1232_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1228_, v___x_1229_, v___x_1230_, v___f_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(lean_object* v___f_1233_, lean_object* v_waiter_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v___f_1233_, v_waiter_1234_, v___y_1235_);
lean_dec(v___y_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(lean_object* v___f_1238_, lean_object* v_ch_1239_, lean_object* v_waiter_1240_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; 
v___f_1242_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1242_, 0, v___f_1238_);
lean_closure_set(v___f_1242_, 1, v_waiter_1240_);
v___x_1243_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_1239_, v___f_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(lean_object* v___f_1244_, lean_object* v_ch_1245_, lean_object* v_waiter_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_1244_, v_ch_1245_, v_waiter_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(lean_object* v___y_1253_, lean_object* v___f_1254_, lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1255_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v___f_1254_);
v_a_1257_ = lean_ctor_get(v_x_1255_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1255_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1259_ = v_x_1255_;
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v_x_1255_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
}
else
{
lean_object* v_a_1266_; uint8_t v___x_1267_; 
v_a_1266_ = lean_ctor_get(v_x_1255_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v_x_1255_, 1);
v___x_1267_ = lean_unbox(v_a_1266_);
lean_dec(v_a_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec_ref(v___f_1254_);
v___x_1268_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1269_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_1253_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = 0;
v___x_1272_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1270_, v___x_1271_, v___x_1269_, v___f_1254_);
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(lean_object* v___y_1273_, lean_object* v___f_1274_, lean_object* v_x_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_1273_, v___f_1274_, v_x_1275_);
lean_dec(v___y_1273_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(lean_object* v___f_1278_, lean_object* v___f_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___f_1288_; lean_object* v___x_1289_; 
v___x_1282_ = lean_st_ref_get(v___y_1280_);
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = 0;
v___x_1287_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1285_, v___x_1286_, v___x_1284_, v___f_1278_);
lean_inc(v___y_1280_);
v___f_1288_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1288_, 0, v___y_1280_);
lean_closure_set(v___f_1288_, 1, v___f_1279_);
v___x_1289_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1285_, v___x_1286_, v___x_1287_, v___f_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(lean_object* v___f_1290_, lean_object* v___f_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_1290_, v___f_1291_, v___y_1292_);
lean_dec(v___y_1292_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(lean_object* v_values_1295_, uint8_t v_closed_1296_, lean_object* v___y_1297_, lean_object* v_x_1298_){
_start:
{
if (lean_obj_tag(v_x_1298_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref(v_values_1295_);
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
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1319_; 
v_a_1309_ = lean_ctor_get(v_x_1298_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_x_1298_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1311_ = v_x_1298_;
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v_x_1298_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1313_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1313_, 0, v_values_1295_);
lean_ctor_set(v___x_1313_, 1, v_a_1309_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*2, v_closed_1296_);
v___x_1314_ = lean_st_ref_set(v___y_1297_, v___x_1313_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1314_);
v___x_1316_ = v___x_1311_;
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed(lean_object* v_values_1320_, lean_object* v_closed_1321_, lean_object* v___y_1322_, lean_object* v_x_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v_closed_boxed_1325_; lean_object* v_res_1326_; 
v_closed_boxed_1325_ = lean_unbox(v_closed_1321_);
v_res_1326_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(v_values_1320_, v_closed_boxed_1325_, v___y_1322_, v_x_1323_);
lean_dec(v___y_1322_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_1327_){
_start:
{
if (lean_obj_tag(v_x_1327_) == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_x_1327_);
return v___x_1329_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1339_; 
v_a_1330_ = lean_ctor_get(v_x_1327_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_x_1327_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1332_ = v_x_1327_;
v_isShared_1333_ = v_isSharedCheck_1339_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v_x_1327_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1339_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = l_List_reverse___redArg(v_a_1330_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(v_x_1340_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_1343_, lean_object* v___x_1344_, lean_object* v_x_1345_){
_start:
{
if (lean_obj_tag(v_x_1345_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v___x_1344_);
lean_dec(v_a_1343_);
v_a_1347_ = lean_ctor_get(v_x_1345_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_x_1345_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1349_ = v_x_1345_;
v_isShared_1350_ = v_isSharedCheck_1355_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v_x_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1355_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1372_; 
v_a_1356_ = lean_ctor_get(v_x_1345_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_x_1345_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1358_ = v_x_1345_;
v_isShared_1359_ = v_isSharedCheck_1372_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v_x_1345_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1372_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
uint8_t v___x_1360_; 
v___x_1360_ = l_List_isEmpty___redArg(v_a_1343_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_dec(v___x_1344_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_a_1356_);
lean_ctor_set(v___x_1361_, 1, v_a_1343_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1361_);
v___x_1363_ = v___x_1358_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_dec(v_a_1343_);
v___x_1366_ = l_List_reverse___redArg(v_a_1356_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1344_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1367_);
v___x_1369_ = v___x_1358_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_1373_, lean_object* v___x_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(v_a_1373_, v___x_1374_, v_x_1375_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(lean_object* v_x_1378_){
_start:
{
uint8_t v___y_1381_; 
if (lean_obj_tag(v_x_1378_) == 0)
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v_x_1378_);
return v___x_1385_;
}
else
{
lean_object* v_a_1386_; uint8_t v___x_1387_; 
v_a_1386_ = lean_ctor_get(v_x_1378_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v_x_1378_, 1);
v___x_1387_ = lean_unbox(v_a_1386_);
lean_dec(v_a_1386_);
if (v___x_1387_ == 0)
{
uint8_t v___x_1388_; 
v___x_1388_ = 1;
v___y_1381_ = v___x_1388_;
goto v___jp_1380_;
}
else
{
uint8_t v___x_1389_; 
v___x_1389_ = 0;
v___y_1381_ = v___x_1389_;
goto v___jp_1380_;
}
}
v___jp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_box(v___y_1381_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(lean_object* v_x_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_tail_1393_, lean_object* v_x_1394_, lean_object* v_head_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_1393_, v_x_1394_, v_head_1395_, v_x_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
if (lean_obj_tag(v_x_1405_) == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_x_1406_);
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
return v___x_1409_;
}
else
{
lean_object* v_head_1410_; lean_object* v_tail_1411_; lean_object* v___f_1412_; lean_object* v_val_1414_; 
v_head_1410_ = lean_ctor_get(v_x_1405_, 0);
lean_inc_n(v_head_1410_, 2);
v_tail_1411_ = lean_ctor_get(v_x_1405_, 1);
lean_inc(v_tail_1411_);
lean_dec_ref_known(v_x_1405_, 2);
v___f_1412_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1412_, 0, v_tail_1411_);
lean_closure_set(v___f_1412_, 1, v_x_1406_);
lean_closure_set(v___f_1412_, 2, v_head_1410_);
if (lean_obj_tag(v_head_1410_) == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref_known(v_head_1410_, 1);
v___x_1418_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_1414_ = v___x_1418_;
goto v___jp_1413_;
}
else
{
lean_object* v_finished_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1433_; 
v_finished_1419_ = lean_ctor_get(v_head_1410_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_head_1410_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1421_ = v_head_1410_;
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_finished_1419_);
lean_dec(v_head_1410_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v_finished_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___x_1427_; 
v_finished_1423_ = lean_ctor_get(v_finished_1419_, 0);
lean_inc(v_finished_1423_);
lean_dec_ref(v_finished_1419_);
v___x_1424_ = lean_st_ref_get(v_finished_1423_);
lean_dec(v_finished_1423_);
v___f_1425_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1424_);
v___x_1427_ = v___x_1421_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1424_);
v___x_1427_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; 
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = 0;
v___x_1431_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1429_, v___x_1430_, v___x_1428_, v___f_1425_);
v_val_1414_ = v___x_1431_;
goto v___jp_1413_;
}
}
}
v___jp_1413_:
{
lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = 0;
v___x_1417_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1415_, v___x_1416_, v_val_1414_, v___f_1412_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object* v_tail_1434_, lean_object* v_x_1435_, lean_object* v_head_1436_, lean_object* v_x_1437_){
_start:
{
if (lean_obj_tag(v_x_1437_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v_head_1436_);
lean_dec(v_x_1435_);
lean_dec(v_tail_1434_);
v_a_1439_ = lean_ctor_get(v_x_1437_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1437_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1441_ = v_x_1437_;
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v_x_1437_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
}
else
{
lean_object* v_a_1448_; uint8_t v___x_1449_; 
v_a_1448_ = lean_ctor_get(v_x_1437_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v_x_1437_, 1);
v___x_1449_ = lean_unbox(v_a_1448_);
lean_dec(v_a_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec_ref(v_head_1436_);
v___x_1450_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1434_, v_x_1435_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_head_1436_);
lean_ctor_set(v___x_1451_, 1, v_x_1435_);
v___x_1452_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1434_, v___x_1451_);
return v___x_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1453_, v_x_1454_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_1457_, lean_object* v___x_1458_, lean_object* v___f_1459_, lean_object* v_x_1460_){
_start:
{
if (lean_obj_tag(v_x_1460_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v___f_1459_);
lean_dec(v___x_1458_);
lean_dec(v_eList_1457_);
v_a_1462_ = lean_ctor_get(v_x_1460_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_x_1460_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1464_ = v_x_1460_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v_x_1460_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; 
v_a_1471_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v_x_1460_, 1);
lean_inc(v___x_1458_);
v___x_1472_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_1457_, v___x_1458_);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = 0;
v___x_1475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1473_, v___x_1474_, v___x_1472_, v___f_1459_);
v___f_1476_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1476_, 0, v_a_1471_);
lean_closure_set(v___f_1476_, 1, v___x_1458_);
v___x_1477_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1473_, v___x_1474_, v___x_1475_, v___f_1476_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_1478_, lean_object* v___x_1479_, lean_object* v___f_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v_eList_1478_, v___x_1479_, v___f_1480_, v_x_1481_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object* v_q_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_eList_1488_; lean_object* v_dList_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; 
v_eList_1488_ = lean_ctor_get(v_q_1485_, 0);
lean_inc(v_eList_1488_);
v_dList_1489_ = lean_ctor_get(v_q_1485_, 1);
lean_inc(v_dList_1489_);
lean_dec_ref(v_q_1485_);
v___x_1490_ = lean_box(0);
v___x_1491_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_1489_, v___x_1490_);
v___f_1492_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = 0;
v___x_1495_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1493_, v___x_1494_, v___x_1491_, v___f_1492_);
v___f_1496_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1496_, 0, v_eList_1488_);
lean_closure_set(v___f_1496_, 1, v___x_1490_);
lean_closure_set(v___f_1496_, 2, v___f_1492_);
v___x_1497_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1493_, v___x_1494_, v___x_1495_, v___f_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object* v_q_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1498_, v___y_1499_);
lean_dec(v___y_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object* v___y_1502_, lean_object* v_x_1503_){
_start:
{
if (lean_obj_tag(v_x_1503_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1513_; 
v_a_1505_ = lean_ctor_get(v_x_1503_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_x_1503_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1507_ = v_x_1503_;
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v_x_1503_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v_values_1515_; lean_object* v_consumers_1516_; uint8_t v_closed_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___f_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; 
v_a_1514_ = lean_ctor_get(v_x_1503_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v_x_1503_, 1);
v_values_1515_ = lean_ctor_get(v_a_1514_, 0);
lean_inc_ref(v_values_1515_);
v_consumers_1516_ = lean_ctor_get(v_a_1514_, 1);
lean_inc_ref(v_consumers_1516_);
v_closed_1517_ = lean_ctor_get_uint8(v_a_1514_, sizeof(void*)*2);
lean_dec(v_a_1514_);
v___x_1518_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_1516_, v___y_1502_);
v___x_1519_ = lean_box(v_closed_1517_);
lean_inc(v___y_1502_);
v___f_1520_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1520_, 0, v_values_1515_);
lean_closure_set(v___f_1520_, 1, v___x_1519_);
lean_closure_set(v___f_1520_, 2, v___y_1502_);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = 0;
v___x_1523_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1521_, v___x_1522_, v___x_1518_, v___f_1520_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object* v___y_1524_, lean_object* v_x_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1524_, v_x_1525_);
lean_dec(v___y_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; 
v___x_1530_ = lean_st_ref_get(v___y_1528_);
lean_inc(v___y_1528_);
v___f_1531_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1531_, 0, v___y_1528_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = 0;
v___x_1536_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1534_, v___x_1535_, v___x_1533_, v___f_1531_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1537_);
lean_dec(v___y_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object* v_ch_1546_){
_start:
{
lean_object* v___f_1547_; lean_object* v___f_1548_; lean_object* v___f_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___f_1547_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1));
lean_inc_ref_n(v_ch_1546_, 2);
v___f_1548_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1548_, 0, v___f_1547_);
lean_closure_set(v___f_1548_, 1, v_ch_1546_);
v___f_1549_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2));
v___f_1550_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3));
v___x_1551_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1551_, 0, lean_box(0));
lean_closure_set(v___x_1551_, 1, lean_box(0));
lean_closure_set(v___x_1551_, 2, v_ch_1546_);
lean_closure_set(v___x_1551_, 3, v___f_1549_);
v___x_1552_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1552_, 0, lean_box(0));
lean_closure_set(v___x_1552_, 1, lean_box(0));
lean_closure_set(v___x_1552_, 2, v_ch_1546_);
lean_closure_set(v___x_1552_, 3, v___f_1550_);
v___x_1553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___f_1548_);
lean_ctor_set(v___x_1553_, 2, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object* v_00_u03b1_1554_, lean_object* v_ch_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object* v_00_u03b1_1557_, lean_object* v_q_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1558_, v___y_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_1562_, lean_object* v_q_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_1562_, v_q_1563_, v___y_1564_);
lean_dec(v___y_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object* v_00_u03b1_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1568_, v_x_1569_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_1573_, v_x_1574_, v_x_1575_, v___y_1576_);
lean_dec(v___y_1576_);
return v_res_1578_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Std_Queue_empty(lean_box(0));
return v___x_1579_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = 0;
v___x_1581_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0);
v___x_1582_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
lean_ctor_set_uint8(v___x_1582_, sizeof(void*)*2, v___x_1580_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg(){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1);
v___x_1585_ = l_Std_Mutex_new___redArg(v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object* v_00_u03b1_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object* v_00_u03b1_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object* v_v_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v_producers_1607_; lean_object* v_consumers_1608_; uint8_t v_closed_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1632_; 
v___x_1606_ = lean_st_ref_get(v___y_1604_);
v_producers_1607_ = lean_ctor_get(v___x_1606_, 0);
v_consumers_1608_ = lean_ctor_get(v___x_1606_, 1);
v_closed_1609_ = lean_ctor_get_uint8(v___x_1606_, sizeof(void*)*2);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1611_ = v___x_1606_;
v_isShared_1612_ = v_isSharedCheck_1632_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_consumers_1608_);
lean_inc(v_producers_1607_);
lean_dec(v___x_1606_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1632_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_1608_);
if (lean_obj_tag(v___x_1613_) == 1)
{
lean_object* v_val_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1630_; 
v_val_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1630_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_val_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1630_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1621_; 
v_fst_1618_ = lean_ctor_get(v_val_1614_, 0);
lean_inc(v_fst_1618_);
v_snd_1619_ = lean_ctor_get(v_val_1614_, 1);
lean_inc(v_snd_1619_);
lean_dec(v_val_1614_);
lean_inc(v_v_1603_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v_v_1603_);
v___x_1621_ = v___x_1616_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_v_1603_);
v___x_1621_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
uint8_t v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_1618_, v___x_1621_);
lean_dec(v_fst_1618_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 1, v_snd_1619_);
v___x_1624_ = v___x_1611_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_producers_1607_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_snd_1619_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*2, v_closed_1609_);
v___x_1624_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_st_ref_set(v___y_1604_, v___x_1624_);
if (v___x_1622_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_1627_; 
lean_dec(v_v_1603_);
v___x_1627_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0));
return v___x_1627_;
}
}
}
}
}
else
{
lean_object* v___x_1631_; 
lean_dec(v___x_1613_);
lean_del_object(v___x_1611_);
lean_dec_ref(v_producers_1607_);
lean_dec(v_v_1603_);
v___x_1631_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2));
return v___x_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object* v_v_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1633_, v___y_1634_);
lean_dec(v___y_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object* v_v_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v_fst_1641_; 
v___x_1640_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1637_, v_a_1638_);
v_fst_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_fst_1641_);
lean_dec_ref(v___x_1640_);
if (lean_obj_tag(v_fst_1641_) == 0)
{
uint8_t v___x_1642_; 
v___x_1642_ = 1;
return v___x_1642_;
}
else
{
lean_object* v_val_1643_; uint8_t v___x_1644_; 
v_val_1643_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_val_1643_);
lean_dec_ref_known(v_fst_1641_, 1);
v___x_1644_ = lean_unbox(v_val_1643_);
lean_dec(v_val_1643_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object* v_v_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1645_, v_a_1646_);
lean_dec(v_a_1646_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object* v_00_u03b1_1650_, lean_object* v_v_1651_, lean_object* v_a_1652_){
_start:
{
uint8_t v___x_1654_; 
v___x_1654_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1651_, v_a_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object* v_00_u03b1_1655_, lean_object* v_v_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_res_1659_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(v_00_u03b1_1655_, v_v_1656_, v_a_1657_);
lean_dec(v_a_1657_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object* v_00_u03b1_1661_, lean_object* v_v_1662_, lean_object* v_inst_1663_, lean_object* v_a_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1662_, v___y_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1668_, lean_object* v_v_1669_, lean_object* v_inst_1670_, lean_object* v_a_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_1668_, v_v_1669_, v_inst_1670_, v_a_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v_a_1671_);
return v_res_1674_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object* v_v_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; uint8_t v_closed_1679_; 
v___x_1678_ = lean_st_ref_get(v___y_1676_);
v_closed_1679_ = lean_ctor_get_uint8(v___x_1678_, sizeof(void*)*2);
lean_dec(v___x_1678_);
if (v_closed_1679_ == 0)
{
uint8_t v___x_1680_; 
v___x_1680_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1675_, v___y_1676_);
return v___x_1680_;
}
else
{
uint8_t v___x_1681_; 
lean_dec(v_v_1675_);
v___x_1681_ = 0;
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object* v_v_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_res_1685_; lean_object* v_r_1686_; 
v_res_1685_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1682_, v___y_1683_);
lean_dec(v___y_1683_);
v_r_1686_ = lean_box(v_res_1685_);
return v_r_1686_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object* v_ch_1687_, lean_object* v_v_1688_){
_start:
{
lean_object* v___f_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___f_1690_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1690_, 0, v_v_1688_);
v___x_1691_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1687_, v___f_1690_);
v___x_1692_ = lean_unbox(v___x_1691_);
lean_dec(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object* v_ch_1693_, lean_object* v_v_1694_, lean_object* v_a_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1693_, v_v_1694_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object* v_00_u03b1_1698_, lean_object* v_ch_1699_, lean_object* v_v_1700_){
_start:
{
uint8_t v___x_1702_; 
v___x_1702_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1699_, v_v_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_ch_1704_, lean_object* v_v_1705_, lean_object* v_a_1706_){
_start:
{
uint8_t v_res_1707_; lean_object* v_r_1708_; 
v_res_1707_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(v_00_u03b1_1703_, v_ch_1704_, v_v_1705_);
v_r_1708_ = lean_box(v_res_1707_);
return v_r_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object* v_x_1709_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
goto v___jp_1710_;
}
else
{
lean_object* v_val_1712_; uint8_t v___x_1713_; 
v_val_1712_ = lean_ctor_get(v_x_1709_, 0);
v___x_1713_ = lean_unbox(v_val_1712_);
if (v___x_1713_ == 0)
{
goto v___jp_1710_;
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
return v___x_1714_;
}
}
v___jp_1710_:
{
lean_object* v___x_1711_; 
v___x_1711_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object* v_x_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_1715_);
lean_dec(v_x_1715_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object* v_v_1717_, lean_object* v___f_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; uint8_t v_closed_1722_; 
v___x_1721_ = lean_st_ref_get(v___y_1719_);
v_closed_1722_ = lean_ctor_get_uint8(v___x_1721_, sizeof(void*)*2);
lean_dec(v___x_1721_);
if (v_closed_1722_ == 0)
{
uint8_t v___x_1723_; 
lean_inc(v_v_1717_);
v___x_1723_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1717_, v___y_1719_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_producers_1726_; lean_object* v_consumers_1727_; uint8_t v_closed_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1742_; 
v___x_1724_ = lean_io_promise_new();
v___x_1725_ = lean_st_ref_take(v___y_1719_);
v_producers_1726_ = lean_ctor_get(v___x_1725_, 0);
v_consumers_1727_ = lean_ctor_get(v___x_1725_, 1);
v_closed_1728_ = lean_ctor_get_uint8(v___x_1725_, sizeof(void*)*2);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1730_ = v___x_1725_;
v_isShared_1731_ = v_isSharedCheck_1742_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_consumers_1727_);
lean_inc(v_producers_1726_);
lean_dec(v___x_1725_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1742_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
lean_inc(v___x_1724_);
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_v_1717_);
lean_ctor_set(v___x_1732_, 1, v___x_1724_);
v___x_1733_ = l_Std_Queue_enqueue___redArg(v___x_1732_, v_producers_1726_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1733_);
v___x_1735_ = v___x_1730_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_consumers_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, sizeof(void*)*2, v_closed_1728_);
v___x_1735_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1736_ = lean_st_ref_set(v___y_1719_, v___x_1735_);
v___x_1737_ = 1;
v___x_1738_ = lean_io_promise_result_opt(v___x_1724_);
lean_dec(v___x_1724_);
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = lean_task_map(v___f_1718_, v___x_1738_, v___x_1739_, v___x_1737_);
return v___x_1740_;
}
}
}
else
{
lean_object* v___x_1743_; 
lean_dec_ref(v___f_1718_);
lean_dec(v_v_1717_);
v___x_1743_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_1743_;
}
}
else
{
lean_object* v___x_1744_; 
lean_dec_ref(v___f_1718_);
lean_dec(v_v_1717_);
v___x_1744_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object* v_v_1745_, lean_object* v___f_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1745_, v___f_1746_, v___y_1747_);
lean_dec(v___y_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object* v_ch_1751_, lean_object* v_v_1752_){
_start:
{
lean_object* v___f_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; 
v___f_1754_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0));
v___f_1755_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1755_, 0, v_v_1752_);
lean_closure_set(v___f_1755_, 1, v___f_1754_);
v___x_1756_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1751_, v___f_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object* v_ch_1757_, lean_object* v_v_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1757_, v_v_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object* v_00_u03b1_1761_, lean_object* v_ch_1762_, lean_object* v_v_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1762_, v_v_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_ch_1767_, lean_object* v_v_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(v_00_u03b1_1766_, v_ch_1767_, v_v_1768_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object* v_as_1771_, size_t v_sz_1772_, size_t v_i_1773_, lean_object* v_b_1774_){
_start:
{
uint8_t v___x_1776_; 
v___x_1776_ = lean_usize_dec_lt(v_i_1773_, v_sz_1772_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_b_1774_);
return v___x_1777_;
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; size_t v___x_1782_; size_t v___x_1783_; 
v_a_1778_ = lean_array_uget_borrowed(v_as_1771_, v_i_1773_);
v___x_1779_ = lean_box(0);
v___x_1780_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_1778_, v___x_1779_);
v___x_1781_ = lean_box(0);
v___x_1782_ = ((size_t)1ULL);
v___x_1783_ = lean_usize_add(v_i_1773_, v___x_1782_);
v_i_1773_ = v___x_1783_;
v_b_1774_ = v___x_1781_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object* v_as_1785_, lean_object* v_sz_1786_, lean_object* v_i_1787_, lean_object* v_b_1788_, lean_object* v___y_1789_){
_start:
{
size_t v_sz_boxed_1790_; size_t v_i_boxed_1791_; lean_object* v_res_1792_; 
v_sz_boxed_1790_ = lean_unbox_usize(v_sz_1786_);
lean_dec(v_sz_1786_);
v_i_boxed_1791_ = lean_unbox_usize(v_i_1787_);
lean_dec(v_i_1787_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1785_, v_sz_boxed_1790_, v_i_boxed_1791_, v_b_1788_);
lean_dec_ref(v_as_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; uint8_t v_closed_1796_; 
v___x_1795_ = lean_st_ref_get(v___y_1793_);
v_closed_1796_ = lean_ctor_get_uint8(v___x_1795_, sizeof(void*)*2);
if (v_closed_1796_ == 0)
{
lean_object* v_producers_1797_; lean_object* v_consumers_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1821_; 
v_producers_1797_ = lean_ctor_get(v___x_1795_, 0);
v_consumers_1798_ = lean_ctor_get(v___x_1795_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1800_ = v___x_1795_;
v_isShared_1801_ = v_isSharedCheck_1821_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_consumers_1798_);
lean_inc(v_producers_1797_);
lean_dec(v___x_1795_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1821_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; size_t v_sz_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1802_ = l_Std_Queue_toArray___redArg(v_consumers_1798_);
v___x_1803_ = lean_box(0);
v_sz_1804_ = lean_array_size(v___x_1802_);
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_1802_, v_sz_1804_, v___x_1805_, v___x_1803_);
lean_dec_ref(v___x_1802_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1819_; 
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v___x_1806_, 0);
lean_dec(v_unused_1820_);
v___x_1808_ = v___x_1806_;
v_isShared_1809_ = v_isSharedCheck_1819_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v___x_1806_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1819_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1813_; 
v___x_1810_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
v___x_1811_ = 1;
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 1, v___x_1810_);
v___x_1813_ = v___x_1800_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_producers_1797_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1810_);
v___x_1813_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
lean_ctor_set_uint8(v___x_1813_, sizeof(void*)*2, v___x_1811_);
v___x_1814_ = lean_st_ref_set(v___y_1793_, v___x_1813_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1803_);
v___x_1816_ = v___x_1808_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1803_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_del_object(v___x_1800_);
lean_dec_ref(v_producers_1797_);
return v___x_1806_;
}
}
}
else
{
uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec(v___x_1795_);
v___x_1822_ = 1;
v___x_1823_ = lean_box(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1825_);
lean_dec(v___y_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object* v_ch_1829_){
_start:
{
lean_object* v___f_1831_; lean_object* v___x_1832_; 
v___f_1831_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0));
v___x_1832_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_1829_, v___f_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object* v_ch_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object* v_00_u03b1_1836_, lean_object* v_ch_1837_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object* v_00_u03b1_1840_, lean_object* v_ch_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(v_00_u03b1_1840_, v_ch_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object* v_00_u03b1_1844_, lean_object* v_as_1845_, size_t v_sz_1846_, size_t v_i_1847_, lean_object* v_b_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1845_, v_sz_1846_, v_i_1847_, v_b_1848_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_as_1853_, lean_object* v_sz_1854_, lean_object* v_i_1855_, lean_object* v_b_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
size_t v_sz_boxed_1859_; size_t v_i_boxed_1860_; lean_object* v_res_1861_; 
v_sz_boxed_1859_ = lean_unbox_usize(v_sz_1854_);
lean_dec(v_sz_1854_);
v_i_boxed_1860_ = lean_unbox_usize(v_i_1855_);
lean_dec(v_i_1855_);
v_res_1861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_1852_, v_as_1853_, v_sz_boxed_1859_, v_i_boxed_1860_, v_b_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v_as_1853_);
return v_res_1861_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; uint8_t v_closed_1865_; 
v___x_1864_ = lean_st_ref_get(v___y_1862_);
v_closed_1865_ = lean_ctor_get_uint8(v___x_1864_, sizeof(void*)*2);
lean_dec(v___x_1864_);
return v_closed_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v_res_1868_; lean_object* v_r_1869_; 
v_res_1868_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1866_);
lean_dec(v___y_1866_);
v_r_1869_ = lean_box(v_res_1868_);
return v_r_1869_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object* v_ch_1871_){
_start:
{
lean_object* v___f_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v___f_1873_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0));
v___x_1874_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1871_, v___f_1873_);
v___x_1875_ = lean_unbox(v___x_1874_);
lean_dec(v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object* v_ch_1876_, lean_object* v_a_1877_){
_start:
{
uint8_t v_res_1878_; lean_object* v_r_1879_; 
v_res_1878_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1876_);
v_r_1879_ = lean_box(v_res_1878_);
return v_r_1879_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object* v_00_u03b1_1880_, lean_object* v_ch_1881_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object* v_00_u03b1_1884_, lean_object* v_ch_1885_, lean_object* v_a_1886_){
_start:
{
uint8_t v_res_1887_; lean_object* v_r_1888_; 
v_res_1887_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(v_00_u03b1_1884_, v_ch_1885_);
v_r_1888_ = lean_box(v_res_1887_);
return v_r_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object* v_snd_1889_, lean_object* v_inst_1890_, lean_object* v_toBind_1891_, lean_object* v___f_1892_, lean_object* v_a_1893_){
_start:
{
uint8_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1894_ = 1;
v___x_1895_ = lean_box(v___x_1894_);
v___x_1896_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1896_, 0, lean_box(0));
lean_closure_set(v___x_1896_, 1, v___x_1895_);
lean_closure_set(v___x_1896_, 2, v_snd_1889_);
v___x_1897_ = lean_apply_2(v_inst_1890_, lean_box(0), v___x_1896_);
v___x_1898_ = lean_apply_4(v_toBind_1891_, lean_box(0), lean_box(0), v___x_1897_, v___f_1892_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_1899_, lean_object* v_inst_1900_, lean_object* v_toBind_1901_, lean_object* v_a_1902_, lean_object* v_inst_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_producers_1905_; lean_object* v_consumers_1906_; uint8_t v_closed_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1928_; 
v_producers_1905_ = lean_ctor_get(v_a_1904_, 0);
v_consumers_1906_ = lean_ctor_get(v_a_1904_, 1);
v_closed_1907_ = lean_ctor_get_uint8(v_a_1904_, sizeof(void*)*2);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_a_1904_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1909_ = v_a_1904_;
v_isShared_1910_ = v_isSharedCheck_1928_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_consumers_1906_);
lean_inc(v_producers_1905_);
lean_dec(v_a_1904_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1928_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1905_);
if (lean_obj_tag(v___x_1911_) == 1)
{
lean_object* v_val_1912_; lean_object* v_fst_1913_; lean_object* v_snd_1914_; lean_object* v_fst_1915_; lean_object* v_snd_1916_; lean_object* v___f_1917_; lean_object* v___f_1918_; lean_object* v___x_1920_; 
v_val_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_val_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v_fst_1913_ = lean_ctor_get(v_val_1912_, 0);
lean_inc(v_fst_1913_);
v_snd_1914_ = lean_ctor_get(v_val_1912_, 1);
lean_inc(v_snd_1914_);
lean_dec(v_val_1912_);
v_fst_1915_ = lean_ctor_get(v_fst_1913_, 0);
lean_inc(v_fst_1915_);
v_snd_1916_ = lean_ctor_get(v_fst_1913_, 1);
lean_inc(v_snd_1916_);
lean_dec(v_fst_1913_);
v___f_1917_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1917_, 0, v_toApplicative_1899_);
lean_closure_set(v___f_1917_, 1, v_fst_1915_);
lean_inc(v_toBind_1901_);
v___f_1918_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1918_, 0, v_snd_1916_);
lean_closure_set(v___f_1918_, 1, v_inst_1900_);
lean_closure_set(v___f_1918_, 2, v_toBind_1901_);
lean_closure_set(v___f_1918_, 3, v___f_1917_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v_snd_1914_);
v___x_1920_ = v___x_1909_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_snd_1914_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_consumers_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*2, v_closed_1907_);
v___x_1920_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_inc(v_a_1902_);
v___x_1921_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1921_, 0, lean_box(0));
lean_closure_set(v___x_1921_, 1, lean_box(0));
lean_closure_set(v___x_1921_, 2, v_a_1902_);
lean_closure_set(v___x_1921_, 3, v___x_1920_);
v___x_1922_ = lean_apply_2(v_inst_1903_, lean_box(0), v___x_1921_);
v___x_1923_ = lean_apply_4(v_toBind_1901_, lean_box(0), lean_box(0), v___x_1922_, v___f_1918_);
return v___x_1923_;
}
}
else
{
lean_object* v_toPure_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec(v___x_1911_);
lean_del_object(v___x_1909_);
lean_dec_ref(v_consumers_1906_);
lean_dec(v_inst_1903_);
lean_dec(v_toBind_1901_);
lean_dec(v_inst_1900_);
v_toPure_1925_ = lean_ctor_get(v_toApplicative_1899_, 1);
lean_inc(v_toPure_1925_);
lean_dec_ref(v_toApplicative_1899_);
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_apply_2(v_toPure_1925_, lean_box(0), v___x_1926_);
return v___x_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_1929_, lean_object* v_inst_1930_, lean_object* v_toBind_1931_, lean_object* v_a_1932_, lean_object* v_inst_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(v_toApplicative_1929_, v_inst_1930_, v_toBind_1931_, v_a_1932_, v_inst_1933_, v_a_1934_);
lean_dec(v_a_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_inst_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_toApplicative_1940_; lean_object* v_toBind_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_toApplicative_1940_ = lean_ctor_get(v_inst_1936_, 0);
lean_inc_ref(v_toApplicative_1940_);
v_toBind_1941_ = lean_ctor_get(v_inst_1936_, 1);
lean_inc_n(v_toBind_1941_, 2);
lean_dec_ref(v_inst_1936_);
lean_inc(v_inst_1937_);
lean_inc_n(v_a_1939_, 2);
v___f_1942_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1942_, 0, v_toApplicative_1940_);
lean_closure_set(v___f_1942_, 1, v_inst_1938_);
lean_closure_set(v___f_1942_, 2, v_toBind_1941_);
lean_closure_set(v___f_1942_, 3, v_a_1939_);
lean_closure_set(v___f_1942_, 4, v_inst_1937_);
v___x_1943_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1943_, 0, lean_box(0));
lean_closure_set(v___x_1943_, 1, lean_box(0));
lean_closure_set(v___x_1943_, 2, v_a_1939_);
v___x_1944_ = lean_apply_2(v_inst_1937_, lean_box(0), v___x_1943_);
v___x_1945_ = lean_apply_4(v_toBind_1941_, lean_box(0), lean_box(0), v___x_1944_, v___f_1942_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1946_, v_inst_1947_, v_inst_1948_, v_a_1949_);
lean_dec(v_a_1949_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object* v_m_1951_, lean_object* v_00_u03b1_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1953_, v_inst_1954_, v_inst_1955_, v_a_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(lean_object* v_m_1958_, lean_object* v_00_u03b1_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(v_m_1958_, v_00_u03b1_1959_, v_inst_1960_, v_inst_1961_, v_inst_1962_, v_a_1963_);
lean_dec(v_a_1963_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v_producers_1968_; lean_object* v_consumers_1969_; uint8_t v_closed_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1995_; 
v___x_1967_ = lean_st_ref_get(v_a_1965_);
v_producers_1968_ = lean_ctor_get(v___x_1967_, 0);
v_consumers_1969_ = lean_ctor_get(v___x_1967_, 1);
v_closed_1970_ = lean_ctor_get_uint8(v___x_1967_, sizeof(void*)*2);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1972_ = v___x_1967_;
v_isShared_1973_ = v_isSharedCheck_1995_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_consumers_1969_);
lean_inc(v_producers_1968_);
lean_dec(v___x_1967_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1995_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1968_);
if (lean_obj_tag(v___x_1974_) == 1)
{
lean_object* v_val_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1993_; 
v_val_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1993_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_val_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1993_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v_fst_1979_; lean_object* v_snd_1980_; lean_object* v_fst_1981_; lean_object* v_snd_1982_; lean_object* v___x_1984_; 
v_fst_1979_ = lean_ctor_get(v_val_1975_, 0);
lean_inc(v_fst_1979_);
v_snd_1980_ = lean_ctor_get(v_val_1975_, 1);
lean_inc(v_snd_1980_);
lean_dec(v_val_1975_);
v_fst_1981_ = lean_ctor_get(v_fst_1979_, 0);
lean_inc(v_fst_1981_);
v_snd_1982_ = lean_ctor_get(v_fst_1979_, 1);
lean_inc(v_snd_1982_);
lean_dec(v_fst_1979_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_snd_1980_);
v___x_1984_ = v___x_1972_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_snd_1980_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_consumers_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*2, v_closed_1970_);
v___x_1984_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1985_ = lean_st_ref_set(v_a_1965_, v___x_1984_);
v___x_1986_ = 1;
v___x_1987_ = lean_box(v___x_1986_);
v___x_1988_ = lean_io_promise_resolve(v___x_1987_, v_snd_1982_);
lean_dec(v_snd_1982_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v_fst_1981_);
v___x_1990_ = v___x_1977_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_fst_1981_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v___x_1994_; 
lean_dec(v___x_1974_);
lean_del_object(v___x_1972_);
lean_dec_ref(v_consumers_1969_);
v___x_1994_ = lean_box(0);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object* v_a_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1996_);
lean_dec(v_a_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object* v_00_u03b1_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_a_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_2003_, v_a_2004_);
lean_dec(v_a_2004_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object* v_ch_2008_){
_start:
{
lean_object* v___f_2010_; lean_object* v___x_2011_; 
v___f_2010_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0));
v___x_2011_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2008_, v___f_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object* v_ch_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object* v_00_u03b1_2015_, lean_object* v_ch_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object* v_00_u03b1_2019_, lean_object* v_ch_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(v_00_u03b1_2019_, v_ch_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object* v___f_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_st_ref_get(v___y_2024_);
v___x_2027_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_2024_);
if (lean_obj_tag(v___x_2027_) == 1)
{
lean_object* v___x_2028_; 
lean_dec(v___x_2026_);
lean_dec_ref(v___f_2023_);
v___x_2028_ = lean_task_pure(v___x_2027_);
return v___x_2028_;
}
else
{
uint8_t v_closed_2029_; 
lean_dec(v___x_2027_);
v_closed_2029_ = lean_ctor_get_uint8(v___x_2026_, sizeof(void*)*2);
if (v_closed_2029_ == 0)
{
lean_object* v_producers_2030_; lean_object* v_consumers_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2046_; 
v_producers_2030_ = lean_ctor_get(v___x_2026_, 0);
v_consumers_2031_ = lean_ctor_get(v___x_2026_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2033_ = v___x_2026_;
v_isShared_2034_ = v_isSharedCheck_2046_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_consumers_2031_);
lean_inc(v_producers_2030_);
lean_dec(v___x_2026_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2046_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2035_ = lean_io_promise_new();
lean_inc(v___x_2035_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
v___x_2037_ = l_Std_Queue_enqueue___redArg(v___x_2036_, v_consumers_2031_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v___x_2037_);
v___x_2039_ = v___x_2033_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_producers_2030_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2045_, sizeof(void*)*2, v_closed_2029_);
v___x_2039_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2040_ = lean_st_ref_set(v___y_2024_, v___x_2039_);
v___x_2041_ = 1;
v___x_2042_ = lean_io_promise_result_opt(v___x_2035_);
lean_dec(v___x_2035_);
v___x_2043_ = lean_unsigned_to_nat(0u);
v___x_2044_ = lean_task_map(v___f_2023_, v___x_2042_, v___x_2043_, v___x_2041_);
return v___x_2044_;
}
}
}
else
{
lean_object* v___x_2047_; 
lean_dec(v___x_2026_);
lean_dec_ref(v___f_2023_);
v___x_2047_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object* v___f_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2048_, v___y_2049_);
lean_dec(v___y_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object* v_ch_2054_){
_start:
{
lean_object* v___f_2056_; lean_object* v___x_2057_; 
v___f_2056_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0));
v___x_2057_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2054_, v___f_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object* v_ch_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object* v_00_u03b1_2061_, lean_object* v_ch_2062_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2062_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object* v_00_u03b1_2065_, lean_object* v_ch_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(v_00_u03b1_2065_, v_ch_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_2069_, lean_object* v_a_2070_){
_start:
{
uint8_t v___y_2072_; lean_object* v_producers_2076_; uint8_t v_closed_2077_; uint8_t v___x_2078_; 
v_producers_2076_ = lean_ctor_get(v_a_2070_, 0);
v_closed_2077_ = lean_ctor_get_uint8(v_a_2070_, sizeof(void*)*2);
v___x_2078_ = l_Std_Queue_isEmpty___redArg(v_producers_2076_);
if (v___x_2078_ == 0)
{
uint8_t v___x_2079_; 
v___x_2079_ = 1;
v___y_2072_ = v___x_2079_;
goto v___jp_2071_;
}
else
{
v___y_2072_ = v_closed_2077_;
goto v___jp_2071_;
}
v___jp_2071_:
{
lean_object* v_toPure_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_toPure_2073_ = lean_ctor_get(v_toApplicative_2069_, 1);
lean_inc(v_toPure_2073_);
lean_dec_ref(v_toApplicative_2069_);
v___x_2074_ = lean_box(v___y_2072_);
v___x_2075_ = lean_apply_2(v_toPure_2073_, lean_box(0), v___x_2074_);
return v___x_2075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(v_toApplicative_2080_, v_a_2081_);
lean_dec_ref(v_a_2081_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object* v_inst_2083_, lean_object* v_inst_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_toApplicative_2086_; lean_object* v_toBind_2087_; lean_object* v___f_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_toApplicative_2086_ = lean_ctor_get(v_inst_2083_, 0);
lean_inc_ref(v_toApplicative_2086_);
v_toBind_2087_ = lean_ctor_get(v_inst_2083_, 1);
lean_inc(v_toBind_2087_);
lean_dec_ref(v_inst_2083_);
v___f_2088_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2088_, 0, v_toApplicative_2086_);
lean_inc(v_a_2085_);
v___x_2089_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2089_, 0, lean_box(0));
lean_closure_set(v___x_2089_, 1, lean_box(0));
lean_closure_set(v___x_2089_, 2, v_a_2085_);
v___x_2090_ = lean_apply_2(v_inst_2084_, lean_box(0), v___x_2089_);
v___x_2091_ = lean_apply_4(v_toBind_2087_, lean_box(0), lean_box(0), v___x_2090_, v___f_2088_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(lean_object* v_inst_2092_, lean_object* v_inst_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(v_inst_2092_, v_inst_2093_, v_a_2094_);
lean_dec(v_a_2094_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object* v_m_2096_, lean_object* v_00_u03b1_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_toApplicative_2101_; lean_object* v_toBind_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_toApplicative_2101_ = lean_ctor_get(v_inst_2098_, 0);
lean_inc_ref(v_toApplicative_2101_);
v_toBind_2102_ = lean_ctor_get(v_inst_2098_, 1);
lean_inc(v_toBind_2102_);
lean_dec_ref(v_inst_2098_);
v___f_2103_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2103_, 0, v_toApplicative_2101_);
lean_inc(v_a_2100_);
v___x_2104_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2104_, 0, lean_box(0));
lean_closure_set(v___x_2104_, 1, lean_box(0));
lean_closure_set(v___x_2104_, 2, v_a_2100_);
v___x_2105_ = lean_apply_2(v_inst_2099_, lean_box(0), v___x_2104_);
v___x_2106_ = lean_apply_4(v_toBind_2102_, lean_box(0), lean_box(0), v___x_2105_, v___f_2103_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(lean_object* v_m_2107_, lean_object* v_00_u03b1_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(v_m_2107_, v_00_u03b1_2108_, v_inst_2109_, v_inst_2110_, v_a_2111_);
lean_dec(v_a_2111_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object* v_snd_2113_, lean_object* v___f_2114_, lean_object* v_x_2115_){
_start:
{
if (lean_obj_tag(v_x_2115_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2125_; 
lean_dec_ref(v___f_2114_);
v_a_2117_ = lean_ctor_get(v_x_2115_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_x_2115_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2119_ = v_x_2115_;
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v_x_2115_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
}
else
{
lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2139_; 
v_isSharedCheck_2139_ = !lean_is_exclusive(v_x_2115_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; 
v_unused_2140_ = lean_ctor_get(v_x_2115_, 0);
lean_dec(v_unused_2140_);
v___x_2127_ = v_x_2115_;
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
else
{
lean_dec(v_x_2115_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
uint8_t v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2129_ = 1;
v___x_2130_ = lean_box(v___x_2129_);
v___x_2131_ = lean_io_promise_resolve(v___x_2130_, v_snd_2113_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2131_);
v___x_2133_ = v___x_2127_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = 0;
v___x_2137_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2135_, v___x_2136_, v___x_2134_, v___f_2114_);
return v___x_2137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_snd_2141_, lean_object* v___f_2142_, lean_object* v_x_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2141_, v___f_2142_, v_x_2143_);
lean_dec(v_snd_2141_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object* v_a_2146_, lean_object* v_x_2147_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2157_; 
v_a_2149_ = lean_ctor_get(v_x_2147_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_x_2147_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2151_ = v_x_2147_;
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v_x_2147_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2195_; 
v_a_2158_ = lean_ctor_get(v_x_2147_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_x_2147_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2160_ = v_x_2147_;
v_isShared_2161_ = v_isSharedCheck_2195_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v_x_2147_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2195_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v_producers_2162_; lean_object* v_consumers_2163_; uint8_t v_closed_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2194_; 
v_producers_2162_ = lean_ctor_get(v_a_2158_, 0);
v_consumers_2163_ = lean_ctor_get(v_a_2158_, 1);
v_closed_2164_ = lean_ctor_get_uint8(v_a_2158_, sizeof(void*)*2);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_a_2158_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2166_ = v_a_2158_;
v_isShared_2167_ = v_isSharedCheck_2194_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_consumers_2163_);
lean_inc(v_producers_2162_);
lean_dec(v_a_2158_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2194_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2162_);
if (lean_obj_tag(v___x_2168_) == 1)
{
lean_object* v_val_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2192_; 
v_val_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2192_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_val_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2192_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v_fst_2173_; lean_object* v_snd_2174_; lean_object* v_fst_2175_; lean_object* v_snd_2176_; lean_object* v___x_2178_; 
v_fst_2173_ = lean_ctor_get(v_val_2169_, 0);
lean_inc(v_fst_2173_);
v_snd_2174_ = lean_ctor_get(v_val_2169_, 1);
lean_inc(v_snd_2174_);
lean_dec(v_val_2169_);
v_fst_2175_ = lean_ctor_get(v_fst_2173_, 0);
lean_inc(v_fst_2175_);
v_snd_2176_ = lean_ctor_get(v_fst_2173_, 1);
lean_inc(v_snd_2176_);
lean_dec(v_fst_2173_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v_snd_2174_);
v___x_2178_ = v___x_2166_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_snd_2174_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_consumers_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2191_, sizeof(void*)*2, v_closed_2164_);
v___x_2178_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; lean_object* v___f_2180_; lean_object* v___f_2181_; lean_object* v___x_2183_; 
v___x_2179_ = lean_st_ref_set(v_a_2146_, v___x_2178_);
v___f_2180_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2180_, 0, v_fst_2175_);
v___f_2181_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2181_, 0, v_snd_2176_);
lean_closure_set(v___f_2181_, 1, v___f_2180_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2179_);
v___x_2183_ = v___x_2160_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2179_);
v___x_2183_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2185_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set_tag(v___x_2171_, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2183_);
v___x_2185_ = v___x_2171_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = 0;
v___x_2188_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2186_, v___x_2187_, v___x_2185_, v___f_2181_);
return v___x_2188_;
}
}
}
}
}
else
{
lean_object* v___x_2193_; 
lean_dec(v___x_2168_);
lean_del_object(v___x_2166_);
lean_dec_ref(v_consumers_2163_);
lean_del_object(v___x_2160_);
v___x_2193_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_a_2196_, lean_object* v_x_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2196_, v_x_2197_);
lean_dec(v_a_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object* v_a_2200_){
_start:
{
lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; 
v___x_2202_ = lean_st_ref_get(v_a_2200_);
lean_inc(v_a_2200_);
v___f_2203_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2203_, 0, v_a_2200_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = 0;
v___x_2208_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2206_, v___x_2207_, v___x_2205_, v___f_2203_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object* v_a_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2209_);
lean_dec(v_a_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object* v_00_u03b1_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_2216_, lean_object* v_a_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_2216_, v_a_2217_);
lean_dec(v_a_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_2220_, lean_object* v___y_2221_, lean_object* v___f_2222_, lean_object* v_x_2223_){
_start:
{
if (lean_obj_tag(v_x_2223_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v___f_2222_);
lean_dec_ref(v_lose_2220_);
v_a_2225_ = lean_ctor_get(v_x_2223_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_x_2223_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2227_ = v_x_2223_;
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v_x_2223_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
return v___x_2231_;
}
}
}
else
{
lean_object* v_a_2234_; uint8_t v___x_2235_; 
v_a_2234_ = lean_ctor_get(v_x_2223_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v_x_2223_, 1);
v___x_2235_ = lean_unbox(v_a_2234_);
lean_dec(v_a_2234_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; 
lean_dec_ref(v___f_2222_);
lean_inc(v___y_2221_);
v___x_2236_ = lean_apply_2(v_lose_2220_, v___y_2221_, lean_box(0));
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_lose_2220_);
v___x_2237_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2221_);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = 0;
v___x_2240_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2238_, v___x_2239_, v___x_2237_, v___f_2222_);
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_2241_, lean_object* v___y_2242_, lean_object* v___f_2243_, lean_object* v_x_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2241_, v___y_2242_, v___f_2243_, v_x_2244_);
lean_dec(v___y_2242_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object* v_w_2247_, lean_object* v_lose_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_finished_2251_; lean_object* v_promise_2252_; lean_object* v___x_2253_; lean_object* v___f_2254_; lean_object* v___f_2255_; uint8_t v___y_2257_; uint8_t v___x_2267_; 
v_finished_2251_ = lean_ctor_get(v_w_2247_, 0);
lean_inc(v_finished_2251_);
v_promise_2252_ = lean_ctor_get(v_w_2247_, 1);
lean_inc(v_promise_2252_);
lean_dec_ref(v_w_2247_);
v___x_2253_ = lean_st_ref_take(v_finished_2251_);
v___f_2254_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2254_, 0, v_promise_2252_);
lean_inc(v___y_2249_);
v___f_2255_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2255_, 0, v_lose_2248_);
lean_closure_set(v___f_2255_, 1, v___y_2249_);
lean_closure_set(v___f_2255_, 2, v___f_2254_);
v___x_2267_ = lean_unbox(v___x_2253_);
lean_dec(v___x_2253_);
if (v___x_2267_ == 0)
{
uint8_t v___x_2268_; 
v___x_2268_ = 1;
v___y_2257_ = v___x_2268_;
goto v___jp_2256_;
}
else
{
uint8_t v___x_2269_; 
v___x_2269_ = 0;
v___y_2257_ = v___x_2269_;
goto v___jp_2256_;
}
v___jp_2256_:
{
uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; 
v___x_2258_ = 1;
v___x_2259_ = lean_box(v___x_2258_);
v___x_2260_ = lean_st_ref_set(v_finished_2251_, v___x_2259_);
lean_dec(v_finished_2251_);
v___x_2261_ = lean_box(v___y_2257_);
v___x_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = lean_unsigned_to_nat(0u);
v___x_2265_ = 0;
v___x_2266_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2264_, v___x_2265_, v___x_2263_, v___f_2255_);
return v___x_2266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object* v_w_2270_, lean_object* v_lose_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2270_, v_lose_2271_, v___y_2272_);
lean_dec(v___y_2272_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object* v_00_u03b1_2275_, lean_object* v_w_2276_, lean_object* v_lose_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2276_, v_lose_2277_, v___y_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_2281_, lean_object* v_w_2282_, lean_object* v_lose_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_2281_, v_w_2282_, v_lose_2283_, v___y_2284_);
lean_dec(v___y_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object* v_x_2287_){
_start:
{
uint8_t v___y_2290_; 
if (lean_obj_tag(v_x_2287_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_a_2294_ = lean_ctor_get(v_x_2287_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_x_2287_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v_x_2287_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v_x_2287_);
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
lean_object* v_a_2303_; lean_object* v_producers_2304_; uint8_t v_closed_2305_; uint8_t v___x_2306_; 
v_a_2303_ = lean_ctor_get(v_x_2287_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v_x_2287_, 1);
v_producers_2304_ = lean_ctor_get(v_a_2303_, 0);
lean_inc_ref(v_producers_2304_);
v_closed_2305_ = lean_ctor_get_uint8(v_a_2303_, sizeof(void*)*2);
lean_dec(v_a_2303_);
v___x_2306_ = l_Std_Queue_isEmpty___redArg(v_producers_2304_);
lean_dec_ref(v_producers_2304_);
if (v___x_2306_ == 0)
{
uint8_t v___x_2307_; 
v___x_2307_ = 1;
v___y_2290_ = v___x_2307_;
goto v___jp_2289_;
}
else
{
v___y_2290_ = v_closed_2305_;
goto v___jp_2289_;
}
}
v___jp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_box(v___y_2290_);
v___x_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object* v_x_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object* v___y_2311_, lean_object* v_waiter_2312_, lean_object* v_x_2313_){
_start:
{
if (lean_obj_tag(v_x_2313_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v_waiter_2312_);
v_a_2315_ = lean_ctor_get(v_x_2313_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_x_2313_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2317_ = v_x_2313_;
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v_x_2313_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
}
}
else
{
lean_object* v_a_2324_; uint8_t v___x_2325_; 
v_a_2324_ = lean_ctor_get(v_x_2313_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v_x_2313_, 1);
v___x_2325_ = lean_unbox(v_a_2324_);
lean_dec(v_a_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; lean_object* v_producers_2327_; lean_object* v_consumers_2328_; uint8_t v_closed_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2340_; 
v___x_2326_ = lean_st_ref_take(v___y_2311_);
v_producers_2327_ = lean_ctor_get(v___x_2326_, 0);
v_consumers_2328_ = lean_ctor_get(v___x_2326_, 1);
v_closed_2329_ = lean_ctor_get_uint8(v___x_2326_, sizeof(void*)*2);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2331_ = v___x_2326_;
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_consumers_2328_);
lean_inc(v_producers_2327_);
lean_dec(v___x_2326_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_waiter_2312_);
v___x_2334_ = l_Std_Queue_enqueue___redArg(v___x_2333_, v_consumers_2328_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v___x_2334_);
v___x_2336_ = v___x_2331_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_producers_2327_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2334_);
lean_ctor_set_uint8(v_reuseFailAlloc_2339_, sizeof(void*)*2, v_closed_2329_);
v___x_2336_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_st_ref_set(v___y_2311_, v___x_2336_);
v___x_2338_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_2338_;
}
}
}
else
{
lean_object* v_lose_2341_; lean_object* v___x_2342_; 
v_lose_2341_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2));
v___x_2342_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_2312_, v_lose_2341_, v___y_2311_);
return v___x_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object* v___y_2343_, lean_object* v_waiter_2344_, lean_object* v_x_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2343_, v_waiter_2344_, v_x_2345_);
lean_dec(v___y_2343_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object* v___f_2348_, lean_object* v_waiter_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___f_2358_; lean_object* v___x_2359_; 
v___x_2352_ = lean_st_ref_get(v___y_2350_);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = 0;
v___x_2357_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2355_, v___x_2356_, v___x_2354_, v___f_2348_);
lean_inc(v___y_2350_);
v___f_2358_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2358_, 0, v___y_2350_);
lean_closure_set(v___f_2358_, 1, v_waiter_2349_);
v___x_2359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2355_, v___x_2356_, v___x_2357_, v___f_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object* v___f_2360_, lean_object* v_waiter_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v___f_2360_, v_waiter_2361_, v___y_2362_);
lean_dec(v___y_2362_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object* v___f_2365_, lean_object* v_ch_2366_, lean_object* v_waiter_2367_){
_start:
{
lean_object* v___f_2369_; lean_object* v___x_2370_; 
v___f_2369_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2369_, 0, v___f_2365_);
lean_closure_set(v___f_2369_, 1, v_waiter_2367_);
v___x_2370_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_2366_, v___f_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object* v___f_2371_, lean_object* v_ch_2372_, lean_object* v_waiter_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2371_, v_ch_2372_, v_waiter_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object* v___y_2376_, lean_object* v___f_2377_, lean_object* v_x_2378_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v___f_2377_);
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
lean_object* v_a_2389_; uint8_t v___x_2390_; 
v_a_2389_ = lean_ctor_get(v_x_2378_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v_x_2378_, 1);
v___x_2390_ = lean_unbox(v_a_2389_);
lean_dec(v_a_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; 
lean_dec_ref(v___f_2377_);
v___x_2391_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; 
v___x_2392_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2376_);
v___x_2393_ = lean_unsigned_to_nat(0u);
v___x_2394_ = 0;
v___x_2395_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2393_, v___x_2394_, v___x_2392_, v___f_2377_);
return v___x_2395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object* v___y_2396_, lean_object* v___f_2397_, lean_object* v_x_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2396_, v___f_2397_, v_x_2398_);
lean_dec(v___y_2396_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object* v___f_2401_, lean_object* v___f_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___f_2411_; lean_object* v___x_2412_; 
v___x_2405_ = lean_st_ref_get(v___y_2403_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
v___x_2408_ = lean_unsigned_to_nat(0u);
v___x_2409_ = 0;
v___x_2410_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2408_, v___x_2409_, v___x_2407_, v___f_2401_);
lean_inc(v___y_2403_);
v___f_2411_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2411_, 0, v___y_2403_);
lean_closure_set(v___f_2411_, 1, v___f_2402_);
v___x_2412_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2408_, v___x_2409_, v___x_2410_, v___f_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object* v___f_2413_, lean_object* v___f_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2413_, v___f_2414_, v___y_2415_);
lean_dec(v___y_2415_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object* v_producers_2418_, uint8_t v_closed_2419_, lean_object* v___y_2420_, lean_object* v_x_2421_){
_start:
{
if (lean_obj_tag(v_x_2421_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2431_; 
lean_dec_ref(v_producers_2418_);
v_a_2423_ = lean_ctor_get(v_x_2421_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_x_2421_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2425_ = v_x_2421_;
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v_x_2421_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
return v___x_2429_;
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2442_; 
v_a_2432_ = lean_ctor_get(v_x_2421_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_x_2421_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2434_ = v_x_2421_;
v_isShared_2435_ = v_isSharedCheck_2442_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v_x_2421_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2442_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2436_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2436_, 0, v_producers_2418_);
lean_ctor_set(v___x_2436_, 1, v_a_2432_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*2, v_closed_2419_);
v___x_2437_ = lean_st_ref_set(v___y_2420_, v___x_2436_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2437_);
v___x_2439_ = v___x_2434_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2437_);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object* v_producers_2443_, lean_object* v_closed_2444_, lean_object* v___y_2445_, lean_object* v_x_2446_, lean_object* v___y_2447_){
_start:
{
uint8_t v_closed_boxed_2448_; lean_object* v_res_2449_; 
v_closed_boxed_2448_ = lean_unbox(v_closed_2444_);
v_res_2449_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2443_, v_closed_boxed_2448_, v___y_2445_, v_x_2446_);
lean_dec(v___y_2445_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_2450_, lean_object* v_x_2451_, lean_object* v_head_2452_, lean_object* v_x_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2450_, v_x_2451_, v_head_2452_, v_x_2453_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object* v_x_2456_, lean_object* v_x_2457_){
_start:
{
if (lean_obj_tag(v_x_2456_) == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2459_, 0, v_x_2457_);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
else
{
lean_object* v_head_2461_; lean_object* v_tail_2462_; lean_object* v___f_2463_; lean_object* v_val_2465_; 
v_head_2461_ = lean_ctor_get(v_x_2456_, 0);
lean_inc_n(v_head_2461_, 2);
v_tail_2462_ = lean_ctor_get(v_x_2456_, 1);
lean_inc(v_tail_2462_);
lean_dec_ref_known(v_x_2456_, 2);
v___f_2463_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2463_, 0, v_tail_2462_);
lean_closure_set(v___f_2463_, 1, v_x_2457_);
lean_closure_set(v___f_2463_, 2, v_head_2461_);
if (lean_obj_tag(v_head_2461_) == 0)
{
lean_object* v___x_2469_; 
lean_dec_ref_known(v_head_2461_, 1);
v___x_2469_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_2465_ = v___x_2469_;
goto v___jp_2464_;
}
else
{
lean_object* v_finished_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2484_; 
v_finished_2470_ = lean_ctor_get(v_head_2461_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_head_2461_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2472_ = v_head_2461_;
v_isShared_2473_ = v_isSharedCheck_2484_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_finished_2470_);
lean_dec(v_head_2461_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2484_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v_finished_2474_; lean_object* v___x_2475_; lean_object* v___f_2476_; lean_object* v___x_2478_; 
v_finished_2474_ = lean_ctor_get(v_finished_2470_, 0);
lean_inc(v_finished_2474_);
lean_dec_ref(v_finished_2470_);
v___x_2475_ = lean_st_ref_get(v_finished_2474_);
lean_dec(v_finished_2474_);
v___f_2476_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2475_);
v___x_2478_ = v___x_2472_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2475_);
v___x_2478_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; 
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
v___x_2480_ = lean_unsigned_to_nat(0u);
v___x_2481_ = 0;
v___x_2482_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2480_, v___x_2481_, v___x_2479_, v___f_2476_);
v_val_2465_ = v___x_2482_;
goto v___jp_2464_;
}
}
}
v___jp_2464_:
{
lean_object* v___x_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = 0;
v___x_2468_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2466_, v___x_2467_, v_val_2465_, v___f_2463_);
return v___x_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_2485_, lean_object* v_x_2486_, lean_object* v_head_2487_, lean_object* v_x_2488_){
_start:
{
if (lean_obj_tag(v_x_2488_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v_head_2487_);
lean_dec(v_x_2486_);
lean_dec(v_tail_2485_);
v_a_2490_ = lean_ctor_get(v_x_2488_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_x_2488_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2492_ = v_x_2488_;
v_isShared_2493_ = v_isSharedCheck_2498_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v_x_2488_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2498_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
return v___x_2496_;
}
}
}
else
{
lean_object* v_a_2499_; uint8_t v___x_2500_; 
v_a_2499_ = lean_ctor_get(v_x_2488_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v_x_2488_, 1);
v___x_2500_ = lean_unbox(v_a_2499_);
lean_dec(v_a_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; 
lean_dec_ref(v_head_2487_);
v___x_2501_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2485_, v_x_2486_);
return v___x_2501_;
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2502_, 0, v_head_2487_);
lean_ctor_set(v___x_2502_, 1, v_x_2486_);
v___x_2503_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2485_, v___x_2502_);
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object* v_x_2504_, lean_object* v_x_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2504_, v_x_2505_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object* v_eList_2508_, lean_object* v___x_2509_, lean_object* v___f_2510_, lean_object* v_x_2511_){
_start:
{
if (lean_obj_tag(v_x_2511_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v___f_2510_);
lean_dec(v___x_2509_);
lean_dec(v_eList_2508_);
v_a_2513_ = lean_ctor_get(v_x_2511_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2515_ = v_x_2511_;
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v_x_2511_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; 
v_a_2522_ = lean_ctor_get(v_x_2511_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v_x_2511_, 1);
lean_inc(v___x_2509_);
v___x_2523_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_2508_, v___x_2509_);
v___x_2524_ = lean_unsigned_to_nat(0u);
v___x_2525_ = 0;
v___x_2526_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2524_, v___x_2525_, v___x_2523_, v___f_2510_);
v___f_2527_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2527_, 0, v_a_2522_);
lean_closure_set(v___f_2527_, 1, v___x_2509_);
v___x_2528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2524_, v___x_2525_, v___x_2526_, v___f_2527_);
return v___x_2528_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_eList_2529_, lean_object* v___x_2530_, lean_object* v___f_2531_, lean_object* v_x_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v_eList_2529_, v___x_2530_, v___f_2531_, v_x_2532_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object* v_q_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_eList_2538_; lean_object* v_dList_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; 
v_eList_2538_ = lean_ctor_get(v_q_2535_, 0);
lean_inc(v_eList_2538_);
v_dList_2539_ = lean_ctor_get(v_q_2535_, 1);
lean_inc(v_dList_2539_);
lean_dec_ref(v_q_2535_);
v___x_2540_ = lean_box(0);
v___x_2541_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_2539_, v___x_2540_);
v___f_2542_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = 0;
v___x_2545_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2543_, v___x_2544_, v___x_2541_, v___f_2542_);
v___f_2546_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2546_, 0, v_eList_2538_);
lean_closure_set(v___f_2546_, 1, v___x_2540_);
lean_closure_set(v___f_2546_, 2, v___f_2542_);
v___x_2547_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2543_, v___x_2544_, v___x_2545_, v___f_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object* v_q_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2548_, v___y_2549_);
lean_dec(v___y_2549_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object* v___y_2552_, lean_object* v_x_2553_){
_start:
{
if (lean_obj_tag(v_x_2553_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2563_; 
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
lean_object* v_a_2564_; lean_object* v_producers_2565_; lean_object* v_consumers_2566_; uint8_t v_closed_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___f_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; 
v_a_2564_ = lean_ctor_get(v_x_2553_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v_x_2553_, 1);
v_producers_2565_ = lean_ctor_get(v_a_2564_, 0);
lean_inc_ref(v_producers_2565_);
v_consumers_2566_ = lean_ctor_get(v_a_2564_, 1);
lean_inc_ref(v_consumers_2566_);
v_closed_2567_ = lean_ctor_get_uint8(v_a_2564_, sizeof(void*)*2);
lean_dec(v_a_2564_);
v___x_2568_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_2566_, v___y_2552_);
v___x_2569_ = lean_box(v_closed_2567_);
lean_inc(v___y_2552_);
v___f_2570_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2570_, 0, v_producers_2565_);
lean_closure_set(v___f_2570_, 1, v___x_2569_);
lean_closure_set(v___f_2570_, 2, v___y_2552_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = 0;
v___x_2573_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2571_, v___x_2572_, v___x_2568_, v___f_2570_);
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object* v___y_2574_, lean_object* v_x_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2574_, v_x_2575_);
lean_dec(v___y_2574_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; lean_object* v___f_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; 
v___x_2580_ = lean_st_ref_get(v___y_2578_);
lean_inc(v___y_2578_);
v___f_2581_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2581_, 0, v___y_2578_);
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
v___x_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = 0;
v___x_2586_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2584_, v___x_2585_, v___x_2583_, v___f_2581_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2587_);
lean_dec(v___y_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object* v_ch_2595_){
_start:
{
lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___f_2596_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0));
lean_inc_ref_n(v_ch_2595_, 2);
v___f_2597_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2597_, 0, v___f_2596_);
lean_closure_set(v___f_2597_, 1, v_ch_2595_);
v___f_2598_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1));
v___f_2599_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2));
v___x_2600_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2600_, 0, lean_box(0));
lean_closure_set(v___x_2600_, 1, lean_box(0));
lean_closure_set(v___x_2600_, 2, v_ch_2595_);
lean_closure_set(v___x_2600_, 3, v___f_2598_);
v___x_2601_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2601_, 0, lean_box(0));
lean_closure_set(v___x_2601_, 1, lean_box(0));
lean_closure_set(v___x_2601_, 2, v_ch_2595_);
lean_closure_set(v___x_2601_, 3, v___f_2599_);
v___x_2602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___f_2597_);
lean_ctor_set(v___x_2602_, 2, v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object* v_00_u03b1_2603_, lean_object* v_ch_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object* v_00_u03b1_2606_, lean_object* v_q_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2607_, v___y_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_2611_, lean_object* v_q_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_2611_, v_q_2612_, v___y_2613_);
lean_dec(v___y_2613_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object* v_00_u03b1_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2617_, v_x_2618_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_2622_, v_x_2623_, v_x_2624_, v___y_2625_);
lean_dec(v___y_2625_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object* v_c_2628_, uint8_t v_b_2629_){
_start:
{
lean_object* v_promise_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_promise_2631_ = lean_ctor_get(v_c_2628_, 0);
v___x_2632_ = lean_box(v_b_2629_);
v___x_2633_ = lean_io_promise_resolve(v___x_2632_, v_promise_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object* v_c_2634_, lean_object* v_b_2635_, lean_object* v_a_2636_){
_start:
{
uint8_t v_b_boxed_2637_; lean_object* v_res_2638_; 
v_b_boxed_2637_ = lean_unbox(v_b_2635_);
v_res_2638_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2634_, v_b_boxed_2637_);
lean_dec_ref(v_c_2634_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object* v_00_u03b1_2639_, lean_object* v_c_2640_, uint8_t v_b_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2640_, v_b_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object* v_00_u03b1_2644_, lean_object* v_c_2645_, lean_object* v_b_2646_, lean_object* v_a_2647_){
_start:
{
uint8_t v_b_boxed_2648_; lean_object* v_res_2649_; 
v_b_boxed_2648_ = lean_unbox(v_b_2646_);
v_res_2649_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(v_00_u03b1_2644_, v_c_2645_, v_b_boxed_2648_);
lean_dec_ref(v_c_2645_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object* v_x_2650_){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_box(0);
v___x_2653_ = lean_st_mk_ref(v___x_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2654_);
lean_dec(v_x_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object* v_n_2657_, lean_object* v_f_2658_, lean_object* v_xs_2659_, lean_object* v_k_2660_, lean_object* v_acc_2661_){
_start:
{
uint8_t v___x_2663_; 
v___x_2663_ = lean_nat_dec_lt(v_k_2660_, v_n_2657_);
if (v___x_2663_ == 0)
{
lean_dec(v_k_2660_);
lean_dec_ref(v_f_2658_);
return v_acc_2661_;
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2664_ = lean_array_fget_borrowed(v_xs_2659_, v_k_2660_);
lean_inc_ref(v_f_2658_);
lean_inc(v___x_2664_);
v___x_2665_ = lean_apply_2(v_f_2658_, v___x_2664_, lean_box(0));
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_nat_add(v_k_2660_, v___x_2666_);
lean_dec(v_k_2660_);
v___x_2668_ = lean_array_push(v_acc_2661_, v___x_2665_);
v_k_2660_ = v___x_2667_;
v_acc_2661_ = v___x_2668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_2670_, lean_object* v_f_2671_, lean_object* v_xs_2672_, lean_object* v_k_2673_, lean_object* v_acc_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2670_, v_f_2671_, v_xs_2672_, v_k_2673_, v_acc_2674_);
lean_dec_ref(v_xs_2672_);
lean_dec(v_n_2670_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object* v_capacity_2680_){
_start:
{
lean_object* v___f_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___f_2682_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0));
lean_inc(v_capacity_2680_);
v___x_2683_ = l_Array_range(v_capacity_2680_);
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1));
v___x_2686_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_2680_, v___f_2682_, v___x_2683_, v___x_2684_, v___x_2685_);
lean_dec_ref(v___x_2683_);
v___x_2687_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2688_ = 0;
v___x_2689_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2687_);
lean_ctor_set(v___x_2689_, 2, v_capacity_2680_);
lean_ctor_set(v___x_2689_, 3, v___x_2686_);
lean_ctor_set(v___x_2689_, 4, v___x_2684_);
lean_ctor_set(v___x_2689_, 5, v___x_2684_);
lean_ctor_set(v___x_2689_, 6, v___x_2684_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*7, v___x_2688_);
v___x_2690_ = l_Std_Mutex_new___redArg(v___x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object* v_capacity_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object* v_00_u03b1_2694_, lean_object* v_capacity_2695_, lean_object* v_hcap_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2695_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object* v_00_u03b1_2699_, lean_object* v_capacity_2700_, lean_object* v_hcap_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(v_00_u03b1_2699_, v_capacity_2700_, v_hcap_2701_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object* v_00_u03b1_2704_, lean_object* v_00_u03b2_2705_, lean_object* v_n_2706_, lean_object* v_f_2707_, lean_object* v_xs_2708_, lean_object* v_k_2709_, lean_object* v_h_2710_, lean_object* v_acc_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2706_, v_f_2707_, v_xs_2708_, v_k_2709_, v_acc_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_00_u03b2_2715_, lean_object* v_n_2716_, lean_object* v_f_2717_, lean_object* v_xs_2718_, lean_object* v_k_2719_, lean_object* v_h_2720_, lean_object* v_acc_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_2714_, v_00_u03b2_2715_, v_n_2716_, v_f_2717_, v_xs_2718_, v_k_2719_, v_h_2720_, v_acc_2721_);
lean_dec_ref(v_xs_2718_);
lean_dec(v_n_2716_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object* v_idx_2724_, lean_object* v_cap_2725_){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_add(v_idx_2724_, v___x_2726_);
v___x_2728_ = lean_nat_dec_eq(v___x_2727_, v_cap_2725_);
if (v___x_2728_ == 0)
{
return v___x_2727_;
}
else
{
lean_object* v___x_2729_; 
lean_dec(v___x_2727_);
v___x_2729_ = lean_unsigned_to_nat(0u);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object* v_idx_2730_, lean_object* v_cap_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(v_idx_2730_, v_cap_2731_);
lean_dec(v_cap_2731_);
lean_dec(v_idx_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object* v_v_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v_st_2737_; lean_object* v___y_2738_; lean_object* v___x_2741_; lean_object* v_producers_2742_; lean_object* v_consumers_2743_; lean_object* v_capacity_2744_; lean_object* v_buf_2745_; lean_object* v_bufCount_2746_; lean_object* v_sendIdx_2747_; lean_object* v_recvIdx_2748_; uint8_t v_closed_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2775_; 
v___x_2741_ = lean_st_ref_get(v_a_2734_);
v_producers_2742_ = lean_ctor_get(v___x_2741_, 0);
v_consumers_2743_ = lean_ctor_get(v___x_2741_, 1);
v_capacity_2744_ = lean_ctor_get(v___x_2741_, 2);
v_buf_2745_ = lean_ctor_get(v___x_2741_, 3);
v_bufCount_2746_ = lean_ctor_get(v___x_2741_, 4);
v_sendIdx_2747_ = lean_ctor_get(v___x_2741_, 5);
v_recvIdx_2748_ = lean_ctor_get(v___x_2741_, 6);
v_closed_2749_ = lean_ctor_get_uint8(v___x_2741_, sizeof(void*)*7);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2751_ = v___x_2741_;
v_isShared_2752_ = v_isSharedCheck_2775_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_recvIdx_2748_);
lean_inc(v_sendIdx_2747_);
lean_inc(v_bufCount_2746_);
lean_inc(v_buf_2745_);
lean_inc(v_capacity_2744_);
lean_inc(v_consumers_2743_);
lean_inc(v_producers_2742_);
lean_dec(v___x_2741_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2775_;
goto v_resetjp_2750_;
}
v___jp_2736_:
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = lean_st_ref_set(v___y_2738_, v_st_2737_);
v___x_2740_ = 1;
return v___x_2740_;
}
v_resetjp_2750_:
{
uint8_t v___x_2753_; 
v___x_2753_ = lean_nat_dec_eq(v_bufCount_2746_, v_capacity_2744_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___y_2760_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2754_ = lean_array_fget_borrowed(v_buf_2745_, v_sendIdx_2747_);
v___x_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_v_2733_);
v___x_2756_ = lean_st_ref_set(v___x_2754_, v___x_2755_);
v___x_2757_ = lean_unsigned_to_nat(1u);
v___x_2758_ = lean_nat_add(v_bufCount_2746_, v___x_2757_);
lean_dec(v_bufCount_2746_);
v___x_2771_ = lean_nat_add(v_sendIdx_2747_, v___x_2757_);
lean_dec(v_sendIdx_2747_);
v___x_2772_ = lean_nat_dec_eq(v___x_2771_, v_capacity_2744_);
if (v___x_2772_ == 0)
{
v___y_2760_ = v___x_2771_;
goto v___jp_2759_;
}
else
{
lean_object* v___x_2773_; 
lean_dec(v___x_2771_);
v___x_2773_ = lean_unsigned_to_nat(0u);
v___y_2760_ = v___x_2773_;
goto v___jp_2759_;
}
v___jp_2759_:
{
lean_object* v___x_2762_; 
lean_inc(v_recvIdx_2748_);
lean_inc(v___y_2760_);
lean_inc(v___x_2758_);
lean_inc_ref(v_buf_2745_);
lean_inc(v_capacity_2744_);
lean_inc_ref(v_consumers_2743_);
lean_inc_ref(v_producers_2742_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 5, v___y_2760_);
lean_ctor_set(v___x_2751_, 4, v___x_2758_);
v___x_2762_ = v___x_2751_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_producers_2742_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_consumers_2743_);
lean_ctor_set(v_reuseFailAlloc_2770_, 2, v_capacity_2744_);
lean_ctor_set(v_reuseFailAlloc_2770_, 3, v_buf_2745_);
lean_ctor_set(v_reuseFailAlloc_2770_, 4, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2770_, 5, v___y_2760_);
lean_ctor_set(v_reuseFailAlloc_2770_, 6, v_recvIdx_2748_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, sizeof(void*)*7, v_closed_2749_);
v___x_2762_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_2743_);
if (lean_obj_tag(v___x_2763_) == 1)
{
lean_object* v_val_2764_; lean_object* v_fst_2765_; lean_object* v_snd_2766_; uint8_t v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_dec_ref(v___x_2762_);
v_val_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v___x_2763_, 1);
v_fst_2765_ = lean_ctor_get(v_val_2764_, 0);
lean_inc(v_fst_2765_);
v_snd_2766_ = lean_ctor_get(v_val_2764_, 1);
lean_inc(v_snd_2766_);
lean_dec(v_val_2764_);
v___x_2767_ = 1;
v___x_2768_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_2765_, v___x_2767_);
lean_dec(v_fst_2765_);
v___x_2769_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2769_, 0, v_producers_2742_);
lean_ctor_set(v___x_2769_, 1, v_snd_2766_);
lean_ctor_set(v___x_2769_, 2, v_capacity_2744_);
lean_ctor_set(v___x_2769_, 3, v_buf_2745_);
lean_ctor_set(v___x_2769_, 4, v___x_2758_);
lean_ctor_set(v___x_2769_, 5, v___y_2760_);
lean_ctor_set(v___x_2769_, 6, v_recvIdx_2748_);
lean_ctor_set_uint8(v___x_2769_, sizeof(void*)*7, v_closed_2749_);
v_st_2737_ = v___x_2769_;
v___y_2738_ = v_a_2734_;
goto v___jp_2736_;
}
else
{
lean_dec(v___x_2763_);
lean_dec(v___y_2760_);
lean_dec(v___x_2758_);
lean_dec(v_recvIdx_2748_);
lean_dec_ref(v_buf_2745_);
lean_dec(v_capacity_2744_);
lean_dec_ref(v_producers_2742_);
v_st_2737_ = v___x_2762_;
v___y_2738_ = v_a_2734_;
goto v___jp_2736_;
}
}
}
}
else
{
uint8_t v___x_2774_; 
lean_del_object(v___x_2751_);
lean_dec(v_recvIdx_2748_);
lean_dec(v_sendIdx_2747_);
lean_dec(v_bufCount_2746_);
lean_dec_ref(v_buf_2745_);
lean_dec(v_capacity_2744_);
lean_dec_ref(v_consumers_2743_);
lean_dec_ref(v_producers_2742_);
lean_dec(v_v_2733_);
v___x_2774_ = 0;
return v___x_2774_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
uint8_t v_res_2779_; lean_object* v_r_2780_; 
v_res_2779_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2776_, v_a_2777_);
lean_dec(v_a_2777_);
v_r_2780_ = lean_box(v_res_2779_);
return v_r_2780_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object* v_00_u03b1_2781_, lean_object* v_v_2782_, lean_object* v_a_2783_){
_start:
{
uint8_t v___x_2785_; 
v___x_2785_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2782_, v_a_2783_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_2786_, lean_object* v_v_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
uint8_t v_res_2790_; lean_object* v_r_2791_; 
v_res_2790_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(v_00_u03b1_2786_, v_v_2787_, v_a_2788_);
lean_dec(v_a_2788_);
v_r_2791_ = lean_box(v_res_2790_);
return v_r_2791_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object* v_v_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v___x_2795_; uint8_t v_closed_2796_; 
v___x_2795_ = lean_st_ref_get(v___y_2793_);
v_closed_2796_ = lean_ctor_get_uint8(v___x_2795_, sizeof(void*)*7);
lean_dec(v___x_2795_);
if (v_closed_2796_ == 0)
{
uint8_t v___x_2797_; 
v___x_2797_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2792_, v___y_2793_);
return v___x_2797_;
}
else
{
uint8_t v___x_2798_; 
lean_dec(v_v_2792_);
v___x_2798_ = 0;
return v___x_2798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
uint8_t v_res_2802_; lean_object* v_r_2803_; 
v_res_2802_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2799_, v___y_2800_);
lean_dec(v___y_2800_);
v_r_2803_ = lean_box(v_res_2802_);
return v_r_2803_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object* v_ch_2804_, lean_object* v_v_2805_){
_start:
{
lean_object* v___f_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___f_2807_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2807_, 0, v_v_2805_);
v___x_2808_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2804_, v___f_2807_);
v___x_2809_ = lean_unbox(v___x_2808_);
lean_dec(v___x_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object* v_ch_2810_, lean_object* v_v_2811_, lean_object* v_a_2812_){
_start:
{
uint8_t v_res_2813_; lean_object* v_r_2814_; 
v_res_2813_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2810_, v_v_2811_);
v_r_2814_ = lean_box(v_res_2813_);
return v_r_2814_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object* v_00_u03b1_2815_, lean_object* v_ch_2816_, lean_object* v_v_2817_){
_start:
{
uint8_t v___x_2819_; 
v___x_2819_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2816_, v_v_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(lean_object* v_00_u03b1_2820_, lean_object* v_ch_2821_, lean_object* v_v_2822_, lean_object* v_a_2823_){
_start:
{
uint8_t v_res_2824_; lean_object* v_r_2825_; 
v_res_2824_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(v_00_u03b1_2820_, v_ch_2821_, v_v_2822_);
v_r_2825_ = lean_box(v_res_2824_);
return v_r_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(lean_object* v_v_2826_, lean_object* v___f_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; uint8_t v_closed_2831_; 
v___x_2830_ = lean_st_ref_get(v___y_2828_);
v_closed_2831_ = lean_ctor_get_uint8(v___x_2830_, sizeof(void*)*7);
lean_dec(v___x_2830_);
if (v_closed_2831_ == 0)
{
uint8_t v___x_2832_; 
v___x_2832_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2826_, v___y_2828_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v_producers_2835_; lean_object* v_consumers_2836_; lean_object* v_capacity_2837_; lean_object* v_buf_2838_; lean_object* v_bufCount_2839_; lean_object* v_sendIdx_2840_; lean_object* v_recvIdx_2841_; uint8_t v_closed_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2854_; 
v___x_2833_ = lean_io_promise_new();
v___x_2834_ = lean_st_ref_take(v___y_2828_);
v_producers_2835_ = lean_ctor_get(v___x_2834_, 0);
v_consumers_2836_ = lean_ctor_get(v___x_2834_, 1);
v_capacity_2837_ = lean_ctor_get(v___x_2834_, 2);
v_buf_2838_ = lean_ctor_get(v___x_2834_, 3);
v_bufCount_2839_ = lean_ctor_get(v___x_2834_, 4);
v_sendIdx_2840_ = lean_ctor_get(v___x_2834_, 5);
v_recvIdx_2841_ = lean_ctor_get(v___x_2834_, 6);
v_closed_2842_ = lean_ctor_get_uint8(v___x_2834_, sizeof(void*)*7);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2844_ = v___x_2834_;
v_isShared_2845_ = v_isSharedCheck_2854_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_recvIdx_2841_);
lean_inc(v_sendIdx_2840_);
lean_inc(v_bufCount_2839_);
lean_inc(v_buf_2838_);
lean_inc(v_capacity_2837_);
lean_inc(v_consumers_2836_);
lean_inc(v_producers_2835_);
lean_dec(v___x_2834_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2854_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2848_; 
lean_inc(v___x_2833_);
v___x_2846_ = l_Std_Queue_enqueue___redArg(v___x_2833_, v_producers_2835_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2846_);
v___x_2848_ = v___x_2844_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2846_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_consumers_2836_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_capacity_2837_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_buf_2838_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_bufCount_2839_);
lean_ctor_set(v_reuseFailAlloc_2853_, 5, v_sendIdx_2840_);
lean_ctor_set(v_reuseFailAlloc_2853_, 6, v_recvIdx_2841_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, sizeof(void*)*7, v_closed_2842_);
v___x_2848_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2849_ = lean_st_ref_set(v___y_2828_, v___x_2848_);
v___x_2850_ = lean_io_promise_result_opt(v___x_2833_);
lean_dec(v___x_2833_);
v___x_2851_ = lean_unsigned_to_nat(0u);
v___x_2852_ = lean_io_bind_task(v___x_2850_, v___f_2827_, v___x_2851_, v___x_2832_);
return v___x_2852_;
}
}
}
else
{
lean_object* v___x_2855_; 
lean_dec_ref(v___f_2827_);
v___x_2855_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_2855_;
}
}
else
{
lean_object* v___x_2856_; 
lean_dec_ref(v___f_2827_);
lean_dec(v_v_2826_);
v___x_2856_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_2857_, lean_object* v___f_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(v_v_2857_, v___f_2858_, v___y_2859_);
lean_dec(v___y_2859_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(lean_object* v_ch_2862_, lean_object* v_v_2863_, lean_object* v_res_2864_){
_start:
{
if (lean_obj_tag(v_res_2864_) == 0)
{
lean_dec(v_v_2863_);
lean_dec_ref(v_ch_2862_);
goto v___jp_2866_;
}
else
{
lean_object* v_val_2868_; uint8_t v___x_2869_; 
v_val_2868_ = lean_ctor_get(v_res_2864_, 0);
v___x_2869_ = lean_unbox(v_val_2868_);
if (v___x_2869_ == 0)
{
lean_dec(v_v_2863_);
lean_dec_ref(v_ch_2862_);
goto v___jp_2866_;
}
else
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2862_, v_v_2863_);
return v___x_2870_;
}
}
v___jp_2866_:
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_2871_, lean_object* v_v_2872_, lean_object* v_res_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(v_ch_2871_, v_v_2872_, v_res_2873_);
lean_dec(v_res_2873_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(lean_object* v_ch_2876_, lean_object* v_v_2877_){
_start:
{
lean_object* v___f_2879_; lean_object* v___f_2880_; lean_object* v___x_2881_; 
lean_inc(v_v_2877_);
lean_inc_ref(v_ch_2876_);
v___f_2879_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2879_, 0, v_ch_2876_);
lean_closure_set(v___f_2879_, 1, v_v_2877_);
v___f_2880_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2880_, 0, v_v_2877_);
lean_closure_set(v___f_2880_, 1, v___f_2879_);
v___x_2881_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2876_, v___f_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(lean_object* v_ch_2882_, lean_object* v_v_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2882_, v_v_2883_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_object* v_00_u03b1_2886_, lean_object* v_ch_2887_, lean_object* v_v_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2887_, v_v_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(lean_object* v_00_u03b1_2891_, lean_object* v_ch_2892_, lean_object* v_v_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(v_00_u03b1_2891_, v_ch_2892_, v_v_2893_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t v___x_2896_, lean_object* v_as_2897_, size_t v_sz_2898_, size_t v_i_2899_, lean_object* v_b_2900_){
_start:
{
uint8_t v___x_2902_; 
v___x_2902_ = lean_usize_dec_lt(v_i_2899_, v_sz_2898_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_b_2900_);
return v___x_2903_;
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; size_t v___x_2907_; size_t v___x_2908_; 
v_a_2904_ = lean_array_uget_borrowed(v_as_2897_, v_i_2899_);
v___x_2905_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_2904_, v___x_2896_);
v___x_2906_ = lean_box(0);
v___x_2907_ = ((size_t)1ULL);
v___x_2908_ = lean_usize_add(v_i_2899_, v___x_2907_);
v_i_2899_ = v___x_2908_;
v_b_2900_ = v___x_2906_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_2910_, lean_object* v_as_2911_, lean_object* v_sz_2912_, lean_object* v_i_2913_, lean_object* v_b_2914_, lean_object* v___y_2915_){
_start:
{
uint8_t v___x_1136__boxed_2916_; size_t v_sz_boxed_2917_; size_t v_i_boxed_2918_; lean_object* v_res_2919_; 
v___x_1136__boxed_2916_ = lean_unbox(v___x_2910_);
v_sz_boxed_2917_ = lean_unbox_usize(v_sz_2912_);
lean_dec(v_sz_2912_);
v_i_boxed_2918_ = lean_unbox_usize(v_i_2913_);
lean_dec(v_i_2913_);
v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1136__boxed_2916_, v_as_2911_, v_sz_boxed_2917_, v_i_boxed_2918_, v_b_2914_);
lean_dec_ref(v_as_2911_);
return v_res_2919_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Std_Queue_empty(lean_box(0));
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; uint8_t v_closed_2924_; 
v___x_2923_ = lean_st_ref_get(v___y_2921_);
v_closed_2924_ = lean_ctor_get_uint8(v___x_2923_, sizeof(void*)*7);
if (v_closed_2924_ == 0)
{
lean_object* v_producers_2925_; lean_object* v_consumers_2926_; lean_object* v_capacity_2927_; lean_object* v_buf_2928_; lean_object* v_bufCount_2929_; lean_object* v_sendIdx_2930_; lean_object* v_recvIdx_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2954_; 
v_producers_2925_ = lean_ctor_get(v___x_2923_, 0);
v_consumers_2926_ = lean_ctor_get(v___x_2923_, 1);
v_capacity_2927_ = lean_ctor_get(v___x_2923_, 2);
v_buf_2928_ = lean_ctor_get(v___x_2923_, 3);
v_bufCount_2929_ = lean_ctor_get(v___x_2923_, 4);
v_sendIdx_2930_ = lean_ctor_get(v___x_2923_, 5);
v_recvIdx_2931_ = lean_ctor_get(v___x_2923_, 6);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2933_ = v___x_2923_;
v_isShared_2934_ = v_isSharedCheck_2954_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_recvIdx_2931_);
lean_inc(v_sendIdx_2930_);
lean_inc(v_bufCount_2929_);
lean_inc(v_buf_2928_);
lean_inc(v_capacity_2927_);
lean_inc(v_consumers_2926_);
lean_inc(v_producers_2925_);
lean_dec(v___x_2923_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2954_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; size_t v_sz_2937_; size_t v___x_2938_; lean_object* v___x_2939_; 
v___x_2935_ = l_Std_Queue_toArray___redArg(v_consumers_2926_);
v___x_2936_ = lean_box(0);
v_sz_2937_ = lean_array_size(v___x_2935_);
v___x_2938_ = ((size_t)0ULL);
v___x_2939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_2924_, v___x_2935_, v_sz_2937_, v___x_2938_, v___x_2936_);
lean_dec_ref(v___x_2935_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2952_; 
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v___x_2939_, 0);
lean_dec(v_unused_2953_);
v___x_2941_ = v___x_2939_;
v_isShared_2942_ = v_isSharedCheck_2952_;
goto v_resetjp_2940_;
}
else
{
lean_dec(v___x_2939_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2952_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; uint8_t v___x_2944_; lean_object* v___x_2946_; 
v___x_2943_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0);
v___x_2944_ = 1;
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_2943_);
v___x_2946_ = v___x_2933_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_producers_2925_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_2951_, 2, v_capacity_2927_);
lean_ctor_set(v_reuseFailAlloc_2951_, 3, v_buf_2928_);
lean_ctor_set(v_reuseFailAlloc_2951_, 4, v_bufCount_2929_);
lean_ctor_set(v_reuseFailAlloc_2951_, 5, v_sendIdx_2930_);
lean_ctor_set(v_reuseFailAlloc_2951_, 6, v_recvIdx_2931_);
v___x_2946_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
lean_ctor_set_uint8(v___x_2946_, sizeof(void*)*7, v___x_2944_);
v___x_2947_ = lean_st_ref_set(v___y_2921_, v___x_2946_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___x_2936_);
v___x_2949_ = v___x_2941_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2936_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
else
{
lean_del_object(v___x_2933_);
lean_dec(v_recvIdx_2931_);
lean_dec(v_sendIdx_2930_);
lean_dec(v_bufCount_2929_);
lean_dec_ref(v_buf_2928_);
lean_dec(v_capacity_2927_);
lean_dec_ref(v_producers_2925_);
return v___x_2939_;
}
}
}
else
{
uint8_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec(v___x_2923_);
v___x_2955_ = 1;
v___x_2956_ = lean_box(v___x_2955_);
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_2958_);
lean_dec(v___y_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_2962_){
_start:
{
lean_object* v___f_2964_; lean_object* v___x_2965_; 
v___f_2964_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_2965_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_2962_, v___f_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2966_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_2969_, lean_object* v_ch_2970_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_2973_, lean_object* v_ch_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_2973_, v_ch_2974_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_2977_, uint8_t v___x_2978_, lean_object* v_as_2979_, size_t v_sz_2980_, size_t v_i_2981_, lean_object* v_b_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_2978_, v_as_2979_, v_sz_2980_, v_i_2981_, v_b_2982_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_2986_, lean_object* v___x_2987_, lean_object* v_as_2988_, lean_object* v_sz_2989_, lean_object* v_i_2990_, lean_object* v_b_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v___x_1234__boxed_2994_; size_t v_sz_boxed_2995_; size_t v_i_boxed_2996_; lean_object* v_res_2997_; 
v___x_1234__boxed_2994_ = lean_unbox(v___x_2987_);
v_sz_boxed_2995_ = lean_unbox_usize(v_sz_2989_);
lean_dec(v_sz_2989_);
v_i_boxed_2996_ = lean_unbox_usize(v_i_2990_);
lean_dec(v_i_2990_);
v_res_2997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_2986_, v___x_1234__boxed_2994_, v_as_2988_, v_sz_boxed_2995_, v_i_boxed_2996_, v_b_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v_as_2988_);
return v_res_2997_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_2998_){
_start:
{
lean_object* v___x_3000_; uint8_t v_closed_3001_; 
v___x_3000_ = lean_st_ref_get(v___y_2998_);
v_closed_3001_ = lean_ctor_get_uint8(v___x_3000_, sizeof(void*)*7);
lean_dec(v___x_3000_);
return v_closed_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
uint8_t v_res_3004_; lean_object* v_r_3005_; 
v_res_3004_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_3002_);
lean_dec(v___y_3002_);
v_r_3005_ = lean_box(v_res_3004_);
return v_r_3005_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_3007_){
_start:
{
lean_object* v___f_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___f_3009_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_3010_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3007_, v___f_3009_);
v___x_3011_ = lean_unbox(v___x_3010_);
lean_dec(v___x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_3012_, lean_object* v_a_3013_){
_start:
{
uint8_t v_res_3014_; lean_object* v_r_3015_; 
v_res_3014_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3012_);
v_r_3015_ = lean_box(v_res_3014_);
return v_r_3015_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_3016_, lean_object* v_ch_3017_){
_start:
{
uint8_t v___x_3019_; 
v___x_3019_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3017_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_3020_, lean_object* v_ch_3021_, lean_object* v_a_3022_){
_start:
{
uint8_t v_res_3023_; lean_object* v_r_3024_; 
v_res_3023_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_3020_, v_ch_3021_);
v_r_3024_ = lean_box(v_res_3023_);
return v_r_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v_toPure_3028_; lean_object* v___x_3029_; 
v_toPure_3028_ = lean_ctor_get(v_toApplicative_3025_, 1);
lean_inc(v_toPure_3028_);
lean_dec_ref(v_toApplicative_3025_);
v___x_3029_ = lean_apply_2(v_toPure_3028_, lean_box(0), v_a_3026_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_3030_, lean_object* v_toBind_3031_, lean_object* v___f_3032_, lean_object* v_____r_3033_, lean_object* v_st_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_inc(v___y_3035_);
v___x_3036_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_3036_, 0, lean_box(0));
lean_closure_set(v___x_3036_, 1, lean_box(0));
lean_closure_set(v___x_3036_, 2, v___y_3035_);
lean_closure_set(v___x_3036_, 3, v_st_3034_);
v___x_3037_ = lean_apply_2(v_inst_3030_, lean_box(0), v___x_3036_);
v___x_3038_ = lean_apply_4(v_toBind_3031_, lean_box(0), lean_box(0), v___x_3037_, v___f_3032_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_inst_3039_, lean_object* v_toBind_3040_, lean_object* v___f_3041_, lean_object* v_____r_3042_, lean_object* v_st_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3039_, v_toBind_3040_, v___f_3041_, v_____r_3042_, v_st_3043_, v___y_3044_);
lean_dec(v___y_3044_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_3046_, lean_object* v_consumers_3047_, lean_object* v_capacity_3048_, lean_object* v_buf_3049_, lean_object* v___x_3050_, lean_object* v_sendIdx_3051_, lean_object* v___y_3052_, uint8_t v_closed_3053_, lean_object* v___f_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3057_, 0, v_snd_3046_);
lean_ctor_set(v___x_3057_, 1, v_consumers_3047_);
lean_ctor_set(v___x_3057_, 2, v_capacity_3048_);
lean_ctor_set(v___x_3057_, 3, v_buf_3049_);
lean_ctor_set(v___x_3057_, 4, v___x_3050_);
lean_ctor_set(v___x_3057_, 5, v_sendIdx_3051_);
lean_ctor_set(v___x_3057_, 6, v___y_3052_);
lean_ctor_set_uint8(v___x_3057_, sizeof(void*)*7, v_closed_3053_);
v___x_3058_ = lean_box(0);
lean_inc(v_a_3055_);
v___x_3059_ = lean_apply_3(v___f_3054_, v___x_3058_, v___x_3057_, v_a_3055_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_3060_, lean_object* v_consumers_3061_, lean_object* v_capacity_3062_, lean_object* v_buf_3063_, lean_object* v___x_3064_, lean_object* v_sendIdx_3065_, lean_object* v___y_3066_, lean_object* v_closed_3067_, lean_object* v___f_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
uint8_t v_closed_boxed_3071_; lean_object* v_res_3072_; 
v_closed_boxed_3071_ = lean_unbox(v_closed_3067_);
v_res_3072_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3060_, v_consumers_3061_, v_capacity_3062_, v_buf_3063_, v___x_3064_, v_sendIdx_3065_, v___y_3066_, v_closed_boxed_3071_, v___f_3068_, v_a_3069_, v_a_3070_);
lean_dec(v_a_3069_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3073_, lean_object* v_inst_3074_, lean_object* v_toBind_3075_, lean_object* v_bufCount_3076_, lean_object* v_producers_3077_, lean_object* v_consumers_3078_, lean_object* v_capacity_3079_, lean_object* v_buf_3080_, lean_object* v_sendIdx_3081_, uint8_t v_closed_3082_, lean_object* v_a_3083_, uint8_t v___x_3084_, lean_object* v_inst_3085_, lean_object* v_recvIdx_3086_, lean_object* v___x_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v___f_3089_; lean_object* v___f_3090_; lean_object* v___y_3092_; lean_object* v___x_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v___f_3089_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3089_, 0, v_toApplicative_3073_);
lean_closure_set(v___f_3089_, 1, v_a_3088_);
lean_inc_ref(v___f_3089_);
lean_inc(v_toBind_3075_);
lean_inc(v_inst_3074_);
v___f_3090_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3090_, 0, v_inst_3074_);
lean_closure_set(v___f_3090_, 1, v_toBind_3075_);
lean_closure_set(v___f_3090_, 2, v___f_3089_);
v___x_3108_ = lean_unsigned_to_nat(1u);
v___x_3109_ = lean_nat_add(v_recvIdx_3086_, v___x_3108_);
v___x_3110_ = lean_nat_dec_eq(v___x_3109_, v_capacity_3079_);
if (v___x_3110_ == 0)
{
lean_dec(v___x_3087_);
v___y_3092_ = v___x_3109_;
goto v___jp_3091_;
}
else
{
lean_dec(v___x_3109_);
v___y_3092_ = v___x_3087_;
goto v___jp_3091_;
}
v___jp_3091_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3093_ = lean_unsigned_to_nat(1u);
v___x_3094_ = lean_nat_sub(v_bufCount_3076_, v___x_3093_);
lean_inc(v___y_3092_);
lean_inc(v_sendIdx_3081_);
lean_inc(v___x_3094_);
lean_inc_ref(v_buf_3080_);
lean_inc(v_capacity_3079_);
lean_inc_ref(v_consumers_3078_);
lean_inc_ref(v_producers_3077_);
v___x_3095_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3095_, 0, v_producers_3077_);
lean_ctor_set(v___x_3095_, 1, v_consumers_3078_);
lean_ctor_set(v___x_3095_, 2, v_capacity_3079_);
lean_ctor_set(v___x_3095_, 3, v_buf_3080_);
lean_ctor_set(v___x_3095_, 4, v___x_3094_);
lean_ctor_set(v___x_3095_, 5, v_sendIdx_3081_);
lean_ctor_set(v___x_3095_, 6, v___y_3092_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*7, v_closed_3082_);
v___x_3096_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3077_);
if (lean_obj_tag(v___x_3096_) == 1)
{
lean_object* v_val_3097_; lean_object* v_fst_3098_; lean_object* v_snd_3099_; lean_object* v___x_3100_; lean_object* v___f_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec_ref_known(v___x_3095_, 7);
lean_dec_ref(v___f_3089_);
lean_dec(v_inst_3074_);
v_val_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_val_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v_fst_3098_ = lean_ctor_get(v_val_3097_, 0);
lean_inc(v_fst_3098_);
v_snd_3099_ = lean_ctor_get(v_val_3097_, 1);
lean_inc(v_snd_3099_);
lean_dec(v_val_3097_);
v___x_3100_ = lean_box(v_closed_3082_);
lean_inc(v_a_3083_);
v___f_3101_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3101_, 0, v_snd_3099_);
lean_closure_set(v___f_3101_, 1, v_consumers_3078_);
lean_closure_set(v___f_3101_, 2, v_capacity_3079_);
lean_closure_set(v___f_3101_, 3, v_buf_3080_);
lean_closure_set(v___f_3101_, 4, v___x_3094_);
lean_closure_set(v___f_3101_, 5, v_sendIdx_3081_);
lean_closure_set(v___f_3101_, 6, v___y_3092_);
lean_closure_set(v___f_3101_, 7, v___x_3100_);
lean_closure_set(v___f_3101_, 8, v___f_3090_);
lean_closure_set(v___f_3101_, 9, v_a_3083_);
v___x_3102_ = lean_box(v___x_3084_);
v___x_3103_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3103_, 0, lean_box(0));
lean_closure_set(v___x_3103_, 1, v___x_3102_);
lean_closure_set(v___x_3103_, 2, v_fst_3098_);
v___x_3104_ = lean_apply_2(v_inst_3085_, lean_box(0), v___x_3103_);
v___x_3105_ = lean_apply_4(v_toBind_3075_, lean_box(0), lean_box(0), v___x_3104_, v___f_3101_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_dec(v___x_3096_);
lean_dec(v___x_3094_);
lean_dec(v___y_3092_);
lean_dec_ref(v___f_3090_);
lean_dec(v_inst_3085_);
lean_dec(v_sendIdx_3081_);
lean_dec_ref(v_buf_3080_);
lean_dec(v_capacity_3079_);
lean_dec_ref(v_consumers_3078_);
v___x_3106_ = lean_box(0);
v___x_3107_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3074_, v_toBind_3075_, v___f_3089_, v___x_3106_, v___x_3095_, v_a_3083_);
return v___x_3107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3111_, lean_object* v_inst_3112_, lean_object* v_toBind_3113_, lean_object* v_bufCount_3114_, lean_object* v_producers_3115_, lean_object* v_consumers_3116_, lean_object* v_capacity_3117_, lean_object* v_buf_3118_, lean_object* v_sendIdx_3119_, lean_object* v_closed_3120_, lean_object* v_a_3121_, lean_object* v___x_3122_, lean_object* v_inst_3123_, lean_object* v_recvIdx_3124_, lean_object* v___x_3125_, lean_object* v_a_3126_){
_start:
{
uint8_t v_closed_boxed_3127_; uint8_t v___x_679__boxed_3128_; lean_object* v_res_3129_; 
v_closed_boxed_3127_ = lean_unbox(v_closed_3120_);
v___x_679__boxed_3128_ = lean_unbox(v___x_3122_);
v_res_3129_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3111_, v_inst_3112_, v_toBind_3113_, v_bufCount_3114_, v_producers_3115_, v_consumers_3116_, v_capacity_3117_, v_buf_3118_, v_sendIdx_3119_, v_closed_boxed_3127_, v_a_3121_, v___x_679__boxed_3128_, v_inst_3123_, v_recvIdx_3124_, v___x_3125_, v_a_3126_);
lean_dec(v_recvIdx_3124_);
lean_dec(v_a_3121_);
lean_dec(v_bufCount_3114_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3130_, lean_object* v_inst_3131_, lean_object* v_toBind_3132_, lean_object* v_a_3133_, lean_object* v_inst_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_producers_3136_; lean_object* v_consumers_3137_; lean_object* v_capacity_3138_; lean_object* v_buf_3139_; lean_object* v_bufCount_3140_; lean_object* v_sendIdx_3141_; lean_object* v_recvIdx_3142_; uint8_t v_closed_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v_producers_3136_ = lean_ctor_get(v_a_3135_, 0);
lean_inc_ref(v_producers_3136_);
v_consumers_3137_ = lean_ctor_get(v_a_3135_, 1);
lean_inc_ref(v_consumers_3137_);
v_capacity_3138_ = lean_ctor_get(v_a_3135_, 2);
lean_inc(v_capacity_3138_);
v_buf_3139_ = lean_ctor_get(v_a_3135_, 3);
lean_inc_ref(v_buf_3139_);
v_bufCount_3140_ = lean_ctor_get(v_a_3135_, 4);
lean_inc(v_bufCount_3140_);
v_sendIdx_3141_ = lean_ctor_get(v_a_3135_, 5);
lean_inc(v_sendIdx_3141_);
v_recvIdx_3142_ = lean_ctor_get(v_a_3135_, 6);
lean_inc(v_recvIdx_3142_);
v_closed_3143_ = lean_ctor_get_uint8(v_a_3135_, sizeof(void*)*7);
lean_dec_ref(v_a_3135_);
v___x_3144_ = lean_unsigned_to_nat(0u);
v___x_3145_ = lean_nat_dec_eq(v_bufCount_3140_, v___x_3144_);
if (v___x_3145_ == 0)
{
uint8_t v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___f_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3146_ = 1;
v___x_3147_ = lean_box(v_closed_3143_);
v___x_3148_ = lean_box(v___x_3146_);
lean_inc(v_recvIdx_3142_);
lean_inc(v_a_3133_);
lean_inc_ref(v_buf_3139_);
lean_inc(v_toBind_3132_);
lean_inc(v_inst_3131_);
v___f_3149_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3149_, 0, v_toApplicative_3130_);
lean_closure_set(v___f_3149_, 1, v_inst_3131_);
lean_closure_set(v___f_3149_, 2, v_toBind_3132_);
lean_closure_set(v___f_3149_, 3, v_bufCount_3140_);
lean_closure_set(v___f_3149_, 4, v_producers_3136_);
lean_closure_set(v___f_3149_, 5, v_consumers_3137_);
lean_closure_set(v___f_3149_, 6, v_capacity_3138_);
lean_closure_set(v___f_3149_, 7, v_buf_3139_);
lean_closure_set(v___f_3149_, 8, v_sendIdx_3141_);
lean_closure_set(v___f_3149_, 9, v___x_3147_);
lean_closure_set(v___f_3149_, 10, v_a_3133_);
lean_closure_set(v___f_3149_, 11, v___x_3148_);
lean_closure_set(v___f_3149_, 12, v_inst_3134_);
lean_closure_set(v___f_3149_, 13, v_recvIdx_3142_);
lean_closure_set(v___f_3149_, 14, v___x_3144_);
v___x_3150_ = lean_array_fget(v_buf_3139_, v_recvIdx_3142_);
lean_dec(v_recvIdx_3142_);
lean_dec_ref(v_buf_3139_);
v___x_3151_ = lean_box(0);
v___x_3152_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3152_, 0, lean_box(0));
lean_closure_set(v___x_3152_, 1, lean_box(0));
lean_closure_set(v___x_3152_, 2, v___x_3150_);
lean_closure_set(v___x_3152_, 3, v___x_3151_);
v___x_3153_ = lean_apply_2(v_inst_3131_, lean_box(0), v___x_3152_);
v___x_3154_ = lean_apply_4(v_toBind_3132_, lean_box(0), lean_box(0), v___x_3153_, v___f_3149_);
return v___x_3154_;
}
else
{
lean_object* v_toPure_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec(v_recvIdx_3142_);
lean_dec(v_sendIdx_3141_);
lean_dec(v_bufCount_3140_);
lean_dec_ref(v_buf_3139_);
lean_dec(v_capacity_3138_);
lean_dec_ref(v_consumers_3137_);
lean_dec_ref(v_producers_3136_);
lean_dec(v_inst_3134_);
lean_dec(v_toBind_3132_);
lean_dec(v_inst_3131_);
v_toPure_3155_ = lean_ctor_get(v_toApplicative_3130_, 1);
lean_inc(v_toPure_3155_);
lean_dec_ref(v_toApplicative_3130_);
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_apply_2(v_toPure_3155_, lean_box(0), v___x_3156_);
return v___x_3157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_3158_, lean_object* v_inst_3159_, lean_object* v_toBind_3160_, lean_object* v_a_3161_, lean_object* v_inst_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(v_toApplicative_3158_, v_inst_3159_, v_toBind_3160_, v_a_3161_, v_inst_3162_, v_a_3163_);
lean_dec(v_a_3161_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v_toApplicative_3169_; lean_object* v_toBind_3170_; lean_object* v___f_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_toApplicative_3169_ = lean_ctor_get(v_inst_3165_, 0);
lean_inc_ref(v_toApplicative_3169_);
v_toBind_3170_ = lean_ctor_get(v_inst_3165_, 1);
lean_inc_n(v_toBind_3170_, 2);
lean_dec_ref(v_inst_3165_);
lean_inc_n(v_a_3168_, 2);
lean_inc(v_inst_3166_);
v___f_3171_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_3171_, 0, v_toApplicative_3169_);
lean_closure_set(v___f_3171_, 1, v_inst_3166_);
lean_closure_set(v___f_3171_, 2, v_toBind_3170_);
lean_closure_set(v___f_3171_, 3, v_a_3168_);
lean_closure_set(v___f_3171_, 4, v_inst_3167_);
v___x_3172_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3172_, 0, lean_box(0));
lean_closure_set(v___x_3172_, 1, lean_box(0));
lean_closure_set(v___x_3172_, 2, v_a_3168_);
v___x_3173_ = lean_apply_2(v_inst_3166_, lean_box(0), v___x_3172_);
v___x_3174_ = lean_apply_4(v_toBind_3170_, lean_box(0), lean_box(0), v___x_3173_, v___f_3171_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3175_, v_inst_3176_, v_inst_3177_, v_a_3178_);
lean_dec(v_a_3178_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3180_, lean_object* v_00_u03b1_3181_, lean_object* v_inst_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3182_, v_inst_3183_, v_inst_3184_, v_a_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object* v_m_3187_, lean_object* v_00_u03b1_3188_, lean_object* v_inst_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(v_m_3187_, v_00_u03b1_3188_, v_inst_3189_, v_inst_3190_, v_inst_3191_, v_a_3192_);
lean_dec(v_a_3192_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3194_){
_start:
{
lean_object* v___x_3196_; lean_object* v_producers_3197_; lean_object* v_consumers_3198_; lean_object* v_capacity_3199_; lean_object* v_buf_3200_; lean_object* v_bufCount_3201_; lean_object* v_sendIdx_3202_; lean_object* v_recvIdx_3203_; uint8_t v_closed_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3236_; 
v___x_3196_ = lean_st_ref_get(v_a_3194_);
v_producers_3197_ = lean_ctor_get(v___x_3196_, 0);
v_consumers_3198_ = lean_ctor_get(v___x_3196_, 1);
v_capacity_3199_ = lean_ctor_get(v___x_3196_, 2);
v_buf_3200_ = lean_ctor_get(v___x_3196_, 3);
v_bufCount_3201_ = lean_ctor_get(v___x_3196_, 4);
v_sendIdx_3202_ = lean_ctor_get(v___x_3196_, 5);
v_recvIdx_3203_ = lean_ctor_get(v___x_3196_, 6);
v_closed_3204_ = lean_ctor_get_uint8(v___x_3196_, sizeof(void*)*7);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3206_ = v___x_3196_;
v_isShared_3207_ = v_isSharedCheck_3236_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_recvIdx_3203_);
lean_inc(v_sendIdx_3202_);
lean_inc(v_bufCount_3201_);
lean_inc(v_buf_3200_);
lean_inc(v_capacity_3199_);
lean_inc(v_consumers_3198_);
lean_inc(v_producers_3197_);
lean_dec(v___x_3196_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3236_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = lean_nat_dec_eq(v_bufCount_3201_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_st_3214_; lean_object* v___y_3215_; uint8_t v___x_3217_; lean_object* v___y_3219_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3210_ = lean_array_fget_borrowed(v_buf_3200_, v_recvIdx_3203_);
v___x_3211_ = lean_box(0);
v___x_3212_ = lean_st_ref_swap(v___x_3210_, v___x_3211_);
v___x_3217_ = 1;
v___x_3232_ = lean_unsigned_to_nat(1u);
v___x_3233_ = lean_nat_add(v_recvIdx_3203_, v___x_3232_);
lean_dec(v_recvIdx_3203_);
v___x_3234_ = lean_nat_dec_eq(v___x_3233_, v_capacity_3199_);
if (v___x_3234_ == 0)
{
v___y_3219_ = v___x_3233_;
goto v___jp_3218_;
}
else
{
lean_dec(v___x_3233_);
v___y_3219_ = v___x_3208_;
goto v___jp_3218_;
}
v___jp_3213_:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_st_ref_set(v___y_3215_, v_st_3214_);
return v___x_3212_;
}
v___jp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3220_ = lean_unsigned_to_nat(1u);
v___x_3221_ = lean_nat_sub(v_bufCount_3201_, v___x_3220_);
lean_dec(v_bufCount_3201_);
lean_inc(v___y_3219_);
lean_inc(v_sendIdx_3202_);
lean_inc(v___x_3221_);
lean_inc_ref(v_buf_3200_);
lean_inc(v_capacity_3199_);
lean_inc_ref(v_consumers_3198_);
lean_inc_ref(v_producers_3197_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 6, v___y_3219_);
lean_ctor_set(v___x_3206_, 4, v___x_3221_);
v___x_3223_ = v___x_3206_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_producers_3197_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_consumers_3198_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_capacity_3199_);
lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_buf_3200_);
lean_ctor_set(v_reuseFailAlloc_3231_, 4, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3231_, 5, v_sendIdx_3202_);
lean_ctor_set(v_reuseFailAlloc_3231_, 6, v___y_3219_);
lean_ctor_set_uint8(v_reuseFailAlloc_3231_, sizeof(void*)*7, v_closed_3204_);
v___x_3223_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3197_);
if (lean_obj_tag(v___x_3224_) == 1)
{
lean_object* v_val_3225_; lean_object* v_fst_3226_; lean_object* v_snd_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_dec_ref(v___x_3223_);
v_val_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_val_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v_fst_3226_ = lean_ctor_get(v_val_3225_, 0);
lean_inc(v_fst_3226_);
v_snd_3227_ = lean_ctor_get(v_val_3225_, 1);
lean_inc(v_snd_3227_);
lean_dec(v_val_3225_);
v___x_3228_ = lean_box(v___x_3217_);
v___x_3229_ = lean_io_promise_resolve(v___x_3228_, v_fst_3226_);
lean_dec(v_fst_3226_);
v___x_3230_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3230_, 0, v_snd_3227_);
lean_ctor_set(v___x_3230_, 1, v_consumers_3198_);
lean_ctor_set(v___x_3230_, 2, v_capacity_3199_);
lean_ctor_set(v___x_3230_, 3, v_buf_3200_);
lean_ctor_set(v___x_3230_, 4, v___x_3221_);
lean_ctor_set(v___x_3230_, 5, v_sendIdx_3202_);
lean_ctor_set(v___x_3230_, 6, v___y_3219_);
lean_ctor_set_uint8(v___x_3230_, sizeof(void*)*7, v_closed_3204_);
v_st_3214_ = v___x_3230_;
v___y_3215_ = v_a_3194_;
goto v___jp_3213_;
}
else
{
lean_dec(v___x_3224_);
lean_dec(v___x_3221_);
lean_dec(v___y_3219_);
lean_dec(v_sendIdx_3202_);
lean_dec_ref(v_buf_3200_);
lean_dec(v_capacity_3199_);
lean_dec_ref(v_consumers_3198_);
v_st_3214_ = v___x_3223_;
v___y_3215_ = v_a_3194_;
goto v___jp_3213_;
}
}
}
}
else
{
lean_object* v___x_3235_; 
lean_del_object(v___x_3206_);
lean_dec(v_recvIdx_3203_);
lean_dec(v_sendIdx_3202_);
lean_dec(v_bufCount_3201_);
lean_dec_ref(v_buf_3200_);
lean_dec(v_capacity_3199_);
lean_dec_ref(v_consumers_3198_);
lean_dec_ref(v_producers_3197_);
v___x_3235_ = lean_box(0);
return v___x_3235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3237_);
lean_dec(v_a_3237_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3241_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3244_, lean_object* v_a_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3244_, v_a_3245_);
lean_dec(v_a_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3249_){
_start:
{
lean_object* v___f_3251_; lean_object* v___x_3252_; 
v___f_3251_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3252_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3249_, v___f_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3256_, lean_object* v_ch_3257_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3260_, lean_object* v_ch_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3260_, v_ch_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3265_);
if (lean_obj_tag(v___x_3267_) == 1)
{
lean_object* v___x_3268_; 
lean_dec_ref(v___f_3264_);
v___x_3268_ = lean_task_pure(v___x_3267_);
return v___x_3268_;
}
else
{
lean_object* v___x_3269_; uint8_t v_closed_3270_; 
lean_dec(v___x_3267_);
v___x_3269_ = lean_st_ref_get(v___y_3265_);
v_closed_3270_ = lean_ctor_get_uint8(v___x_3269_, sizeof(void*)*7);
lean_dec(v___x_3269_);
if (v_closed_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v_producers_3273_; lean_object* v_consumers_3274_; lean_object* v_capacity_3275_; lean_object* v_buf_3276_; lean_object* v_bufCount_3277_; lean_object* v_sendIdx_3278_; lean_object* v_recvIdx_3279_; uint8_t v_closed_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3294_; 
v___x_3271_ = lean_io_promise_new();
v___x_3272_ = lean_st_ref_take(v___y_3265_);
v_producers_3273_ = lean_ctor_get(v___x_3272_, 0);
v_consumers_3274_ = lean_ctor_get(v___x_3272_, 1);
v_capacity_3275_ = lean_ctor_get(v___x_3272_, 2);
v_buf_3276_ = lean_ctor_get(v___x_3272_, 3);
v_bufCount_3277_ = lean_ctor_get(v___x_3272_, 4);
v_sendIdx_3278_ = lean_ctor_get(v___x_3272_, 5);
v_recvIdx_3279_ = lean_ctor_get(v___x_3272_, 6);
v_closed_3280_ = lean_ctor_get_uint8(v___x_3272_, sizeof(void*)*7);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3282_ = v___x_3272_;
v_isShared_3283_ = v_isSharedCheck_3294_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_recvIdx_3279_);
lean_inc(v_sendIdx_3278_);
lean_inc(v_bufCount_3277_);
lean_inc(v_buf_3276_);
lean_inc(v_capacity_3275_);
lean_inc(v_consumers_3274_);
lean_inc(v_producers_3273_);
lean_dec(v___x_3272_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3294_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3284_ = lean_box(0);
lean_inc(v___x_3271_);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3271_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = l_Std_Queue_enqueue___redArg(v___x_3285_, v_consumers_3274_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 1, v___x_3286_);
v___x_3288_ = v___x_3282_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_producers_3273_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3293_, 2, v_capacity_3275_);
lean_ctor_set(v_reuseFailAlloc_3293_, 3, v_buf_3276_);
lean_ctor_set(v_reuseFailAlloc_3293_, 4, v_bufCount_3277_);
lean_ctor_set(v_reuseFailAlloc_3293_, 5, v_sendIdx_3278_);
lean_ctor_set(v_reuseFailAlloc_3293_, 6, v_recvIdx_3279_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, sizeof(void*)*7, v_closed_3280_);
v___x_3288_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3289_ = lean_st_ref_set(v___y_3265_, v___x_3288_);
v___x_3290_ = lean_io_promise_result_opt(v___x_3271_);
lean_dec(v___x_3271_);
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = lean_io_bind_task(v___x_3290_, v___f_3264_, v___x_3291_, v_closed_3270_);
return v___x_3292_;
}
}
}
else
{
lean_object* v___x_3295_; 
lean_dec_ref(v___f_3264_);
v___x_3295_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3296_, v___y_3297_);
lean_dec(v___y_3297_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3300_, lean_object* v_res_3301_){
_start:
{
if (lean_obj_tag(v_res_3301_) == 0)
{
lean_dec_ref(v_ch_3300_);
goto v___jp_3303_;
}
else
{
lean_object* v_val_3305_; uint8_t v___x_3306_; 
v_val_3305_ = lean_ctor_get(v_res_3301_, 0);
v___x_3306_ = lean_unbox(v_val_3305_);
if (v___x_3306_ == 0)
{
lean_dec_ref(v_ch_3300_);
goto v___jp_3303_;
}
else
{
lean_object* v___x_3307_; 
v___x_3307_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3300_);
return v___x_3307_;
}
}
v___jp_3303_:
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3308_, lean_object* v_res_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3308_, v_res_3309_);
lean_dec(v_res_3309_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3312_){
_start:
{
lean_object* v___f_3314_; lean_object* v___f_3315_; lean_object* v___x_3316_; 
lean_inc_ref(v_ch_3312_);
v___f_3314_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3314_, 0, v_ch_3312_);
v___f_3315_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3315_, 0, v___f_3314_);
v___x_3316_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3312_, v___f_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3317_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3320_, lean_object* v_ch_3321_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3324_, lean_object* v_ch_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3324_, v_ch_3325_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3328_, lean_object* v_a_3329_){
_start:
{
uint8_t v___y_3331_; lean_object* v_bufCount_3335_; uint8_t v_closed_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_bufCount_3335_ = lean_ctor_get(v_a_3329_, 4);
v_closed_3336_ = lean_ctor_get_uint8(v_a_3329_, sizeof(void*)*7);
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = lean_nat_dec_eq(v_bufCount_3335_, v___x_3337_);
if (v___x_3338_ == 0)
{
uint8_t v___x_3339_; 
v___x_3339_ = 1;
v___y_3331_ = v___x_3339_;
goto v___jp_3330_;
}
else
{
v___y_3331_ = v_closed_3336_;
goto v___jp_3330_;
}
v___jp_3330_:
{
lean_object* v_toPure_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_toPure_3332_ = lean_ctor_get(v_toApplicative_3328_, 1);
lean_inc(v_toPure_3332_);
lean_dec_ref(v_toApplicative_3328_);
v___x_3333_ = lean_box(v___y_3331_);
v___x_3334_ = lean_apply_2(v_toPure_3332_, lean_box(0), v___x_3333_);
return v___x_3334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3340_, v_a_3341_);
lean_dec_ref(v_a_3341_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3343_, lean_object* v_inst_3344_, lean_object* v_a_3345_){
_start:
{
lean_object* v_toApplicative_3346_; lean_object* v_toBind_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v_toApplicative_3346_ = lean_ctor_get(v_inst_3343_, 0);
lean_inc_ref(v_toApplicative_3346_);
v_toBind_3347_ = lean_ctor_get(v_inst_3343_, 1);
lean_inc(v_toBind_3347_);
lean_dec_ref(v_inst_3343_);
v___f_3348_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3348_, 0, v_toApplicative_3346_);
lean_inc(v_a_3345_);
v___x_3349_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3349_, 0, lean_box(0));
lean_closure_set(v___x_3349_, 1, lean_box(0));
lean_closure_set(v___x_3349_, 2, v_a_3345_);
v___x_3350_ = lean_apply_2(v_inst_3344_, lean_box(0), v___x_3349_);
v___x_3351_ = lean_apply_4(v_toBind_3347_, lean_box(0), lean_box(0), v___x_3350_, v___f_3348_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object* v_inst_3352_, lean_object* v_inst_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(v_inst_3352_, v_inst_3353_, v_a_3354_);
lean_dec(v_a_3354_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3356_, lean_object* v_00_u03b1_3357_, lean_object* v_inst_3358_, lean_object* v_inst_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v_toApplicative_3361_; lean_object* v_toBind_3362_; lean_object* v___f_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_toApplicative_3361_ = lean_ctor_get(v_inst_3358_, 0);
lean_inc_ref(v_toApplicative_3361_);
v_toBind_3362_ = lean_ctor_get(v_inst_3358_, 1);
lean_inc(v_toBind_3362_);
lean_dec_ref(v_inst_3358_);
v___f_3363_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3363_, 0, v_toApplicative_3361_);
lean_inc(v_a_3360_);
v___x_3364_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3364_, 0, lean_box(0));
lean_closure_set(v___x_3364_, 1, lean_box(0));
lean_closure_set(v___x_3364_, 2, v_a_3360_);
v___x_3365_ = lean_apply_2(v_inst_3359_, lean_box(0), v___x_3364_);
v___x_3366_ = lean_apply_4(v_toBind_3362_, lean_box(0), lean_box(0), v___x_3365_, v___f_3363_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object* v_m_3367_, lean_object* v_00_u03b1_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(v_m_3367_, v_00_u03b1_3368_, v_inst_3369_, v_inst_3370_, v_a_3371_);
lean_dec(v_a_3371_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3373_){
_start:
{
lean_object* v___x_3375_; lean_object* v_producers_3376_; lean_object* v_consumers_3377_; lean_object* v_capacity_3378_; lean_object* v_buf_3379_; lean_object* v_bufCount_3380_; lean_object* v_sendIdx_3381_; lean_object* v_recvIdx_3382_; uint8_t v_closed_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3417_; 
v___x_3375_ = lean_st_ref_get(v_a_3373_);
v_producers_3376_ = lean_ctor_get(v___x_3375_, 0);
v_consumers_3377_ = lean_ctor_get(v___x_3375_, 1);
v_capacity_3378_ = lean_ctor_get(v___x_3375_, 2);
v_buf_3379_ = lean_ctor_get(v___x_3375_, 3);
v_bufCount_3380_ = lean_ctor_get(v___x_3375_, 4);
v_sendIdx_3381_ = lean_ctor_get(v___x_3375_, 5);
v_recvIdx_3382_ = lean_ctor_get(v___x_3375_, 6);
v_closed_3383_ = lean_ctor_get_uint8(v___x_3375_, sizeof(void*)*7);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3385_ = v___x_3375_;
v_isShared_3386_ = v_isSharedCheck_3417_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_recvIdx_3382_);
lean_inc(v_sendIdx_3381_);
lean_inc(v_bufCount_3380_);
lean_inc(v_buf_3379_);
lean_inc(v_capacity_3378_);
lean_inc(v_consumers_3377_);
lean_inc(v_producers_3376_);
lean_dec(v___x_3375_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3417_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = lean_unsigned_to_nat(0u);
v___x_3388_ = lean_nat_dec_eq(v_bufCount_3380_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v_st_3393_; lean_object* v___y_3394_; uint8_t v___x_3397_; lean_object* v___y_3399_; lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3389_ = lean_array_fget_borrowed(v_buf_3379_, v_recvIdx_3382_);
v___x_3390_ = lean_box(0);
v___x_3391_ = lean_st_ref_swap(v___x_3389_, v___x_3390_);
v___x_3397_ = 1;
v___x_3412_ = lean_unsigned_to_nat(1u);
v___x_3413_ = lean_nat_add(v_recvIdx_3382_, v___x_3412_);
lean_dec(v_recvIdx_3382_);
v___x_3414_ = lean_nat_dec_eq(v___x_3413_, v_capacity_3378_);
if (v___x_3414_ == 0)
{
v___y_3399_ = v___x_3413_;
goto v___jp_3398_;
}
else
{
lean_dec(v___x_3413_);
v___y_3399_ = v___x_3387_;
goto v___jp_3398_;
}
v___jp_3392_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = lean_st_ref_set(v___y_3394_, v_st_3393_);
v___x_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3391_);
return v___x_3396_;
}
v___jp_3398_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3400_ = lean_unsigned_to_nat(1u);
v___x_3401_ = lean_nat_sub(v_bufCount_3380_, v___x_3400_);
lean_dec(v_bufCount_3380_);
lean_inc(v___y_3399_);
lean_inc(v_sendIdx_3381_);
lean_inc(v___x_3401_);
lean_inc_ref(v_buf_3379_);
lean_inc(v_capacity_3378_);
lean_inc_ref(v_consumers_3377_);
lean_inc_ref(v_producers_3376_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 6, v___y_3399_);
lean_ctor_set(v___x_3385_, 4, v___x_3401_);
v___x_3403_ = v___x_3385_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_producers_3376_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_consumers_3377_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_capacity_3378_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v_buf_3379_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3411_, 5, v_sendIdx_3381_);
lean_ctor_set(v_reuseFailAlloc_3411_, 6, v___y_3399_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, sizeof(void*)*7, v_closed_3383_);
v___x_3403_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3376_);
if (lean_obj_tag(v___x_3404_) == 1)
{
lean_object* v_val_3405_; lean_object* v_fst_3406_; lean_object* v_snd_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_dec_ref(v___x_3403_);
v_val_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v___x_3404_, 1);
v_fst_3406_ = lean_ctor_get(v_val_3405_, 0);
lean_inc(v_fst_3406_);
v_snd_3407_ = lean_ctor_get(v_val_3405_, 1);
lean_inc(v_snd_3407_);
lean_dec(v_val_3405_);
v___x_3408_ = lean_box(v___x_3397_);
v___x_3409_ = lean_io_promise_resolve(v___x_3408_, v_fst_3406_);
lean_dec(v_fst_3406_);
v___x_3410_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3410_, 0, v_snd_3407_);
lean_ctor_set(v___x_3410_, 1, v_consumers_3377_);
lean_ctor_set(v___x_3410_, 2, v_capacity_3378_);
lean_ctor_set(v___x_3410_, 3, v_buf_3379_);
lean_ctor_set(v___x_3410_, 4, v___x_3401_);
lean_ctor_set(v___x_3410_, 5, v_sendIdx_3381_);
lean_ctor_set(v___x_3410_, 6, v___y_3399_);
lean_ctor_set_uint8(v___x_3410_, sizeof(void*)*7, v_closed_3383_);
v_st_3393_ = v___x_3410_;
v___y_3394_ = v_a_3373_;
goto v___jp_3392_;
}
else
{
lean_dec(v___x_3404_);
lean_dec(v___x_3401_);
lean_dec(v___y_3399_);
lean_dec(v_sendIdx_3381_);
lean_dec_ref(v_buf_3379_);
lean_dec(v_capacity_3378_);
lean_dec_ref(v_consumers_3377_);
v_st_3393_ = v___x_3403_;
v___y_3394_ = v_a_3373_;
goto v___jp_3392_;
}
}
}
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_del_object(v___x_3385_);
lean_dec(v_recvIdx_3382_);
lean_dec(v_sendIdx_3381_);
lean_dec(v_bufCount_3380_);
lean_dec_ref(v_buf_3379_);
lean_dec(v_capacity_3378_);
lean_dec_ref(v_consumers_3377_);
lean_dec_ref(v_producers_3376_);
v___x_3415_ = lean_box(0);
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
return v___x_3416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3418_);
lean_dec(v_a_3418_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3421_, lean_object* v_a_3422_){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3422_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3425_, lean_object* v_a_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3425_, v_a_3426_);
lean_dec(v_a_3426_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3429_, lean_object* v_lose_3430_){
_start:
{
lean_object* v_finished_3432_; lean_object* v_promise_3433_; lean_object* v___x_3434_; uint8_t v___y_3436_; uint8_t v___x_3444_; 
v_finished_3432_ = lean_ctor_get(v_w_3429_, 0);
v_promise_3433_ = lean_ctor_get(v_w_3429_, 1);
v___x_3434_ = lean_st_ref_take(v_finished_3432_);
v___x_3444_ = lean_unbox(v___x_3434_);
lean_dec(v___x_3434_);
if (v___x_3444_ == 0)
{
uint8_t v___x_3445_; 
v___x_3445_ = 1;
v___y_3436_ = v___x_3445_;
goto v___jp_3435_;
}
else
{
uint8_t v___x_3446_; 
v___x_3446_ = 0;
v___y_3436_ = v___x_3446_;
goto v___jp_3435_;
}
v___jp_3435_:
{
uint8_t v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = 1;
v___x_3438_ = lean_box(v___x_3437_);
v___x_3439_ = lean_st_ref_set(v_finished_3432_, v___x_3438_);
if (v___y_3436_ == 0)
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_apply_1(v_lose_3430_, lean_box(0));
return v___x_3440_;
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec_ref(v_lose_3430_);
v___x_3441_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0));
v___x_3442_ = lean_io_promise_resolve(v___x_3441_, v_promise_3433_);
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3447_, lean_object* v_lose_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3447_, v_lose_3448_);
lean_dec_ref(v_w_3447_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3451_, lean_object* v_w_3452_, lean_object* v_lose_3453_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3452_, v_lose_3453_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3456_, lean_object* v_w_3457_, lean_object* v_lose_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3456_, v_w_3457_, v_lose_3458_);
lean_dec_ref(v_w_3457_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3461_, lean_object* v_lose_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_finished_3465_; lean_object* v_promise_3466_; lean_object* v___x_3467_; uint8_t v___y_3469_; uint8_t v___x_3485_; 
v_finished_3465_ = lean_ctor_get(v_w_3461_, 0);
v_promise_3466_ = lean_ctor_get(v_w_3461_, 1);
v___x_3467_ = lean_st_ref_take(v_finished_3465_);
v___x_3485_ = lean_unbox(v___x_3467_);
lean_dec(v___x_3467_);
if (v___x_3485_ == 0)
{
uint8_t v___x_3486_; 
v___x_3486_ = 1;
v___y_3469_ = v___x_3486_;
goto v___jp_3468_;
}
else
{
uint8_t v___x_3487_; 
v___x_3487_ = 0;
v___y_3469_ = v___x_3487_;
goto v___jp_3468_;
}
v___jp_3468_:
{
uint8_t v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = 1;
v___x_3471_ = lean_box(v___x_3470_);
v___x_3472_ = lean_st_ref_set(v_finished_3465_, v___x_3471_);
if (v___y_3469_ == 0)
{
lean_object* v___x_3473_; 
lean_inc(v___y_3463_);
v___x_3473_ = lean_apply_2(v_lose_3462_, v___y_3463_, lean_box(0));
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3484_; 
lean_dec_ref(v_lose_3462_);
v___x_3474_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3463_);
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3484_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3484_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3479_, 0, v_a_3475_);
v___x_3480_ = lean_io_promise_resolve(v___x_3479_, v_promise_3466_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3480_);
v___x_3482_ = v___x_3477_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3488_, lean_object* v_lose_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3488_, v_lose_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v_w_3488_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3493_, lean_object* v_w_3494_, lean_object* v_lose_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3494_, v_lose_3495_, v___y_3496_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3499_, lean_object* v_w_3500_, lean_object* v_lose_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3499_, v_w_3500_, v_lose_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v_w_3500_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3505_, lean_object* v_k_3506_){
_start:
{
lean_object* v_ref_3508_; lean_object* v_mutex_3509_; lean_object* v___x_3510_; lean_object* v_r_3511_; 
v_ref_3508_ = lean_ctor_get(v_mutex_3505_, 0);
lean_inc(v_ref_3508_);
v_mutex_3509_ = lean_ctor_get(v_mutex_3505_, 1);
lean_inc(v_mutex_3509_);
lean_dec_ref(v_mutex_3505_);
v___x_3510_ = lean_io_basemutex_lock(v_mutex_3509_);
v_r_3511_ = lean_apply_2(v_k_3506_, v_ref_3508_, lean_box(0));
if (lean_obj_tag(v_r_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3520_; 
v_a_3512_ = lean_ctor_get(v_r_3511_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_r_3511_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3514_ = v_r_3511_;
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v_r_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3516_ = lean_io_basemutex_unlock(v_mutex_3509_);
lean_dec(v_mutex_3509_);
if (v_isShared_3515_ == 0)
{
v___x_3518_ = v___x_3514_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3512_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3529_; 
v_a_3521_ = lean_ctor_get(v_r_3511_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_r_3511_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3523_ = v_r_3511_;
v_isShared_3524_ = v_isSharedCheck_3529_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v_r_3511_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3529_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3525_ = lean_io_basemutex_unlock(v_mutex_3509_);
lean_dec(v_mutex_3509_);
if (v_isShared_3524_ == 0)
{
v___x_3527_ = v___x_3523_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3521_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3530_, lean_object* v_k_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3530_, v_k_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3534_, lean_object* v_00_u03b2_3535_, lean_object* v_mutex_3536_, lean_object* v_k_3537_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3536_, v_k_3537_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3540_, lean_object* v_00_u03b2_3541_, lean_object* v_mutex_3542_, lean_object* v_k_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3540_, v_00_u03b2_3541_, v_mutex_3542_, v_k_3543_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3549_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v___x_3555_; lean_object* v_producers_3556_; lean_object* v_consumers_3557_; lean_object* v_capacity_3558_; lean_object* v_buf_3559_; lean_object* v_bufCount_3560_; lean_object* v_sendIdx_3561_; lean_object* v_recvIdx_3562_; uint8_t v_closed_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3585_; 
v___x_3555_ = lean_st_ref_get(v___y_3553_);
v_producers_3556_ = lean_ctor_get(v___x_3555_, 0);
v_consumers_3557_ = lean_ctor_get(v___x_3555_, 1);
v_capacity_3558_ = lean_ctor_get(v___x_3555_, 2);
v_buf_3559_ = lean_ctor_get(v___x_3555_, 3);
v_bufCount_3560_ = lean_ctor_get(v___x_3555_, 4);
v_sendIdx_3561_ = lean_ctor_get(v___x_3555_, 5);
v_recvIdx_3562_ = lean_ctor_get(v___x_3555_, 6);
v_closed_3563_ = lean_ctor_get_uint8(v___x_3555_, sizeof(void*)*7);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3565_ = v___x_3555_;
v_isShared_3566_ = v_isSharedCheck_3585_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_recvIdx_3562_);
lean_inc(v_sendIdx_3561_);
lean_inc(v_bufCount_3560_);
lean_inc(v_buf_3559_);
lean_inc(v_capacity_3558_);
lean_inc(v_consumers_3557_);
lean_inc(v_producers_3556_);
lean_dec(v___x_3555_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3585_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3557_);
if (lean_obj_tag(v___x_3567_) == 1)
{
lean_object* v_val_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3582_; 
v_val_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3582_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_val_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3582_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v_fst_3572_; lean_object* v_snd_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
v_fst_3572_ = lean_ctor_get(v_val_3568_, 0);
lean_inc(v_fst_3572_);
v_snd_3573_ = lean_ctor_get(v_val_3568_, 1);
lean_inc(v_snd_3573_);
lean_dec(v_val_3568_);
v___x_3574_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3572_, v_____do__lift_3552_);
lean_dec(v_fst_3572_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 1, v_snd_3573_);
v___x_3576_ = v___x_3565_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_producers_3556_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_snd_3573_);
lean_ctor_set(v_reuseFailAlloc_3581_, 2, v_capacity_3558_);
lean_ctor_set(v_reuseFailAlloc_3581_, 3, v_buf_3559_);
lean_ctor_set(v_reuseFailAlloc_3581_, 4, v_bufCount_3560_);
lean_ctor_set(v_reuseFailAlloc_3581_, 5, v_sendIdx_3561_);
lean_ctor_set(v_reuseFailAlloc_3581_, 6, v_recvIdx_3562_);
lean_ctor_set_uint8(v_reuseFailAlloc_3581_, sizeof(void*)*7, v_closed_3563_);
v___x_3576_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3577_ = lean_st_ref_set(v___y_3553_, v___x_3576_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set_tag(v___x_3570_, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3577_);
v___x_3579_ = v___x_3570_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec(v___x_3567_);
lean_del_object(v___x_3565_);
lean_dec(v_recvIdx_3562_);
lean_dec(v_sendIdx_3561_);
lean_dec(v_bufCount_3560_);
lean_dec_ref(v_buf_3559_);
lean_dec(v_capacity_3558_);
lean_dec_ref(v_producers_3556_);
v___x_3583_ = lean_box(0);
v___x_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
return v___x_3584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
uint8_t v_____do__lift_3921__boxed_3589_; lean_object* v_res_3590_; 
v_____do__lift_3921__boxed_3589_ = lean_unbox(v_____do__lift_3586_);
v_res_3590_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3921__boxed_3589_, v___y_3587_);
lean_dec(v___y_3587_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3591_, lean_object* v___f_3592_, uint8_t v_____do__lift_3593_, lean_object* v___y_3594_){
_start:
{
if (v_____do__lift_3593_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v_producers_3598_; lean_object* v_consumers_3599_; lean_object* v_capacity_3600_; lean_object* v_buf_3601_; lean_object* v_bufCount_3602_; lean_object* v_sendIdx_3603_; lean_object* v_recvIdx_3604_; uint8_t v_closed_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3619_; 
v___x_3596_ = lean_io_promise_new();
v___x_3597_ = lean_st_ref_take(v___y_3594_);
v_producers_3598_ = lean_ctor_get(v___x_3597_, 0);
v_consumers_3599_ = lean_ctor_get(v___x_3597_, 1);
v_capacity_3600_ = lean_ctor_get(v___x_3597_, 2);
v_buf_3601_ = lean_ctor_get(v___x_3597_, 3);
v_bufCount_3602_ = lean_ctor_get(v___x_3597_, 4);
v_sendIdx_3603_ = lean_ctor_get(v___x_3597_, 5);
v_recvIdx_3604_ = lean_ctor_get(v___x_3597_, 6);
v_closed_3605_ = lean_ctor_get_uint8(v___x_3597_, sizeof(void*)*7);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3607_ = v___x_3597_;
v_isShared_3608_ = v_isSharedCheck_3619_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_recvIdx_3604_);
lean_inc(v_sendIdx_3603_);
lean_inc(v_bufCount_3602_);
lean_inc(v_buf_3601_);
lean_inc(v_capacity_3600_);
lean_inc(v_consumers_3599_);
lean_inc(v_producers_3598_);
lean_dec(v___x_3597_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3619_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_waiter_3591_);
lean_inc(v___x_3596_);
v___x_3610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3596_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = l_Std_Queue_enqueue___redArg(v___x_3610_, v_consumers_3599_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 1, v___x_3611_);
v___x_3613_ = v___x_3607_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_producers_3598_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_capacity_3600_);
lean_ctor_set(v_reuseFailAlloc_3618_, 3, v_buf_3601_);
lean_ctor_set(v_reuseFailAlloc_3618_, 4, v_bufCount_3602_);
lean_ctor_set(v_reuseFailAlloc_3618_, 5, v_sendIdx_3603_);
lean_ctor_set(v_reuseFailAlloc_3618_, 6, v_recvIdx_3604_);
lean_ctor_set_uint8(v_reuseFailAlloc_3618_, sizeof(void*)*7, v_closed_3605_);
v___x_3613_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3614_ = lean_st_ref_set(v___y_3594_, v___x_3613_);
v___x_3615_ = lean_io_promise_result_opt(v___x_3596_);
lean_dec(v___x_3596_);
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = l_EIO_chainTask___redArg(v___x_3615_, v___f_3592_, v___x_3616_, v_____do__lift_3593_);
return v___x_3617_;
}
}
}
else
{
lean_object* v___x_3620_; lean_object* v_lose_3621_; lean_object* v___x_3622_; 
lean_dec_ref(v___f_3592_);
v___x_3620_ = lean_box(v_____do__lift_3593_);
v_lose_3621_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3621_, 0, v___x_3620_);
v___x_3622_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3591_, v_lose_3621_, v___y_3594_);
lean_dec_ref(v_waiter_3591_);
return v___x_3622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3623_, lean_object* v___f_3624_, lean_object* v_____do__lift_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
uint8_t v_____do__lift_3977__boxed_3628_; lean_object* v_res_3629_; 
v_____do__lift_3977__boxed_3628_ = lean_unbox(v_____do__lift_3625_);
v_res_3629_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3623_, v___f_3624_, v_____do__lift_3977__boxed_3628_, v___y_3626_);
lean_dec(v___y_3626_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; lean_object* v_bufCount_3634_; uint8_t v_closed_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3633_ = lean_st_ref_get(v___y_3631_);
v_bufCount_3634_ = lean_ctor_get(v___x_3633_, 4);
lean_inc(v_bufCount_3634_);
v_closed_3635_ = lean_ctor_get_uint8(v___x_3633_, sizeof(void*)*7);
lean_dec(v___x_3633_);
v___x_3636_ = lean_unsigned_to_nat(0u);
v___x_3637_ = lean_nat_dec_eq(v_bufCount_3634_, v___x_3636_);
lean_dec(v_bufCount_3634_);
if (v___x_3637_ == 0)
{
uint8_t v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3638_ = 1;
v___x_3639_ = lean_box(v___x_3638_);
lean_inc(v___y_3631_);
v___x_3640_ = lean_apply_3(v___f_3630_, v___x_3639_, v___y_3631_, lean_box(0));
return v___x_3640_;
}
else
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_box(v_closed_3635_);
lean_inc(v___y_3631_);
v___x_3642_ = lean_apply_3(v___f_3630_, v___x_3641_, v___y_3631_, lean_box(0));
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3643_, v___y_3644_);
lean_dec(v___y_3644_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3649_, lean_object* v_ch_3650_, lean_object* v_x_3651_){
_start:
{
if (lean_obj_tag(v_x_3651_) == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_dec_ref(v_ch_3650_);
lean_dec_ref(v_waiter_3649_);
v___x_3653_ = lean_box(0);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
else
{
lean_object* v_val_3655_; uint8_t v___x_3656_; 
v_val_3655_ = lean_ctor_get(v_x_3651_, 0);
v___x_3656_ = lean_unbox(v_val_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___f_3657_; lean_object* v___x_3658_; 
lean_dec_ref(v_ch_3650_);
v___f_3657_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3658_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3649_, v___f_3657_);
lean_dec_ref(v_waiter_3649_);
return v___x_3658_;
}
else
{
lean_object* v___x_3659_; 
v___x_3659_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3650_, v_waiter_3649_);
return v___x_3659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3660_, lean_object* v_ch_3661_, lean_object* v_x_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3660_, v_ch_3661_, v_x_3662_);
lean_dec(v_x_3662_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3665_, lean_object* v_waiter_3666_){
_start:
{
lean_object* v___f_3668_; lean_object* v___f_3669_; lean_object* v___f_3670_; lean_object* v___x_3671_; 
lean_inc_ref(v_ch_3665_);
lean_inc_ref(v_waiter_3666_);
v___f_3668_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3668_, 0, v_waiter_3666_);
lean_closure_set(v___f_3668_, 1, v_ch_3665_);
v___f_3669_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3669_, 0, v_waiter_3666_);
lean_closure_set(v___f_3669_, 1, v___f_3668_);
v___f_3670_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3670_, 0, v___f_3669_);
v___x_3671_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3665_, v___f_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3672_, lean_object* v_waiter_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3672_, v_waiter_3673_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3676_, lean_object* v_ch_3677_, lean_object* v_waiter_3678_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3677_, v_waiter_3678_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3681_, lean_object* v_ch_3682_, lean_object* v_waiter_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3681_, v_ch_3682_, v_waiter_3683_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3686_, lean_object* v_x_3687_){
_start:
{
if (lean_obj_tag(v_x_3687_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3697_; 
lean_dec_ref(v_x_3686_);
v_a_3689_ = lean_ctor_get(v_x_3687_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_x_3687_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3691_ = v_x_3687_;
v_isShared_3692_ = v_isSharedCheck_3697_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v_x_3687_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3697_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; 
v___x_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
return v___x_3695_;
}
}
}
else
{
lean_object* v___x_3698_; 
lean_dec_ref_known(v_x_3687_, 1);
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v_x_3686_);
return v___x_3698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3699_, lean_object* v_x_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3699_, v_x_3700_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3703_, uint8_t v___x_3704_, lean_object* v___f_3705_, lean_object* v_____r_3706_, lean_object* v_st_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3710_ = lean_st_ref_set(v___y_3708_, v_st_3707_);
v___x_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
v___x_3713_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3703_, v___x_3704_, v___x_3712_, v___f_3705_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3714_, lean_object* v___x_3715_, lean_object* v___f_3716_, lean_object* v_____r_3717_, lean_object* v_st_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
uint8_t v___x_6388__boxed_3721_; lean_object* v_res_3722_; 
v___x_6388__boxed_3721_ = lean_unbox(v___x_3715_);
v_res_3722_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3714_, v___x_6388__boxed_3721_, v___f_3716_, v_____r_3717_, v_st_3718_, v___y_3719_);
lean_dec(v___y_3719_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3723_, lean_object* v_consumers_3724_, lean_object* v_capacity_3725_, lean_object* v_buf_3726_, lean_object* v___x_3727_, lean_object* v_sendIdx_3728_, lean_object* v___y_3729_, uint8_t v_closed_3730_, lean_object* v___f_3731_, lean_object* v_a_3732_, lean_object* v_x_3733_){
_start:
{
if (lean_obj_tag(v_x_3733_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3743_; 
lean_dec_ref(v___f_3731_);
lean_dec(v___y_3729_);
lean_dec(v_sendIdx_3728_);
lean_dec(v___x_3727_);
lean_dec_ref(v_buf_3726_);
lean_dec(v_capacity_3725_);
lean_dec_ref(v_consumers_3724_);
lean_dec_ref(v_snd_3723_);
v_a_3735_ = lean_ctor_get(v_x_3733_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_x_3733_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3737_ = v_x_3733_;
v_isShared_3738_ = v_isSharedCheck_3743_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v_x_3733_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3743_;
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
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
return v___x_3741_;
}
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec_ref_known(v_x_3733_, 1);
v___x_3744_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3744_, 0, v_snd_3723_);
lean_ctor_set(v___x_3744_, 1, v_consumers_3724_);
lean_ctor_set(v___x_3744_, 2, v_capacity_3725_);
lean_ctor_set(v___x_3744_, 3, v_buf_3726_);
lean_ctor_set(v___x_3744_, 4, v___x_3727_);
lean_ctor_set(v___x_3744_, 5, v_sendIdx_3728_);
lean_ctor_set(v___x_3744_, 6, v___y_3729_);
lean_ctor_set_uint8(v___x_3744_, sizeof(void*)*7, v_closed_3730_);
v___x_3745_ = lean_box(0);
lean_inc(v_a_3732_);
v___x_3746_ = lean_apply_4(v___f_3731_, v___x_3745_, v___x_3744_, v_a_3732_, lean_box(0));
return v___x_3746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3747_, lean_object* v_consumers_3748_, lean_object* v_capacity_3749_, lean_object* v_buf_3750_, lean_object* v___x_3751_, lean_object* v_sendIdx_3752_, lean_object* v___y_3753_, lean_object* v_closed_3754_, lean_object* v___f_3755_, lean_object* v_a_3756_, lean_object* v_x_3757_, lean_object* v___y_3758_){
_start:
{
uint8_t v_closed_boxed_3759_; lean_object* v_res_3760_; 
v_closed_boxed_3759_ = lean_unbox(v_closed_3754_);
v_res_3760_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3747_, v_consumers_3748_, v_capacity_3749_, v_buf_3750_, v___x_3751_, v_sendIdx_3752_, v___y_3753_, v_closed_boxed_3759_, v___f_3755_, v_a_3756_, v_x_3757_);
lean_dec(v_a_3756_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3761_, uint8_t v___x_3762_, lean_object* v_bufCount_3763_, lean_object* v_producers_3764_, lean_object* v_consumers_3765_, lean_object* v_capacity_3766_, lean_object* v_buf_3767_, lean_object* v_sendIdx_3768_, uint8_t v_closed_3769_, uint8_t v___x_3770_, lean_object* v_a_3771_, lean_object* v_recvIdx_3772_, lean_object* v_x_3773_){
_start:
{
if (lean_obj_tag(v_x_3773_) == 0)
{
lean_object* v___x_3775_; 
lean_dec(v_sendIdx_3768_);
lean_dec_ref(v_buf_3767_);
lean_dec(v_capacity_3766_);
lean_dec_ref(v_consumers_3765_);
lean_dec_ref(v_producers_3764_);
lean_dec(v___x_3761_);
v___x_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3775_, 0, v_x_3773_);
return v___x_3775_;
}
else
{
lean_object* v___f_3776_; lean_object* v___x_3777_; lean_object* v___f_3778_; lean_object* v___y_3780_; lean_object* v___x_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; 
v___f_3776_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3776_, 0, v_x_3773_);
v___x_3777_ = lean_box(v___x_3762_);
lean_inc_ref(v___f_3776_);
lean_inc(v___x_3761_);
v___f_3778_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3778_, 0, v___x_3761_);
lean_closure_set(v___f_3778_, 1, v___x_3777_);
lean_closure_set(v___f_3778_, 2, v___f_3776_);
v___x_3803_ = lean_unsigned_to_nat(1u);
v___x_3804_ = lean_nat_add(v_recvIdx_3772_, v___x_3803_);
v___x_3805_ = lean_nat_dec_eq(v___x_3804_, v_capacity_3766_);
if (v___x_3805_ == 0)
{
v___y_3780_ = v___x_3804_;
goto v___jp_3779_;
}
else
{
lean_dec(v___x_3804_);
lean_inc(v___x_3761_);
v___y_3780_ = v___x_3761_;
goto v___jp_3779_;
}
v___jp_3779_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3781_ = lean_unsigned_to_nat(1u);
v___x_3782_ = lean_nat_sub(v_bufCount_3763_, v___x_3781_);
lean_inc(v___y_3780_);
lean_inc(v_sendIdx_3768_);
lean_inc(v___x_3782_);
lean_inc_ref(v_buf_3767_);
lean_inc(v_capacity_3766_);
lean_inc_ref(v_consumers_3765_);
lean_inc_ref(v_producers_3764_);
v___x_3783_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3783_, 0, v_producers_3764_);
lean_ctor_set(v___x_3783_, 1, v_consumers_3765_);
lean_ctor_set(v___x_3783_, 2, v_capacity_3766_);
lean_ctor_set(v___x_3783_, 3, v_buf_3767_);
lean_ctor_set(v___x_3783_, 4, v___x_3782_);
lean_ctor_set(v___x_3783_, 5, v_sendIdx_3768_);
lean_ctor_set(v___x_3783_, 6, v___y_3780_);
lean_ctor_set_uint8(v___x_3783_, sizeof(void*)*7, v_closed_3769_);
v___x_3784_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3764_);
if (lean_obj_tag(v___x_3784_) == 1)
{
lean_object* v_val_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3800_; 
lean_dec_ref_known(v___x_3783_, 7);
lean_dec_ref(v___f_3776_);
v_val_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3800_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_val_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3800_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v_fst_3789_; lean_object* v_snd_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___f_3794_; lean_object* v___x_3796_; 
v_fst_3789_ = lean_ctor_get(v_val_3785_, 0);
lean_inc(v_fst_3789_);
v_snd_3790_ = lean_ctor_get(v_val_3785_, 1);
lean_inc(v_snd_3790_);
lean_dec(v_val_3785_);
v___x_3791_ = lean_box(v___x_3770_);
v___x_3792_ = lean_io_promise_resolve(v___x_3791_, v_fst_3789_);
lean_dec(v_fst_3789_);
v___x_3793_ = lean_box(v_closed_3769_);
lean_inc(v_a_3771_);
v___f_3794_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3794_, 0, v_snd_3790_);
lean_closure_set(v___f_3794_, 1, v_consumers_3765_);
lean_closure_set(v___f_3794_, 2, v_capacity_3766_);
lean_closure_set(v___f_3794_, 3, v_buf_3767_);
lean_closure_set(v___f_3794_, 4, v___x_3782_);
lean_closure_set(v___f_3794_, 5, v_sendIdx_3768_);
lean_closure_set(v___f_3794_, 6, v___y_3780_);
lean_closure_set(v___f_3794_, 7, v___x_3793_);
lean_closure_set(v___f_3794_, 8, v___f_3778_);
lean_closure_set(v___f_3794_, 9, v_a_3771_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3792_);
v___x_3796_ = v___x_3787_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3792_);
v___x_3796_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
v___x_3798_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3761_, v___x_3762_, v___x_3797_, v___f_3794_);
return v___x_3798_;
}
}
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_dec(v___x_3784_);
lean_dec(v___x_3782_);
lean_dec(v___y_3780_);
lean_dec_ref(v___f_3778_);
lean_dec(v_sendIdx_3768_);
lean_dec_ref(v_buf_3767_);
lean_dec(v_capacity_3766_);
lean_dec_ref(v_consumers_3765_);
v___x_3801_ = lean_box(0);
v___x_3802_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3761_, v___x_3762_, v___f_3776_, v___x_3801_, v___x_3783_, v_a_3771_);
return v___x_3802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3806_, lean_object* v___x_3807_, lean_object* v_bufCount_3808_, lean_object* v_producers_3809_, lean_object* v_consumers_3810_, lean_object* v_capacity_3811_, lean_object* v_buf_3812_, lean_object* v_sendIdx_3813_, lean_object* v_closed_3814_, lean_object* v___x_3815_, lean_object* v_a_3816_, lean_object* v_recvIdx_3817_, lean_object* v_x_3818_, lean_object* v___y_3819_){
_start:
{
uint8_t v___x_6457__boxed_3820_; uint8_t v_closed_boxed_3821_; uint8_t v___x_6458__boxed_3822_; lean_object* v_res_3823_; 
v___x_6457__boxed_3820_ = lean_unbox(v___x_3807_);
v_closed_boxed_3821_ = lean_unbox(v_closed_3814_);
v___x_6458__boxed_3822_ = lean_unbox(v___x_3815_);
v_res_3823_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3806_, v___x_6457__boxed_3820_, v_bufCount_3808_, v_producers_3809_, v_consumers_3810_, v_capacity_3811_, v_buf_3812_, v_sendIdx_3813_, v_closed_boxed_3821_, v___x_6458__boxed_3822_, v_a_3816_, v_recvIdx_3817_, v_x_3818_);
lean_dec(v_recvIdx_3817_);
lean_dec(v_a_3816_);
lean_dec(v_bufCount_3808_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3824_, lean_object* v_x_3825_){
_start:
{
if (lean_obj_tag(v_x_3825_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3835_; 
v_a_3827_ = lean_ctor_get(v_x_3825_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_x_3825_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3829_ = v_x_3825_;
v_isShared_3830_ = v_isSharedCheck_3835_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v_x_3825_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3835_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
return v___x_3833_;
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3864_; 
v_a_3836_ = lean_ctor_get(v_x_3825_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_x_3825_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3838_ = v_x_3825_;
v_isShared_3839_ = v_isSharedCheck_3864_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v_x_3825_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3864_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v_producers_3840_; lean_object* v_consumers_3841_; lean_object* v_capacity_3842_; lean_object* v_buf_3843_; lean_object* v_bufCount_3844_; lean_object* v_sendIdx_3845_; lean_object* v_recvIdx_3846_; uint8_t v_closed_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; 
v_producers_3840_ = lean_ctor_get(v_a_3836_, 0);
lean_inc_ref(v_producers_3840_);
v_consumers_3841_ = lean_ctor_get(v_a_3836_, 1);
lean_inc_ref(v_consumers_3841_);
v_capacity_3842_ = lean_ctor_get(v_a_3836_, 2);
lean_inc(v_capacity_3842_);
v_buf_3843_ = lean_ctor_get(v_a_3836_, 3);
lean_inc_ref(v_buf_3843_);
v_bufCount_3844_ = lean_ctor_get(v_a_3836_, 4);
lean_inc(v_bufCount_3844_);
v_sendIdx_3845_ = lean_ctor_get(v_a_3836_, 5);
lean_inc(v_sendIdx_3845_);
v_recvIdx_3846_ = lean_ctor_get(v_a_3836_, 6);
lean_inc(v_recvIdx_3846_);
v_closed_3847_ = lean_ctor_get_uint8(v_a_3836_, sizeof(void*)*7);
lean_dec(v_a_3836_);
v___x_3848_ = lean_unsigned_to_nat(0u);
v___x_3849_ = lean_nat_dec_eq(v_bufCount_3844_, v___x_3848_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___f_3857_; lean_object* v___x_3859_; 
v___x_3850_ = lean_array_fget_borrowed(v_buf_3843_, v_recvIdx_3846_);
v___x_3851_ = lean_box(0);
v___x_3852_ = lean_st_ref_swap(v___x_3850_, v___x_3851_);
v___x_3853_ = 1;
v___x_3854_ = lean_box(v___x_3849_);
v___x_3855_ = lean_box(v_closed_3847_);
v___x_3856_ = lean_box(v___x_3853_);
lean_inc(v_a_3824_);
v___f_3857_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_3857_, 0, v___x_3848_);
lean_closure_set(v___f_3857_, 1, v___x_3854_);
lean_closure_set(v___f_3857_, 2, v_bufCount_3844_);
lean_closure_set(v___f_3857_, 3, v_producers_3840_);
lean_closure_set(v___f_3857_, 4, v_consumers_3841_);
lean_closure_set(v___f_3857_, 5, v_capacity_3842_);
lean_closure_set(v___f_3857_, 6, v_buf_3843_);
lean_closure_set(v___f_3857_, 7, v_sendIdx_3845_);
lean_closure_set(v___f_3857_, 8, v___x_3855_);
lean_closure_set(v___f_3857_, 9, v___x_3856_);
lean_closure_set(v___f_3857_, 10, v_a_3824_);
lean_closure_set(v___f_3857_, 11, v_recvIdx_3846_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3852_);
v___x_3859_ = v___x_3838_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3852_);
v___x_3859_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
v___x_3861_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3848_, v___x_3849_, v___x_3860_, v___f_3857_);
return v___x_3861_;
}
}
else
{
lean_object* v___x_3863_; 
lean_dec(v_recvIdx_3846_);
lean_dec(v_sendIdx_3845_);
lean_dec(v_bufCount_3844_);
lean_dec_ref(v_buf_3843_);
lean_dec(v_capacity_3842_);
lean_dec_ref(v_consumers_3841_);
lean_dec_ref(v_producers_3840_);
lean_del_object(v___x_3838_);
v___x_3863_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_3863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_3865_, lean_object* v_x_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3865_, v_x_3866_);
lean_dec(v_a_3865_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_3869_){
_start:
{
lean_object* v___x_3871_; lean_object* v___f_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; 
v___x_3871_ = lean_st_ref_get(v_a_3869_);
lean_inc(v_a_3869_);
v___f_3872_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3872_, 0, v_a_3869_);
v___x_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3871_);
v___x_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
v___x_3875_ = lean_unsigned_to_nat(0u);
v___x_3876_ = 0;
v___x_3877_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3875_, v___x_3876_, v___x_3874_, v___f_3872_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3878_);
lean_dec(v_a_3878_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3882_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_3885_, lean_object* v_a_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_3885_, v_a_3886_);
lean_dec(v_a_3886_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_3889_, lean_object* v_x_3890_){
_start:
{
lean_object* v_val_3893_; lean_object* v___x_3895_; 
v___x_3895_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3889_, v_x_3890_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
lean_ctor_set_tag(v___x_3898_, 1);
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
v_val_3893_ = v___x_3901_;
goto v___jp_3892_;
}
}
}
else
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
v_a_3904_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3895_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3895_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
lean_ctor_set_tag(v___x_3906_, 0);
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
v_val_3893_ = v___x_3909_;
goto v___jp_3892_;
}
}
}
v___jp_3892_:
{
lean_object* v___x_3894_; 
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v_val_3893_);
return v___x_3894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_3912_, lean_object* v_x_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_3912_, v_x_3913_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v_x_3916_){
_start:
{
uint8_t v___y_3919_; 
if (lean_obj_tag(v_x_3916_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3931_; 
v_a_3923_ = lean_ctor_get(v_x_3916_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_x_3916_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3925_ = v_x_3916_;
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v_x_3916_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; 
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
return v___x_3929_;
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v_bufCount_3933_; uint8_t v_closed_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_a_3932_ = lean_ctor_get(v_x_3916_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v_x_3916_, 1);
v_bufCount_3933_ = lean_ctor_get(v_a_3932_, 4);
lean_inc(v_bufCount_3933_);
v_closed_3934_ = lean_ctor_get_uint8(v_a_3932_, sizeof(void*)*7);
lean_dec(v_a_3932_);
v___x_3935_ = lean_unsigned_to_nat(0u);
v___x_3936_ = lean_nat_dec_eq(v_bufCount_3933_, v___x_3935_);
lean_dec(v_bufCount_3933_);
if (v___x_3936_ == 0)
{
uint8_t v___x_3937_; 
v___x_3937_ = 1;
v___y_3919_ = v___x_3937_;
goto v___jp_3918_;
}
else
{
v___y_3919_ = v_closed_3934_;
goto v___jp_3918_;
}
}
v___jp_3918_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3920_ = lean_box(v___y_3919_);
v___x_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v_x_3938_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___y_3941_, lean_object* v___f_3942_, lean_object* v_x_3943_){
_start:
{
if (lean_obj_tag(v_x_3943_) == 0)
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref(v___f_3942_);
v_a_3945_ = lean_ctor_get(v_x_3943_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v_x_3943_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3947_ = v_x_3943_;
v_isShared_3948_ = v_isSharedCheck_3953_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v_x_3943_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3953_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3951_; 
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
return v___x_3951_;
}
}
}
else
{
lean_object* v_a_3954_; uint8_t v___x_3955_; 
v_a_3954_ = lean_ctor_get(v_x_3943_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v_x_3943_, 1);
v___x_3955_ = lean_unbox(v_a_3954_);
lean_dec(v_a_3954_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_dec_ref(v___f_3942_);
v___x_3956_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_3956_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; lean_object* v___x_3960_; 
v___x_3957_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_3941_);
v___x_3958_ = lean_unsigned_to_nat(0u);
v___x_3959_ = 0;
v___x_3960_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3958_, v___x_3959_, v___x_3957_, v___f_3942_);
return v___x_3960_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___y_3961_, lean_object* v___f_3962_, lean_object* v_x_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___y_3961_, v___f_3962_, v_x_3963_);
lean_dec(v___y_3961_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_3966_, lean_object* v___f_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; lean_object* v___x_3975_; lean_object* v___f_3976_; lean_object* v___x_3977_; 
v___x_3970_ = lean_st_ref_get(v___y_3968_);
v___x_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
v___x_3973_ = lean_unsigned_to_nat(0u);
v___x_3974_ = 0;
v___x_3975_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3973_, v___x_3974_, v___x_3972_, v___f_3966_);
lean_inc(v___y_3968_);
v___f_3976_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3976_, 0, v___y_3968_);
lean_closure_set(v___f_3976_, 1, v___f_3967_);
v___x_3977_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3973_, v___x_3974_, v___x_3975_, v___f_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_3978_, lean_object* v___f_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_3978_, v___f_3979_, v___y_3980_);
lean_dec(v___y_3980_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_3983_, lean_object* v_capacity_3984_, lean_object* v_buf_3985_, lean_object* v_bufCount_3986_, lean_object* v_sendIdx_3987_, lean_object* v_recvIdx_3988_, uint8_t v_closed_3989_, lean_object* v___y_3990_, lean_object* v_x_3991_){
_start:
{
if (lean_obj_tag(v_x_3991_) == 0)
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4001_; 
lean_dec(v_recvIdx_3988_);
lean_dec(v_sendIdx_3987_);
lean_dec(v_bufCount_3986_);
lean_dec_ref(v_buf_3985_);
lean_dec(v_capacity_3984_);
lean_dec_ref(v_producers_3983_);
v_a_3993_ = lean_ctor_get(v_x_3991_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v_x_3991_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3995_ = v_x_3991_;
v_isShared_3996_ = v_isSharedCheck_4001_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v_x_3991_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4001_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
lean_object* v___x_3999_; 
v___x_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
return v___x_3999_;
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4012_; 
v_a_4002_ = lean_ctor_get(v_x_3991_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_x_3991_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4004_ = v_x_3991_;
v_isShared_4005_ = v_isSharedCheck_4012_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v_x_3991_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4012_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4006_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_4006_, 0, v_producers_3983_);
lean_ctor_set(v___x_4006_, 1, v_a_4002_);
lean_ctor_set(v___x_4006_, 2, v_capacity_3984_);
lean_ctor_set(v___x_4006_, 3, v_buf_3985_);
lean_ctor_set(v___x_4006_, 4, v_bufCount_3986_);
lean_ctor_set(v___x_4006_, 5, v_sendIdx_3987_);
lean_ctor_set(v___x_4006_, 6, v_recvIdx_3988_);
lean_ctor_set_uint8(v___x_4006_, sizeof(void*)*7, v_closed_3989_);
v___x_4007_ = lean_st_ref_set(v___y_3990_, v___x_4006_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v___x_4007_);
v___x_4009_ = v___x_4004_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
return v___x_4010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_4013_, lean_object* v_capacity_4014_, lean_object* v_buf_4015_, lean_object* v_bufCount_4016_, lean_object* v_sendIdx_4017_, lean_object* v_recvIdx_4018_, lean_object* v_closed_4019_, lean_object* v___y_4020_, lean_object* v_x_4021_, lean_object* v___y_4022_){
_start:
{
uint8_t v_closed_boxed_4023_; lean_object* v_res_4024_; 
v_closed_boxed_4023_ = lean_unbox(v_closed_4019_);
v_res_4024_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_4013_, v_capacity_4014_, v_buf_4015_, v_bufCount_4016_, v_sendIdx_4017_, v_recvIdx_4018_, v_closed_boxed_4023_, v___y_4020_, v_x_4021_);
lean_dec(v___y_4020_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_4025_, lean_object* v_x_4026_, lean_object* v_head_4027_, lean_object* v_x_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_4025_, v_x_4026_, v_head_4027_, v_x_4028_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_4031_, lean_object* v_x_4032_){
_start:
{
if (lean_obj_tag(v_x_4031_) == 0)
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4034_, 0, v_x_4032_);
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
return v___x_4035_;
}
else
{
lean_object* v_head_4036_; lean_object* v_tail_4037_; lean_object* v_waiter_4038_; lean_object* v___f_4039_; lean_object* v_val_4041_; 
v_head_4036_ = lean_ctor_get(v_x_4031_, 0);
lean_inc(v_head_4036_);
v_tail_4037_ = lean_ctor_get(v_x_4031_, 1);
lean_inc(v_tail_4037_);
lean_dec_ref_known(v_x_4031_, 2);
v_waiter_4038_ = lean_ctor_get(v_head_4036_, 1);
lean_inc(v_waiter_4038_);
v___f_4039_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4039_, 0, v_tail_4037_);
lean_closure_set(v___f_4039_, 1, v_x_4032_);
lean_closure_set(v___f_4039_, 2, v_head_4036_);
if (lean_obj_tag(v_waiter_4038_) == 0)
{
lean_object* v___x_4045_; 
v___x_4045_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_4041_ = v___x_4045_;
goto v___jp_4040_;
}
else
{
lean_object* v_val_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4060_; 
v_val_4046_ = lean_ctor_get(v_waiter_4038_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_waiter_4038_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4048_ = v_waiter_4038_;
v_isShared_4049_ = v_isSharedCheck_4060_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_val_4046_);
lean_dec(v_waiter_4038_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4060_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v_finished_4050_; lean_object* v___x_4051_; lean_object* v___f_4052_; lean_object* v___x_4054_; 
v_finished_4050_ = lean_ctor_get(v_val_4046_, 0);
lean_inc(v_finished_4050_);
lean_dec(v_val_4046_);
v___x_4051_ = lean_st_ref_get(v_finished_4050_);
lean_dec(v_finished_4050_);
v___f_4052_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v___x_4051_);
v___x_4054_ = v___x_4048_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4051_);
v___x_4054_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; lean_object* v___x_4058_; 
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
v___x_4056_ = lean_unsigned_to_nat(0u);
v___x_4057_ = 0;
v___x_4058_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4056_, v___x_4057_, v___x_4055_, v___f_4052_);
v_val_4041_ = v___x_4058_;
goto v___jp_4040_;
}
}
}
v___jp_4040_:
{
lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = lean_unsigned_to_nat(0u);
v___x_4043_ = 0;
v___x_4044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4042_, v___x_4043_, v_val_4041_, v___f_4039_);
return v___x_4044_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_4061_, lean_object* v_x_4062_, lean_object* v_head_4063_, lean_object* v_x_4064_){
_start:
{
if (lean_obj_tag(v_x_4064_) == 0)
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4074_; 
lean_dec_ref(v_head_4063_);
lean_dec(v_x_4062_);
lean_dec(v_tail_4061_);
v_a_4066_ = lean_ctor_get(v_x_4064_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_x_4064_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4068_ = v_x_4064_;
v_isShared_4069_ = v_isSharedCheck_4074_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v_x_4064_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4074_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4072_; 
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
}
}
else
{
lean_object* v_a_4075_; uint8_t v___x_4076_; 
v_a_4075_ = lean_ctor_get(v_x_4064_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v_x_4064_, 1);
v___x_4076_ = lean_unbox(v_a_4075_);
lean_dec(v_a_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; 
lean_dec_ref(v_head_4063_);
v___x_4077_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4061_, v_x_4062_);
return v___x_4077_;
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4078_, 0, v_head_4063_);
lean_ctor_set(v___x_4078_, 1, v_x_4062_);
v___x_4079_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4061_, v___x_4078_);
return v___x_4079_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_4080_, lean_object* v_x_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4080_, v_x_4081_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_4084_){
_start:
{
if (lean_obj_tag(v_x_4084_) == 0)
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v_x_4084_);
return v___x_4086_;
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4096_; 
v_a_4087_ = lean_ctor_get(v_x_4084_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_x_4084_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4089_ = v_x_4084_;
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v_x_4084_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4091_ = l_List_reverse___redArg(v_a_4087_);
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
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4097_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4100_, lean_object* v___x_4101_, lean_object* v_x_4102_){
_start:
{
if (lean_obj_tag(v_x_4102_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4112_; 
lean_dec(v___x_4101_);
lean_dec(v_a_4100_);
v_a_4104_ = lean_ctor_get(v_x_4102_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v_x_4102_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4106_ = v_x_4102_;
v_isShared_4107_ = v_isSharedCheck_4112_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v_x_4102_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4112_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4110_; 
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
return v___x_4110_;
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4129_; 
v_a_4113_ = lean_ctor_get(v_x_4102_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v_x_4102_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4115_ = v_x_4102_;
v_isShared_4116_ = v_isSharedCheck_4129_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v_x_4102_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4129_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
uint8_t v___x_4117_; 
v___x_4117_ = l_List_isEmpty___redArg(v_a_4100_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; lean_object* v___x_4120_; 
lean_dec(v___x_4101_);
v___x_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4118_, 0, v_a_4113_);
lean_ctor_set(v___x_4118_, 1, v_a_4100_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v___x_4118_);
v___x_4120_ = v___x_4115_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; 
v___x_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
return v___x_4121_;
}
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
lean_dec(v_a_4100_);
v___x_4123_ = l_List_reverse___redArg(v_a_4113_);
v___x_4124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4101_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v___x_4124_);
v___x_4126_ = v___x_4115_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4124_);
v___x_4126_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4127_; 
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
return v___x_4127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4130_, lean_object* v___x_4131_, lean_object* v_x_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4130_, v___x_4131_, v_x_4132_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_eList_4135_, lean_object* v___x_4136_, lean_object* v___f_4137_, lean_object* v_x_4138_){
_start:
{
if (lean_obj_tag(v_x_4138_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v___f_4137_);
lean_dec(v___x_4136_);
lean_dec(v_eList_4135_);
v_a_4140_ = lean_ctor_get(v_x_4138_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_x_4138_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4142_ = v_x_4138_;
v_isShared_4143_ = v_isSharedCheck_4148_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v_x_4138_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4148_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; uint8_t v___x_4152_; lean_object* v___x_4153_; lean_object* v___f_4154_; lean_object* v___x_4155_; 
v_a_4149_ = lean_ctor_get(v_x_4138_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v_x_4138_, 1);
lean_inc(v___x_4136_);
v___x_4150_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4135_, v___x_4136_);
v___x_4151_ = lean_unsigned_to_nat(0u);
v___x_4152_ = 0;
v___x_4153_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4151_, v___x_4152_, v___x_4150_, v___f_4137_);
v___f_4154_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4154_, 0, v_a_4149_);
lean_closure_set(v___f_4154_, 1, v___x_4136_);
v___x_4155_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4151_, v___x_4152_, v___x_4153_, v___f_4154_);
return v___x_4155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_eList_4156_, lean_object* v___x_4157_, lean_object* v___f_4158_, lean_object* v_x_4159_, lean_object* v___y_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v_eList_4156_, v___x_4157_, v___f_4158_, v_x_4159_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_eList_4166_; lean_object* v_dList_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___f_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___f_4174_; lean_object* v___x_4175_; 
v_eList_4166_ = lean_ctor_get(v_q_4163_, 0);
lean_inc(v_eList_4166_);
v_dList_4167_ = lean_ctor_get(v_q_4163_, 1);
lean_inc(v_dList_4167_);
lean_dec_ref(v_q_4163_);
v___x_4168_ = lean_box(0);
v___x_4169_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4167_, v___x_4168_);
v___f_4170_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4171_ = lean_unsigned_to_nat(0u);
v___x_4172_ = 0;
v___x_4173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4171_, v___x_4172_, v___x_4169_, v___f_4170_);
v___f_4174_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4174_, 0, v_eList_4166_);
lean_closure_set(v___f_4174_, 1, v___x_4168_);
lean_closure_set(v___f_4174_, 2, v___f_4170_);
v___x_4175_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4171_, v___x_4172_, v___x_4173_, v___f_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4176_, v___y_4177_);
lean_dec(v___y_4177_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4180_, lean_object* v_x_4181_){
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
lean_object* v_a_4192_; lean_object* v_producers_4193_; lean_object* v_consumers_4194_; lean_object* v_capacity_4195_; lean_object* v_buf_4196_; lean_object* v_bufCount_4197_; lean_object* v_sendIdx_4198_; lean_object* v_recvIdx_4199_; uint8_t v_closed_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___f_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; lean_object* v___x_4206_; 
v_a_4192_ = lean_ctor_get(v_x_4181_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v_x_4181_, 1);
v_producers_4193_ = lean_ctor_get(v_a_4192_, 0);
lean_inc_ref(v_producers_4193_);
v_consumers_4194_ = lean_ctor_get(v_a_4192_, 1);
lean_inc_ref(v_consumers_4194_);
v_capacity_4195_ = lean_ctor_get(v_a_4192_, 2);
lean_inc(v_capacity_4195_);
v_buf_4196_ = lean_ctor_get(v_a_4192_, 3);
lean_inc_ref(v_buf_4196_);
v_bufCount_4197_ = lean_ctor_get(v_a_4192_, 4);
lean_inc(v_bufCount_4197_);
v_sendIdx_4198_ = lean_ctor_get(v_a_4192_, 5);
lean_inc(v_sendIdx_4198_);
v_recvIdx_4199_ = lean_ctor_get(v_a_4192_, 6);
lean_inc(v_recvIdx_4199_);
v_closed_4200_ = lean_ctor_get_uint8(v_a_4192_, sizeof(void*)*7);
lean_dec(v_a_4192_);
v___x_4201_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4194_, v___y_4180_);
v___x_4202_ = lean_box(v_closed_4200_);
lean_inc(v___y_4180_);
v___f_4203_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4203_, 0, v_producers_4193_);
lean_closure_set(v___f_4203_, 1, v_capacity_4195_);
lean_closure_set(v___f_4203_, 2, v_buf_4196_);
lean_closure_set(v___f_4203_, 3, v_bufCount_4197_);
lean_closure_set(v___f_4203_, 4, v_sendIdx_4198_);
lean_closure_set(v___f_4203_, 5, v_recvIdx_4199_);
lean_closure_set(v___f_4203_, 6, v___x_4202_);
lean_closure_set(v___f_4203_, 7, v___y_4180_);
v___x_4204_ = lean_unsigned_to_nat(0u);
v___x_4205_ = 0;
v___x_4206_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4204_, v___x_4205_, v___x_4201_, v___f_4203_);
return v___x_4206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4207_, lean_object* v_x_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4207_, v_x_4208_);
lean_dec(v___y_4207_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4211_){
_start:
{
lean_object* v___x_4213_; lean_object* v___f_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; lean_object* v___x_4219_; 
v___x_4213_ = lean_st_ref_get(v___y_4211_);
lean_inc(v___y_4211_);
v___f_4214_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4214_, 0, v___y_4211_);
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
v___x_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = 0;
v___x_4219_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4217_, v___x_4218_, v___x_4216_, v___f_4214_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4220_);
lean_dec(v___y_4220_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4228_){
_start:
{
lean_object* v___f_4229_; lean_object* v___f_4230_; lean_object* v___f_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
lean_inc_ref_n(v_ch_4228_, 2);
v___f_4229_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4229_, 0, v_ch_4228_);
v___f_4230_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___f_4231_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2));
v___x_4232_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4232_, 0, lean_box(0));
lean_closure_set(v___x_4232_, 1, lean_box(0));
lean_closure_set(v___x_4232_, 2, v_ch_4228_);
lean_closure_set(v___x_4232_, 3, v___f_4230_);
v___x_4233_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4233_, 0, lean_box(0));
lean_closure_set(v___x_4233_, 1, lean_box(0));
lean_closure_set(v___x_4233_, 2, v_ch_4228_);
lean_closure_set(v___x_4233_, 3, v___f_4231_);
v___x_4234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4232_);
lean_ctor_set(v___x_4234_, 1, v___f_4229_);
lean_ctor_set(v___x_4234_, 2, v___x_4233_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4235_, lean_object* v_ch_4236_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4238_, lean_object* v_q_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4239_, v___y_4240_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4243_, lean_object* v_q_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4243_, v_q_4244_, v___y_4245_);
lean_dec(v___y_4245_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4248_, lean_object* v_x_4249_, lean_object* v_x_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4249_, v_x_4250_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4254_, lean_object* v_x_4255_, lean_object* v_x_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4254_, v_x_4255_, v_x_4256_, v___y_4257_);
lean_dec(v___y_4257_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg(lean_object* v_x_4260_){
_start:
{
switch(lean_obj_tag(v_x_4260_))
{
case 0:
{
lean_object* v___x_4261_; 
v___x_4261_ = lean_unsigned_to_nat(0u);
return v___x_4261_;
}
case 1:
{
lean_object* v___x_4262_; 
v___x_4262_ = lean_unsigned_to_nat(1u);
return v___x_4262_;
}
default: 
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_unsigned_to_nat(2u);
return v___x_4263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(lean_object* v_x_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4264_);
lean_dec_ref(v_x_4264_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx(lean_object* v_00_u03b1_4266_, lean_object* v_x_4267_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___boxed(lean_object* v_00_u03b1_4269_, lean_object* v_x_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Std_CloseableChannel_Flavors_ctorIdx(v_00_u03b1_4269_, v_x_4270_);
lean_dec_ref(v_x_4270_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4272_, lean_object* v_k_4273_){
_start:
{
lean_object* v_ch_4274_; lean_object* v___x_4275_; 
v_ch_4274_ = lean_ctor_get(v_t_4272_, 0);
lean_inc_ref(v_ch_4274_);
lean_dec_ref(v_t_4272_);
v___x_4275_ = lean_apply_1(v_k_4273_, v_ch_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4276_, lean_object* v_motive_4277_, lean_object* v_ctorIdx_4278_, lean_object* v_t_4279_, lean_object* v_h_4280_, lean_object* v_k_4281_){
_start:
{
lean_object* v___x_4282_; 
v___x_4282_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4279_, v_k_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4283_, lean_object* v_motive_4284_, lean_object* v_ctorIdx_4285_, lean_object* v_t_4286_, lean_object* v_h_4287_, lean_object* v_k_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4283_, v_motive_4284_, v_ctorIdx_4285_, v_t_4286_, v_h_4287_, v_k_4288_);
lean_dec(v_ctorIdx_4285_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4290_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4290_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4293_, lean_object* v_motive_4294_, lean_object* v_t_4295_, lean_object* v_h_4296_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4297_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4295_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4299_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4300_){
_start:
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4299_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4300_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4302_, lean_object* v_motive_4303_, lean_object* v_t_4304_, lean_object* v_h_4305_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4306_){
_start:
{
lean_object* v___x_4307_; 
v___x_4307_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4304_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4306_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4308_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4309_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4308_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4309_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4311_, lean_object* v_motive_4312_, lean_object* v_t_4313_, lean_object* v_h_4314_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4315_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4313_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4315_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4317_){
_start:
{
if (lean_obj_tag(v_capacity_4317_) == 0)
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4319_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
else
{
lean_object* v_val_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4338_; 
v_val_4321_ = lean_ctor_get(v_capacity_4317_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v_capacity_4317_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4323_ = v_capacity_4317_;
v_isShared_4324_ = v_isSharedCheck_4338_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_val_4321_);
lean_dec(v_capacity_4317_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4338_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v_zero_4325_; uint8_t v_isZero_4326_; 
v_zero_4325_ = lean_unsigned_to_nat(0u);
v_isZero_4326_ = lean_nat_dec_eq(v_val_4321_, v_zero_4325_);
if (v_isZero_4326_ == 1)
{
lean_object* v___x_4327_; lean_object* v___x_4329_; 
lean_dec(v_val_4321_);
v___x_4327_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 0, v___x_4327_);
v___x_4329_ = v___x_4323_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4327_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
else
{
lean_object* v_one_4331_; lean_object* v_n_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
v_one_4331_ = lean_unsigned_to_nat(1u);
v_n_4332_ = lean_nat_sub(v_val_4321_, v_one_4331_);
lean_dec(v_val_4321_);
v___x_4333_ = lean_nat_add(v_n_4332_, v_one_4331_);
lean_dec(v_n_4332_);
v___x_4334_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4333_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set_tag(v___x_4323_, 2);
lean_ctor_set(v___x_4323_, 0, v___x_4334_);
v___x_4336_ = v___x_4323_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Std_CloseableChannel_new___redArg(v_capacity_4339_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4342_, lean_object* v_capacity_4343_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = l_Std_CloseableChannel_new___redArg(v_capacity_4343_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4346_, lean_object* v_capacity_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Std_CloseableChannel_new(v_00_u03b1_4346_, v_capacity_4347_);
return v_res_4349_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4350_, lean_object* v_v_4351_){
_start:
{
switch(lean_obj_tag(v_ch_4350_))
{
case 0:
{
lean_object* v_ch_4353_; uint8_t v___x_4354_; 
v_ch_4353_ = lean_ctor_get(v_ch_4350_, 0);
lean_inc_ref(v_ch_4353_);
lean_dec_ref_known(v_ch_4350_, 1);
v___x_4354_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4353_, v_v_4351_);
return v___x_4354_;
}
case 1:
{
lean_object* v_ch_4355_; uint8_t v___x_4356_; 
v_ch_4355_ = lean_ctor_get(v_ch_4350_, 0);
lean_inc_ref(v_ch_4355_);
lean_dec_ref_known(v_ch_4350_, 1);
v___x_4356_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4355_, v_v_4351_);
return v___x_4356_;
}
default: 
{
lean_object* v_ch_4357_; uint8_t v___x_4358_; 
v_ch_4357_ = lean_ctor_get(v_ch_4350_, 0);
lean_inc_ref(v_ch_4357_);
lean_dec_ref_known(v_ch_4350_, 1);
v___x_4358_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4357_, v_v_4351_);
return v___x_4358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4359_, lean_object* v_v_4360_, lean_object* v_a_4361_){
_start:
{
uint8_t v_res_4362_; lean_object* v_r_4363_; 
v_res_4362_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4359_, v_v_4360_);
v_r_4363_ = lean_box(v_res_4362_);
return v_r_4363_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4364_, lean_object* v_ch_4365_, lean_object* v_v_4366_){
_start:
{
uint8_t v___x_4368_; 
v___x_4368_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4365_, v_v_4366_);
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4369_, lean_object* v_ch_4370_, lean_object* v_v_4371_, lean_object* v_a_4372_){
_start:
{
uint8_t v_res_4373_; lean_object* v_r_4374_; 
v_res_4373_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4369_, v_ch_4370_, v_v_4371_);
v_r_4374_ = lean_box(v_res_4373_);
return v_r_4374_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4375_, lean_object* v_v_4376_){
_start:
{
switch(lean_obj_tag(v_ch_4375_))
{
case 0:
{
lean_object* v_ch_4378_; lean_object* v___x_4379_; 
v_ch_4378_ = lean_ctor_get(v_ch_4375_, 0);
lean_inc_ref(v_ch_4378_);
lean_dec_ref_known(v_ch_4375_, 1);
v___x_4379_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4378_, v_v_4376_);
return v___x_4379_;
}
case 1:
{
lean_object* v_ch_4380_; lean_object* v___x_4381_; 
v_ch_4380_ = lean_ctor_get(v_ch_4375_, 0);
lean_inc_ref(v_ch_4380_);
lean_dec_ref_known(v_ch_4375_, 1);
v___x_4381_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4380_, v_v_4376_);
return v___x_4381_;
}
default: 
{
lean_object* v_ch_4382_; lean_object* v___x_4383_; 
v_ch_4382_ = lean_ctor_get(v_ch_4375_, 0);
lean_inc_ref(v_ch_4382_);
lean_dec_ref_known(v_ch_4375_, 1);
v___x_4383_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4382_, v_v_4376_);
return v___x_4383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4384_, lean_object* v_v_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Std_CloseableChannel_send___redArg(v_ch_4384_, v_v_4385_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4388_, lean_object* v_ch_4389_, lean_object* v_v_4390_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Std_CloseableChannel_send___redArg(v_ch_4389_, v_v_4390_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4393_, lean_object* v_ch_4394_, lean_object* v_v_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Std_CloseableChannel_send(v_00_u03b1_4393_, v_ch_4394_, v_v_4395_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4398_){
_start:
{
switch(lean_obj_tag(v_ch_4398_))
{
case 0:
{
lean_object* v_ch_4400_; lean_object* v___x_4401_; 
v_ch_4400_ = lean_ctor_get(v_ch_4398_, 0);
lean_inc_ref(v_ch_4400_);
lean_dec_ref_known(v_ch_4398_, 1);
v___x_4401_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4400_);
return v___x_4401_;
}
case 1:
{
lean_object* v_ch_4402_; lean_object* v___x_4403_; 
v_ch_4402_ = lean_ctor_get(v_ch_4398_, 0);
lean_inc_ref(v_ch_4402_);
lean_dec_ref_known(v_ch_4398_, 1);
v___x_4403_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4402_);
return v___x_4403_;
}
default: 
{
lean_object* v_ch_4404_; lean_object* v___x_4405_; 
v_ch_4404_ = lean_ctor_get(v_ch_4398_, 0);
lean_inc_ref(v_ch_4404_);
lean_dec_ref_known(v_ch_4398_, 1);
v___x_4405_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4404_);
return v___x_4405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Std_CloseableChannel_close___redArg(v_ch_4406_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4409_, lean_object* v_ch_4410_){
_start:
{
lean_object* v___x_4412_; 
v___x_4412_ = l_Std_CloseableChannel_close___redArg(v_ch_4410_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4413_, lean_object* v_ch_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Std_CloseableChannel_close(v_00_u03b1_4413_, v_ch_4414_);
return v_res_4416_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4417_){
_start:
{
switch(lean_obj_tag(v_ch_4417_))
{
case 0:
{
lean_object* v_ch_4419_; uint8_t v___x_4420_; 
v_ch_4419_ = lean_ctor_get(v_ch_4417_, 0);
lean_inc_ref(v_ch_4419_);
lean_dec_ref_known(v_ch_4417_, 1);
v___x_4420_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4419_);
return v___x_4420_;
}
case 1:
{
lean_object* v_ch_4421_; uint8_t v___x_4422_; 
v_ch_4421_ = lean_ctor_get(v_ch_4417_, 0);
lean_inc_ref(v_ch_4421_);
lean_dec_ref_known(v_ch_4417_, 1);
v___x_4422_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4421_);
return v___x_4422_;
}
default: 
{
lean_object* v_ch_4423_; uint8_t v___x_4424_; 
v_ch_4423_ = lean_ctor_get(v_ch_4417_, 0);
lean_inc_ref(v_ch_4423_);
lean_dec_ref_known(v_ch_4417_, 1);
v___x_4424_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4423_);
return v___x_4424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4425_, lean_object* v_a_4426_){
_start:
{
uint8_t v_res_4427_; lean_object* v_r_4428_; 
v_res_4427_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4425_);
v_r_4428_ = lean_box(v_res_4427_);
return v_r_4428_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4429_, lean_object* v_ch_4430_){
_start:
{
uint8_t v___x_4432_; 
v___x_4432_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4430_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4433_, lean_object* v_ch_4434_, lean_object* v_a_4435_){
_start:
{
uint8_t v_res_4436_; lean_object* v_r_4437_; 
v_res_4436_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4433_, v_ch_4434_);
v_r_4437_ = lean_box(v_res_4436_);
return v_r_4437_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4438_){
_start:
{
switch(lean_obj_tag(v_ch_4438_))
{
case 0:
{
lean_object* v_ch_4440_; lean_object* v___x_4441_; 
v_ch_4440_ = lean_ctor_get(v_ch_4438_, 0);
lean_inc_ref(v_ch_4440_);
lean_dec_ref_known(v_ch_4438_, 1);
v___x_4441_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4440_);
return v___x_4441_;
}
case 1:
{
lean_object* v_ch_4442_; lean_object* v___x_4443_; 
v_ch_4442_ = lean_ctor_get(v_ch_4438_, 0);
lean_inc_ref(v_ch_4442_);
lean_dec_ref_known(v_ch_4438_, 1);
v___x_4443_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4442_);
return v___x_4443_;
}
default: 
{
lean_object* v_ch_4444_; lean_object* v___x_4445_; 
v_ch_4444_ = lean_ctor_get(v_ch_4438_, 0);
lean_inc_ref(v_ch_4444_);
lean_dec_ref_known(v_ch_4438_, 1);
v___x_4445_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4444_);
return v___x_4445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4446_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4449_, lean_object* v_ch_4450_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4450_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4453_, lean_object* v_ch_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4453_, v_ch_4454_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4457_){
_start:
{
switch(lean_obj_tag(v_ch_4457_))
{
case 0:
{
lean_object* v_ch_4459_; lean_object* v___x_4460_; 
v_ch_4459_ = lean_ctor_get(v_ch_4457_, 0);
lean_inc_ref(v_ch_4459_);
lean_dec_ref_known(v_ch_4457_, 1);
v___x_4460_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4459_);
return v___x_4460_;
}
case 1:
{
lean_object* v_ch_4461_; lean_object* v___x_4462_; 
v_ch_4461_ = lean_ctor_get(v_ch_4457_, 0);
lean_inc_ref(v_ch_4461_);
lean_dec_ref_known(v_ch_4457_, 1);
v___x_4462_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4461_);
return v___x_4462_;
}
default: 
{
lean_object* v_ch_4463_; lean_object* v___x_4464_; 
v_ch_4463_ = lean_ctor_get(v_ch_4457_, 0);
lean_inc_ref(v_ch_4463_);
lean_dec_ref_known(v_ch_4457_, 1);
v___x_4464_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4463_);
return v___x_4464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4465_, lean_object* v_a_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l_Std_CloseableChannel_recv___redArg(v_ch_4465_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4468_, lean_object* v_ch_4469_){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = l_Std_CloseableChannel_recv___redArg(v_ch_4469_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4472_, lean_object* v_ch_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Std_CloseableChannel_recv(v_00_u03b1_4472_, v_ch_4473_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4476_){
_start:
{
switch(lean_obj_tag(v_ch_4476_))
{
case 0:
{
lean_object* v_ch_4477_; lean_object* v___x_4478_; 
v_ch_4477_ = lean_ctor_get(v_ch_4476_, 0);
lean_inc_ref(v_ch_4477_);
lean_dec_ref_known(v_ch_4476_, 1);
v___x_4478_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4477_);
return v___x_4478_;
}
case 1:
{
lean_object* v_ch_4479_; lean_object* v___x_4480_; 
v_ch_4479_ = lean_ctor_get(v_ch_4476_, 0);
lean_inc_ref(v_ch_4479_);
lean_dec_ref_known(v_ch_4476_, 1);
v___x_4480_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4479_);
return v___x_4480_;
}
default: 
{
lean_object* v_ch_4481_; lean_object* v___x_4482_; 
v_ch_4481_ = lean_ctor_get(v_ch_4476_, 0);
lean_inc_ref(v_ch_4481_);
lean_dec_ref_known(v_ch_4476_, 1);
v___x_4482_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4481_);
return v___x_4482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4483_, lean_object* v_ch_4484_){
_start:
{
lean_object* v___x_4485_; 
v___x_4485_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4484_);
return v___x_4485_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = lean_box(0);
v___x_4487_ = lean_task_pure(v___x_4486_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4488_, lean_object* v_ch_4489_, lean_object* v_prio_4490_, lean_object* v_x_4491_){
_start:
{
if (lean_obj_tag(v_x_4491_) == 0)
{
lean_object* v___x_4493_; 
lean_dec(v_prio_4490_);
lean_dec_ref(v_ch_4489_);
lean_dec_ref(v_f_4488_);
v___x_4493_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4493_;
}
else
{
lean_object* v_val_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v_val_4494_ = lean_ctor_get(v_x_4491_, 0);
lean_inc(v_val_4494_);
lean_dec_ref_known(v_x_4491_, 1);
lean_inc_ref(v_f_4488_);
v___x_4495_ = lean_apply_2(v_f_4488_, v_val_4494_, lean_box(0));
v___x_4496_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4488_, v_ch_4489_, v_prio_4490_);
return v___x_4496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4497_, lean_object* v_ch_4498_, lean_object* v_prio_4499_, lean_object* v_x_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4497_, v_ch_4498_, v_prio_4499_, v_x_4500_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4503_, lean_object* v_ch_4504_, lean_object* v_prio_4505_){
_start:
{
lean_object* v___x_4507_; lean_object* v___f_4508_; uint8_t v___x_4509_; lean_object* v___x_4510_; 
lean_inc_ref(v_ch_4504_);
v___x_4507_ = l_Std_CloseableChannel_recv___redArg(v_ch_4504_);
lean_inc(v_prio_4505_);
v___f_4508_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4508_, 0, v_f_4503_);
lean_closure_set(v___f_4508_, 1, v_ch_4504_);
lean_closure_set(v___f_4508_, 2, v_prio_4505_);
v___x_4509_ = 0;
v___x_4510_ = lean_io_bind_task(v___x_4507_, v___f_4508_, v_prio_4505_, v___x_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4511_, lean_object* v_ch_4512_, lean_object* v_prio_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4511_, v_ch_4512_, v_prio_4513_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4516_, lean_object* v_f_4517_, lean_object* v_ch_4518_, lean_object* v_prio_4519_){
_start:
{
lean_object* v___x_4521_; 
v___x_4521_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4517_, v_ch_4518_, v_prio_4519_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4522_, lean_object* v_f_4523_, lean_object* v_ch_4524_, lean_object* v_prio_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4522_, v_f_4523_, v_ch_4524_, v_prio_4525_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(lean_object* v_x_4528_){
_start:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = lean_box(0);
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed(lean_object* v_x_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(v_x_4532_);
lean_dec_ref(v_x_4532_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4540_, lean_object* v_inst_4541_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4543_, lean_object* v_inst_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4543_, v_inst_4544_);
lean_dec(v_inst_4544_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_4546_){
_start:
{
lean_object* v___x_4547_; 
v___x_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4547_, 0, v_a_4546_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_4548_, lean_object* v_x_4549_){
_start:
{
if (lean_obj_tag(v_x_4549_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4559_; 
lean_dec_ref(v___f_4548_);
v_a_4551_ = lean_ctor_get(v_x_4549_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_x_4549_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4553_ = v_x_4549_;
v_isShared_4554_ = v_isSharedCheck_4559_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v_x_4549_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4559_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
lean_object* v___x_4557_; 
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
return v___x_4557_;
}
}
}
else
{
lean_object* v_a_4560_; 
v_a_4560_ = lean_ctor_get(v_x_4549_, 0);
lean_inc(v_a_4560_);
lean_dec_ref_known(v_x_4549_, 1);
if (lean_obj_tag(v_a_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref(v___f_4548_);
v_a_4561_ = lean_ctor_get(v_a_4560_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_a_4560_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4563_ = v_a_4560_;
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v_a_4560_);
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
lean_object* v_a_4570_; lean_object* v___x_4571_; uint8_t v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v_a_4570_ = lean_ctor_get(v_a_4560_, 0);
lean_inc(v_a_4570_);
lean_dec_ref_known(v_a_4560_, 1);
v___x_4571_ = lean_unsigned_to_nat(0u);
v___x_4572_ = 0;
v___x_4573_ = lean_task_map(v___f_4548_, v_a_4570_, v___x_4571_, v___x_4572_);
v___x_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4573_);
return v___x_4574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_4575_, lean_object* v_x_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(v___f_4575_, v_x_4576_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_4579_, lean_object* v_receiver_4580_){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; uint8_t v___x_4587_; lean_object* v___x_4588_; 
v___x_4582_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4580_);
v___x_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
v___x_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
v___x_4586_ = lean_unsigned_to_nat(0u);
v___x_4587_ = 0;
v___x_4588_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4586_, v___x_4587_, v___x_4585_, v___f_4579_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_4589_, lean_object* v_receiver_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(v___f_4589_, v_receiver_4590_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4598_, lean_object* v_inst_4599_){
_start:
{
lean_object* v___f_4600_; 
v___f_4600_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2));
return v___f_4600_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4601_, lean_object* v_inst_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4601_, v_inst_4602_);
lean_dec(v_inst_4602_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_4605_, lean_object* v_x_4606_){
_start:
{
if (lean_obj_tag(v_x_4606_) == 0)
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4616_; 
lean_dec_ref(v___f_4605_);
v_a_4608_ = lean_ctor_get(v_x_4606_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v_x_4606_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4610_ = v_x_4606_;
v_isShared_4611_ = v_isSharedCheck_4616_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v_x_4606_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4616_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
lean_object* v___x_4614_; 
v___x_4614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4613_);
return v___x_4614_;
}
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; uint8_t v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v_a_4617_ = lean_ctor_get(v_x_4606_, 0);
lean_inc(v_a_4617_);
lean_dec_ref_known(v_x_4606_, 1);
v___x_4618_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0));
v___x_4619_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4619_, 0, lean_box(0));
lean_closure_set(v___x_4619_, 1, lean_box(0));
lean_closure_set(v___x_4619_, 2, lean_box(0));
lean_closure_set(v___x_4619_, 3, v___x_4618_);
lean_closure_set(v___x_4619_, 4, v___f_4605_);
v___x_4620_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4620_, 0, lean_box(0));
lean_closure_set(v___x_4620_, 1, lean_box(0));
lean_closure_set(v___x_4620_, 2, lean_box(0));
lean_closure_set(v___x_4620_, 3, v___x_4619_);
v___x_4621_ = lean_unsigned_to_nat(0u);
v___x_4622_ = 0;
v___x_4623_ = lean_task_map(v___x_4620_, v_a_4617_, v___x_4621_, v___x_4622_);
v___x_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4623_);
return v___x_4624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_4625_, lean_object* v_x_4626_, lean_object* v___y_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(v___f_4625_, v_x_4626_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_4629_, lean_object* v_receiver_4630_, lean_object* v_x_4631_){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; uint8_t v___x_4637_; lean_object* v___x_4638_; 
v___x_4633_ = l_Std_CloseableChannel_send___redArg(v_receiver_4630_, v_x_4631_);
v___x_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
v___x_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
v___x_4636_ = lean_unsigned_to_nat(0u);
v___x_4637_ = 0;
v___x_4638_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4636_, v___x_4637_, v___x_4635_, v___f_4629_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_4639_, lean_object* v_receiver_4640_, lean_object* v_x_4641_, lean_object* v___y_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(v___f_4639_, v_receiver_4640_, v_x_4641_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(lean_object* v_x_4644_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v_x_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(v_x_4647_);
lean_dec_ref(v_x_4647_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(lean_object* v___f_4650_, lean_object* v_socket_4651_, lean_object* v_x_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = lean_apply_3(v___f_4650_, v_socket_4651_, v___y_4653_, lean_box(0));
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v___f_4656_, lean_object* v_socket_4657_, lean_object* v_x_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(v___f_4656_, v_socket_4657_, v_x_4658_, v___y_4659_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_4662_, lean_object* v___x_4663_, lean_object* v_socket_4664_, lean_object* v_data_4665_){
_start:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; uint8_t v___x_4670_; 
v___x_4667_ = lean_unsigned_to_nat(0u);
v___x_4668_ = lean_array_get_size(v_data_4665_);
v___x_4669_ = lean_box(0);
v___x_4670_ = lean_nat_dec_lt(v___x_4667_, v___x_4668_);
if (v___x_4670_ == 0)
{
lean_object* v___x_4671_; 
lean_dec_ref(v_data_4665_);
lean_dec_ref(v_socket_4664_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___f_4662_);
v___x_4671_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4671_;
}
else
{
lean_object* v___f_4672_; uint8_t v___x_4673_; 
v___f_4672_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4672_, 0, v___f_4662_);
lean_closure_set(v___f_4672_, 1, v_socket_4664_);
v___x_4673_ = lean_nat_dec_le(v___x_4668_, v___x_4668_);
if (v___x_4673_ == 0)
{
if (v___x_4670_ == 0)
{
lean_object* v___x_4674_; 
lean_dec_ref(v___f_4672_);
lean_dec_ref(v_data_4665_);
lean_dec_ref(v___x_4663_);
v___x_4674_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4674_;
}
else
{
size_t v___x_4675_; size_t v___x_4676_; lean_object* v___x_753__overap_4677_; lean_object* v___x_4678_; 
v___x_4675_ = ((size_t)0ULL);
v___x_4676_ = lean_usize_of_nat(v___x_4668_);
v___x_753__overap_4677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4663_, v___f_4672_, v_data_4665_, v___x_4675_, v___x_4676_, v___x_4669_);
v___x_4678_ = lean_apply_1(v___x_753__overap_4677_, lean_box(0));
return v___x_4678_;
}
}
else
{
size_t v___x_4679_; size_t v___x_4680_; lean_object* v___x_756__overap_4681_; lean_object* v___x_4682_; 
v___x_4679_ = ((size_t)0ULL);
v___x_4680_ = lean_usize_of_nat(v___x_4668_);
v___x_756__overap_4681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4663_, v___f_4672_, v_data_4665_, v___x_4679_, v___x_4680_, v___x_4669_);
v___x_4682_ = lean_apply_1(v___x_756__overap_4681_, lean_box(0));
return v___x_4682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_4683_, lean_object* v___x_4684_, lean_object* v_socket_4685_, lean_object* v_data_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(v___f_4683_, v___x_4684_, v_socket_4685_, v_data_4686_);
return v_res_4688_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_4694_; 
v___x_4694_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_4694_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_4695_; lean_object* v___f_4696_; lean_object* v___f_4697_; 
v___x_4695_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_4696_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___f_4697_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4697_, 0, v___f_4696_);
lean_closure_set(v___f_4697_, 1, v___x_4695_);
return v___f_4697_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___f_4698_; lean_object* v___f_4699_; lean_object* v___f_4700_; lean_object* v___x_4701_; 
v___f_4698_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_4699_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4);
v___f_4700_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___x_4701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4701_, 0, v___f_4700_);
lean_ctor_set(v___x_4701_, 1, v___f_4699_);
lean_ctor_set(v___x_4701_, 2, v___f_4698_);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4702_, lean_object* v_inst_4703_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4705_, lean_object* v_inst_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4705_, v_inst_4706_);
lean_dec(v_inst_4706_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4708_){
_start:
{
lean_inc_ref(v_ch_4708_);
return v_ch_4708_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l_Std_CloseableChannel_sync___redArg(v_ch_4709_);
lean_dec_ref(v_ch_4709_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4711_, lean_object* v_ch_4712_){
_start:
{
lean_inc_ref(v_ch_4712_);
return v_ch_4712_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4713_, lean_object* v_ch_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l_Std_CloseableChannel_sync(v_00_u03b1_4713_, v_ch_4714_);
lean_dec_ref(v_ch_4714_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4716_){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = l_Std_CloseableChannel_new___redArg(v_capacity_4716_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4719_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4722_, lean_object* v_capacity_4723_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Std_CloseableChannel_new___redArg(v_capacity_4723_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4726_, lean_object* v_capacity_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4726_, v_capacity_4727_);
return v_res_4729_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4730_, lean_object* v_v_4731_){
_start:
{
uint8_t v___x_4733_; 
v___x_4733_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4730_, v_v_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4734_, lean_object* v_v_4735_, lean_object* v_a_4736_){
_start:
{
uint8_t v_res_4737_; lean_object* v_r_4738_; 
v_res_4737_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4734_, v_v_4735_);
v_r_4738_ = lean_box(v_res_4737_);
return v_r_4738_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4739_, lean_object* v_ch_4740_, lean_object* v_v_4741_){
_start:
{
uint8_t v___x_4743_; 
v___x_4743_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4740_, v_v_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4744_, lean_object* v_ch_4745_, lean_object* v_v_4746_, lean_object* v_a_4747_){
_start:
{
uint8_t v_res_4748_; lean_object* v_r_4749_; 
v_res_4748_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4744_, v_ch_4745_, v_v_4746_);
v_r_4749_ = lean_box(v_res_4748_);
return v_r_4749_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4750_, lean_object* v_v_4751_){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = l_Std_CloseableChannel_send___redArg(v_ch_4750_, v_v_4751_);
v___x_4754_ = lean_io_wait(v___x_4753_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4754_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4754_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
lean_ctor_set_tag(v___x_4757_, 1);
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
v_a_4763_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4754_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4754_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
lean_ctor_set_tag(v___x_4765_, 0);
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_4771_, lean_object* v_v_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4771_, v_v_4772_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_4775_, lean_object* v_ch_4776_, lean_object* v_v_4777_){
_start:
{
lean_object* v___x_4779_; 
v___x_4779_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4776_, v_v_4777_);
return v___x_4779_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_4780_, lean_object* v_ch_4781_, lean_object* v_v_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_4780_, v_ch_4781_, v_v_4782_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_4785_){
_start:
{
lean_object* v___x_4787_; 
v___x_4787_ = l_Std_CloseableChannel_close___redArg(v_ch_4785_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_4788_, lean_object* v_a_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_4788_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_4791_, lean_object* v_ch_4792_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_Std_CloseableChannel_close___redArg(v_ch_4792_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_4795_, lean_object* v_ch_4796_, lean_object* v_a_4797_){
_start:
{
lean_object* v_res_4798_; 
v_res_4798_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_4795_, v_ch_4796_);
return v_res_4798_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_4799_){
_start:
{
uint8_t v___x_4801_; 
v___x_4801_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4799_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_4802_, lean_object* v_a_4803_){
_start:
{
uint8_t v_res_4804_; lean_object* v_r_4805_; 
v_res_4804_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_4802_);
v_r_4805_ = lean_box(v_res_4804_);
return v_r_4805_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_4806_, lean_object* v_ch_4807_){
_start:
{
uint8_t v___x_4809_; 
v___x_4809_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4807_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_4810_, lean_object* v_ch_4811_, lean_object* v_a_4812_){
_start:
{
uint8_t v_res_4813_; lean_object* v_r_4814_; 
v_res_4813_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_4810_, v_ch_4811_);
v_r_4814_ = lean_box(v_res_4813_);
return v_r_4814_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_4815_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4815_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_4818_, lean_object* v_a_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_4818_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_4821_, lean_object* v_ch_4822_){
_start:
{
lean_object* v___x_4824_; 
v___x_4824_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4822_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_4825_, lean_object* v_ch_4826_, lean_object* v_a_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_4825_, v_ch_4826_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_4829_){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4831_ = l_Std_CloseableChannel_recv___redArg(v_ch_4829_);
v___x_4832_ = lean_io_wait(v___x_4831_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_4833_, lean_object* v_a_4834_){
_start:
{
lean_object* v_res_4835_; 
v_res_4835_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4833_);
return v_res_4835_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_4836_, lean_object* v_ch_4837_){
_start:
{
lean_object* v___x_4839_; 
v___x_4839_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4837_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_4840_, lean_object* v_ch_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_4840_, v_ch_4841_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_4844_, lean_object* v_b_4845_, lean_object* v_f_4846_, lean_object* v_toBind_4847_, lean_object* v___f_4848_, lean_object* v_____do__lift_4849_){
_start:
{
if (lean_obj_tag(v_____do__lift_4849_) == 0)
{
lean_object* v___x_4850_; 
lean_dec(v___f_4848_);
lean_dec(v_toBind_4847_);
lean_dec(v_f_4846_);
v___x_4850_ = lean_apply_2(v_toPure_4844_, lean_box(0), v_b_4845_);
return v___x_4850_;
}
else
{
lean_object* v_val_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
lean_dec(v_toPure_4844_);
v_val_4851_ = lean_ctor_get(v_____do__lift_4849_, 0);
lean_inc(v_val_4851_);
lean_dec_ref_known(v_____do__lift_4849_, 1);
v___x_4852_ = lean_apply_2(v_f_4846_, v_val_4851_, v_b_4845_);
v___x_4853_ = lean_apply_4(v_toBind_4847_, lean_box(0), lean_box(0), v___x_4852_, v___f_4848_);
return v___x_4853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_4854_, lean_object* v_inst_4855_, lean_object* v_ch_4856_, lean_object* v_f_4857_, lean_object* v_b_4858_){
_start:
{
lean_object* v_toApplicative_4859_; lean_object* v_toBind_4860_; lean_object* v_toPure_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___f_4864_; lean_object* v___f_4865_; lean_object* v___x_4866_; 
v_toApplicative_4859_ = lean_ctor_get(v_inst_4854_, 0);
v_toBind_4860_ = lean_ctor_get(v_inst_4854_, 1);
lean_inc_n(v_toBind_4860_, 2);
v_toPure_4861_ = lean_ctor_get(v_toApplicative_4859_, 1);
lean_inc_n(v_toPure_4861_, 2);
lean_inc_ref(v_ch_4856_);
v___x_4862_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_4862_, 0, lean_box(0));
lean_closure_set(v___x_4862_, 1, v_ch_4856_);
lean_inc(v_inst_4855_);
v___x_4863_ = lean_apply_2(v_inst_4855_, lean_box(0), v___x_4862_);
lean_inc(v_f_4857_);
v___f_4864_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4864_, 0, v_toPure_4861_);
lean_closure_set(v___f_4864_, 1, v_inst_4854_);
lean_closure_set(v___f_4864_, 2, v_inst_4855_);
lean_closure_set(v___f_4864_, 3, v_ch_4856_);
lean_closure_set(v___f_4864_, 4, v_f_4857_);
v___f_4865_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_4865_, 0, v_toPure_4861_);
lean_closure_set(v___f_4865_, 1, v_b_4858_);
lean_closure_set(v___f_4865_, 2, v_f_4857_);
lean_closure_set(v___f_4865_, 3, v_toBind_4860_);
lean_closure_set(v___f_4865_, 4, v___f_4864_);
v___x_4866_ = lean_apply_4(v_toBind_4860_, lean_box(0), lean_box(0), v___x_4863_, v___f_4865_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_4867_, lean_object* v_inst_4868_, lean_object* v_inst_4869_, lean_object* v_ch_4870_, lean_object* v_f_4871_, lean_object* v_____do__lift_4872_){
_start:
{
if (lean_obj_tag(v_____do__lift_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4874_; 
lean_dec(v_f_4871_);
lean_dec_ref(v_ch_4870_);
lean_dec(v_inst_4869_);
lean_dec_ref(v_inst_4868_);
v_a_4873_ = lean_ctor_get(v_____do__lift_4872_, 0);
lean_inc(v_a_4873_);
lean_dec_ref_known(v_____do__lift_4872_, 1);
v___x_4874_ = lean_apply_2(v_toPure_4867_, lean_box(0), v_a_4873_);
return v___x_4874_;
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4876_; 
lean_dec(v_toPure_4867_);
v_a_4875_ = lean_ctor_get(v_____do__lift_4872_, 0);
lean_inc(v_a_4875_);
lean_dec_ref_known(v_____do__lift_4872_, 1);
v___x_4876_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4868_, v_inst_4869_, v_ch_4870_, v_f_4871_, v_a_4875_);
return v___x_4876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_4877_, lean_object* v_00_u03b1_4878_, lean_object* v_00_u03b2_4879_, lean_object* v_inst_4880_, lean_object* v_inst_4881_, lean_object* v_ch_4882_, lean_object* v_f_4883_, lean_object* v_b_4884_){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4880_, v_inst_4881_, v_ch_4882_, v_f_4883_, v_b_4884_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_4886_, lean_object* v_inst_4887_, lean_object* v_ch_4888_, lean_object* v_b_4889_, lean_object* v_f_4890_){
_start:
{
lean_object* v___x_4891_; 
v___x_4891_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4886_, v_inst_4887_, v_ch_4888_, v_f_4890_, v_b_4889_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_4892_, lean_object* v_00_u03b1_4893_, lean_object* v_inst_4894_, lean_object* v_inst_4895_, lean_object* v_00_u03b2_4896_, lean_object* v_ch_4897_, lean_object* v_b_4898_, lean_object* v_f_4899_){
_start:
{
lean_object* v___x_4900_; 
v___x_4900_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4894_, v_inst_4895_, v_ch_4897_, v_f_4899_, v_b_4898_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_4901_, lean_object* v_inst_4902_, lean_object* v_00_u03b2_4903_, lean_object* v_ch_4904_, lean_object* v_b_4905_, lean_object* v_f_4906_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4901_, v_inst_4902_, v_ch_4904_, v_f_4906_, v_b_4905_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_4908_, lean_object* v_inst_4909_){
_start:
{
lean_object* v___f_4910_; 
v___f_4910_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4910_, 0, v_inst_4908_);
lean_closure_set(v___f_4910_, 1, v_inst_4909_);
return v___f_4910_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_4911_, lean_object* v_00_u03b1_4912_, lean_object* v_inst_4913_, lean_object* v_inst_4914_){
_start:
{
lean_object* v___f_4915_; 
v___f_4915_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4915_, 0, v_inst_4913_);
lean_closure_set(v___f_4915_, 1, v_inst_4914_);
return v___f_4915_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_4916_){
_start:
{
lean_object* v___x_4918_; 
v___x_4918_ = l_Std_CloseableChannel_new___redArg(v_capacity_4916_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_4919_, lean_object* v_a_4920_){
_start:
{
lean_object* v_res_4921_; 
v_res_4921_ = l_Std_Channel_new___redArg(v_capacity_4919_);
return v_res_4921_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_4922_, lean_object* v_capacity_4923_){
_start:
{
lean_object* v___x_4925_; 
v___x_4925_ = l_Std_CloseableChannel_new___redArg(v_capacity_4923_);
return v___x_4925_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_4926_, lean_object* v_capacity_4927_, lean_object* v_a_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Std_Channel_new(v_00_u03b1_4926_, v_capacity_4927_);
return v_res_4929_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_4930_, lean_object* v_v_4931_){
_start:
{
uint8_t v___x_4933_; 
v___x_4933_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4930_, v_v_4931_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_4934_, lean_object* v_v_4935_, lean_object* v_a_4936_){
_start:
{
uint8_t v_res_4937_; lean_object* v_r_4938_; 
v_res_4937_ = l_Std_Channel_trySend___redArg(v_ch_4934_, v_v_4935_);
v_r_4938_ = lean_box(v_res_4937_);
return v_r_4938_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_4939_, lean_object* v_ch_4940_, lean_object* v_v_4941_){
_start:
{
uint8_t v___x_4943_; 
v___x_4943_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4940_, v_v_4941_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_4944_, lean_object* v_ch_4945_, lean_object* v_v_4946_, lean_object* v_a_4947_){
_start:
{
uint8_t v_res_4948_; lean_object* v_r_4949_; 
v_res_4948_ = l_Std_Channel_trySend(v_00_u03b1_4944_, v_ch_4945_, v_v_4946_);
v_r_4949_ = lean_box(v_res_4948_);
return v_r_4949_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; 
v___x_4950_ = lean_box(0);
v___x_4951_ = lean_task_pure(v___x_4950_);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_4952_){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_142__overap_4957_; lean_object* v___x_4958_; 
v___x_4954_ = l_instMonadBaseIO;
v___x_4955_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4956_ = l_instInhabitedOfMonad___redArg(v___x_4954_, v___x_4955_);
v___x_142__overap_4957_ = lean_panic_fn_borrowed(v___x_4956_, v_msg_4952_);
lean_dec(v___x_4956_);
v___x_4958_ = lean_apply_1(v___x_142__overap_4957_, lean_box(0));
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_4959_, lean_object* v___y_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_4959_);
return v_res_4961_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4965_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4966_ = lean_unsigned_to_nat(21u);
v___x_4967_ = lean_unsigned_to_nat(869u);
v___x_4968_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_4969_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4970_ = l_mkPanicMessageWithDecl(v___x_4969_, v___x_4968_, v___x_4967_, v___x_4966_, v___x_4965_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_4971_){
_start:
{
if (lean_obj_tag(v_x_4971_) == 0)
{
lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4973_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_4974_ = l_panic___at___00Std_Channel_send_spec__0(v___x_4973_);
return v___x_4974_;
}
else
{
lean_object* v___x_4975_; 
v___x_4975_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4975_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l_Std_Channel_send___redArg___lam__0(v_x_4976_);
lean_dec_ref(v_x_4976_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_4980_, lean_object* v_v_4981_){
_start:
{
lean_object* v___x_4983_; lean_object* v___f_4984_; lean_object* v___x_4985_; uint8_t v___x_4986_; lean_object* v___x_4987_; 
v___x_4983_ = l_Std_CloseableChannel_send___redArg(v_ch_4980_, v_v_4981_);
v___f_4984_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_4985_ = lean_unsigned_to_nat(0u);
v___x_4986_ = 1;
v___x_4987_ = lean_io_bind_task(v___x_4983_, v___f_4984_, v___x_4985_, v___x_4986_);
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_4988_, lean_object* v_v_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Std_Channel_send___redArg(v_ch_4988_, v_v_4989_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_4992_, lean_object* v_ch_4993_, lean_object* v_v_4994_){
_start:
{
lean_object* v___x_4996_; 
v___x_4996_ = l_Std_Channel_send___redArg(v_ch_4993_, v_v_4994_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_4997_, lean_object* v_ch_4998_, lean_object* v_v_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Std_Channel_send(v_00_u03b1_4997_, v_ch_4998_, v_v_4999_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_5002_){
_start:
{
lean_object* v___x_5004_; 
v___x_5004_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5002_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_5005_, lean_object* v_a_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Std_Channel_tryRecv___redArg(v_ch_5005_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_5008_, lean_object* v_ch_5009_){
_start:
{
lean_object* v___x_5011_; 
v___x_5011_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5009_);
return v___x_5011_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_5012_, lean_object* v_ch_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l_Std_Channel_tryRecv(v_00_u03b1_5012_, v_ch_5013_);
return v_res_5015_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5017_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_5018_ = lean_unsigned_to_nat(16u);
v___x_5019_ = lean_unsigned_to_nat(880u);
v___x_5020_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_5021_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_5022_ = l_mkPanicMessageWithDecl(v___x_5021_, v___x_5020_, v___x_5019_, v___x_5018_, v___x_5017_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_5023_, lean_object* v_x_5024_){
_start:
{
if (lean_obj_tag(v_x_5024_) == 0)
{
lean_object* v___x_5026_; lean_object* v___x_140__overap_5027_; lean_object* v___x_5028_; 
v___x_5026_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_140__overap_5027_ = l_panic___redArg(v___x_5023_, v___x_5026_);
v___x_5028_ = lean_apply_1(v___x_140__overap_5027_, lean_box(0));
return v___x_5028_;
}
else
{
lean_object* v_val_5029_; lean_object* v___x_5030_; 
v_val_5029_ = lean_ctor_get(v_x_5024_, 0);
lean_inc(v_val_5029_);
lean_dec_ref_known(v_x_5024_, 1);
v___x_5030_ = lean_task_pure(v_val_5029_);
return v___x_5030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_5031_, lean_object* v_x_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l_Std_Channel_recv___redArg___lam__0(v___x_5031_, v_x_5032_);
lean_dec_ref(v___x_5031_);
return v_res_5034_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_5035_, lean_object* v_ch_5036_){
_start:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___f_5042_; lean_object* v___x_5043_; uint8_t v___x_5044_; lean_object* v___x_5045_; 
v___x_5038_ = l_instMonadBaseIO;
v___x_5039_ = l_Std_CloseableChannel_recv___redArg(v_ch_5036_);
v___x_5040_ = lean_task_pure(v_inst_5035_);
v___x_5041_ = l_instInhabitedOfMonad___redArg(v___x_5038_, v___x_5040_);
v___f_5042_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5042_, 0, v___x_5041_);
v___x_5043_ = lean_unsigned_to_nat(0u);
v___x_5044_ = 1;
v___x_5045_ = lean_io_bind_task(v___x_5039_, v___f_5042_, v___x_5043_, v___x_5044_);
return v___x_5045_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_5046_, lean_object* v_ch_5047_, lean_object* v_a_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l_Std_Channel_recv___redArg(v_inst_5046_, v_ch_5047_);
return v_res_5049_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_5050_, lean_object* v_inst_5051_, lean_object* v_ch_5052_){
_start:
{
lean_object* v___x_5054_; 
v___x_5054_ = l_Std_Channel_recv___redArg(v_inst_5051_, v_ch_5052_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_5055_, lean_object* v_inst_5056_, lean_object* v_ch_5057_, lean_object* v_a_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l_Std_Channel_recv(v_00_u03b1_5055_, v_inst_5056_, v_ch_5057_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_5060_){
_start:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5062_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5060_);
v___x_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5062_);
v___x_5064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5063_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_5065_, lean_object* v___y_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5065_);
return v_res_5067_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5071_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_5072_ = lean_unsigned_to_nat(14u);
v___x_5073_ = lean_unsigned_to_nat(22u);
v___x_5074_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_5075_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_5076_ = l_mkPanicMessageWithDecl(v___x_5075_, v___x_5074_, v___x_5073_, v___x_5072_, v___x_5071_);
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_5077_, lean_object* v_inst_5078_, lean_object* v_x_5079_){
_start:
{
lean_object* v___y_5082_; lean_object* v___y_5086_; 
if (lean_obj_tag(v_x_5079_) == 0)
{
lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5088_ = lean_box(0);
v___x_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5089_, 0, v___x_5088_);
return v___x_5089_;
}
else
{
lean_object* v_val_5090_; 
v_val_5090_ = lean_ctor_get(v_x_5079_, 0);
lean_inc(v_val_5090_);
lean_dec_ref_known(v_x_5079_, 1);
if (lean_obj_tag(v_val_5090_) == 0)
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5098_; 
v_a_5091_ = lean_ctor_get(v_val_5090_, 0);
v_isSharedCheck_5098_ = !lean_is_exclusive(v_val_5090_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5093_ = v_val_5090_;
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v_val_5090_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5096_; 
if (v_isShared_5094_ == 0)
{
v___x_5096_ = v___x_5093_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5091_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
v___y_5082_ = v___x_5096_;
goto v___jp_5081_;
}
}
}
else
{
lean_object* v_a_5099_; 
v_a_5099_ = lean_ctor_get(v_val_5090_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v_val_5090_, 1);
if (lean_obj_tag(v_a_5099_) == 0)
{
lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5100_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5101_ = l_panic___redArg(v_inst_5078_, v___x_5100_);
v___y_5086_ = v___x_5101_;
goto v___jp_5085_;
}
else
{
lean_object* v_val_5102_; 
v_val_5102_ = lean_ctor_get(v_a_5099_, 0);
lean_inc(v_val_5102_);
lean_dec_ref_known(v_a_5099_, 1);
v___y_5086_ = v_val_5102_;
goto v___jp_5085_;
}
}
}
v___jp_5081_:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5083_ = lean_io_promise_resolve(v___y_5082_, v_promise_5077_);
v___x_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5084_, 0, v___x_5083_);
return v___x_5084_;
}
v___jp_5085_:
{
lean_object* v___x_5087_; 
v___x_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5087_, 0, v___y_5086_);
v___y_5082_ = v___x_5087_;
goto v___jp_5081_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5103_, lean_object* v_inst_5104_, lean_object* v_x_5105_, lean_object* v___y_5106_){
_start:
{
lean_object* v_res_5107_; 
v_res_5107_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5103_, v_inst_5104_, v_x_5105_);
lean_dec(v_inst_5104_);
lean_dec(v_promise_5103_);
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5108_, lean_object* v___f_5109_, lean_object* v_x_5110_){
_start:
{
lean_object* v_val_5113_; 
if (lean_obj_tag(v_x_5110_) == 0)
{
lean_object* v___x_5115_; 
lean_dec_ref(v___f_5109_);
v___x_5115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5115_, 0, v_x_5110_);
return v___x_5115_;
}
else
{
lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5131_; 
v_isSharedCheck_5131_ = !lean_is_exclusive(v_x_5110_);
if (v_isSharedCheck_5131_ == 0)
{
lean_object* v_unused_5132_; 
v_unused_5132_ = lean_ctor_get(v_x_5110_, 0);
lean_dec(v_unused_5132_);
v___x_5117_ = v_x_5110_;
v_isShared_5118_ = v_isSharedCheck_5131_;
goto v_resetjp_5116_;
}
else
{
lean_dec(v_x_5110_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5131_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5119_; lean_object* v___x_5120_; uint8_t v___x_5121_; lean_object* v___x_5122_; 
v___x_5119_ = lean_io_promise_result_opt(v_a_5108_);
v___x_5120_ = lean_unsigned_to_nat(0u);
v___x_5121_ = 1;
v___x_5122_ = l_EIO_chainTask___redArg(v___x_5119_, v___f_5109_, v___x_5120_, v___x_5121_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5125_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_a_5123_);
lean_dec_ref_known(v___x_5122_, 1);
if (v_isShared_5118_ == 0)
{
lean_ctor_set(v___x_5117_, 0, v_a_5123_);
v___x_5125_ = v___x_5117_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5123_);
v___x_5125_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
v_val_5113_ = v___x_5125_;
goto v___jp_5112_;
}
}
else
{
lean_object* v_a_5127_; lean_object* v___x_5129_; 
v_a_5127_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_a_5127_);
lean_dec_ref_known(v___x_5122_, 1);
if (v_isShared_5118_ == 0)
{
lean_ctor_set_tag(v___x_5117_, 0);
lean_ctor_set(v___x_5117_, 0, v_a_5127_);
v___x_5129_ = v___x_5117_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_a_5127_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
v_val_5113_ = v___x_5129_;
goto v___jp_5112_;
}
}
}
}
v___jp_5112_:
{
lean_object* v___x_5114_; 
v___x_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5114_, 0, v_val_5113_);
return v___x_5114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5133_, lean_object* v___f_5134_, lean_object* v_x_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v_res_5137_; 
v_res_5137_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5133_, v___f_5134_, v_x_5135_);
lean_dec(v_a_5133_);
return v_res_5137_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5138_, lean_object* v_finished_5139_, lean_object* v___f_5140_, lean_object* v_x_5141_){
_start:
{
if (lean_obj_tag(v_x_5141_) == 0)
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5151_; 
lean_dec_ref(v___f_5140_);
lean_dec(v_finished_5139_);
lean_dec_ref(v_sel_5138_);
v_a_5143_ = lean_ctor_get(v_x_5141_, 0);
v_isSharedCheck_5151_ = !lean_is_exclusive(v_x_5141_);
if (v_isSharedCheck_5151_ == 0)
{
v___x_5145_ = v_x_5141_;
v_isShared_5146_ = v_isSharedCheck_5151_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v_x_5141_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5151_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
lean_object* v___x_5149_; 
v___x_5149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5149_, 0, v___x_5148_);
return v___x_5149_;
}
}
}
else
{
lean_object* v_a_5152_; lean_object* v_registerFn_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___f_5156_; lean_object* v___x_5157_; uint8_t v___x_5158_; lean_object* v___x_5159_; 
v_a_5152_ = lean_ctor_get(v_x_5141_, 0);
lean_inc_n(v_a_5152_, 2);
lean_dec_ref_known(v_x_5141_, 1);
v_registerFn_5153_ = lean_ctor_get(v_sel_5138_, 1);
lean_inc_ref(v_registerFn_5153_);
lean_dec_ref(v_sel_5138_);
v___x_5154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5154_, 0, v_finished_5139_);
lean_ctor_set(v___x_5154_, 1, v_a_5152_);
v___x_5155_ = lean_apply_2(v_registerFn_5153_, v___x_5154_, lean_box(0));
v___f_5156_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5156_, 0, v_a_5152_);
lean_closure_set(v___f_5156_, 1, v___f_5140_);
v___x_5157_ = lean_unsigned_to_nat(0u);
v___x_5158_ = 0;
v___x_5159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5157_, v___x_5158_, v___x_5155_, v___f_5156_);
return v___x_5159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5160_, lean_object* v_finished_5161_, lean_object* v___f_5162_, lean_object* v_x_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v_res_5165_; 
v_res_5165_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5160_, v_finished_5161_, v___f_5162_, v_x_5163_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5166_, lean_object* v_sel_5167_, lean_object* v_waiter_5168_){
_start:
{
lean_object* v___x_5170_; lean_object* v_finished_5171_; lean_object* v_promise_5172_; lean_object* v___f_5173_; lean_object* v___f_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; uint8_t v___x_5178_; lean_object* v___x_5179_; 
v___x_5170_ = lean_io_promise_new();
v_finished_5171_ = lean_ctor_get(v_waiter_5168_, 0);
lean_inc(v_finished_5171_);
v_promise_5172_ = lean_ctor_get(v_waiter_5168_, 1);
lean_inc(v_promise_5172_);
lean_dec_ref(v_waiter_5168_);
v___f_5173_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5173_, 0, v_promise_5172_);
lean_closure_set(v___f_5173_, 1, v_inst_5166_);
v___f_5174_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5174_, 0, v_sel_5167_);
lean_closure_set(v___f_5174_, 1, v_finished_5171_);
lean_closure_set(v___f_5174_, 2, v___f_5173_);
v___x_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5175_, 0, v___x_5170_);
v___x_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5175_);
v___x_5177_ = lean_unsigned_to_nat(0u);
v___x_5178_ = 0;
v___x_5179_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5177_, v___x_5178_, v___x_5176_, v___f_5174_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5180_, lean_object* v_sel_5181_, lean_object* v_waiter_5182_, lean_object* v___y_5183_){
_start:
{
lean_object* v_res_5184_; 
v_res_5184_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5180_, v_sel_5181_, v_waiter_5182_);
return v_res_5184_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5185_, lean_object* v_ch_5186_){
_start:
{
lean_object* v_sel_5187_; lean_object* v_unregisterFn_5188_; lean_object* v___f_5189_; lean_object* v___f_5190_; lean_object* v___x_5191_; 
lean_inc_ref(v_ch_5186_);
v_sel_5187_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5186_);
v_unregisterFn_5188_ = lean_ctor_get(v_sel_5187_, 2);
lean_inc_ref(v_unregisterFn_5188_);
v___f_5189_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5189_, 0, v_ch_5186_);
v___f_5190_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5190_, 0, v_inst_5185_);
lean_closure_set(v___f_5190_, 1, v_sel_5187_);
v___x_5191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5191_, 0, v___f_5189_);
lean_ctor_set(v___x_5191_, 1, v___f_5190_);
lean_ctor_set(v___x_5191_, 2, v_unregisterFn_5188_);
return v___x_5191_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5192_, lean_object* v_inst_5193_, lean_object* v_ch_5194_){
_start:
{
lean_object* v___x_5195_; 
v___x_5195_ = l_Std_Channel_recvSelector___redArg(v_inst_5193_, v_ch_5194_);
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5196_, lean_object* v_inst_5197_, lean_object* v_ch_5198_, lean_object* v_prio_5199_, lean_object* v_v_5200_, lean_object* v___y_5201_){
_start:
{
lean_object* v_res_5202_; 
v_res_5202_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5196_, v_inst_5197_, v_ch_5198_, v_prio_5199_, v_v_5200_);
return v_res_5202_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5203_, lean_object* v_f_5204_, lean_object* v_ch_5205_, lean_object* v_prio_5206_){
_start:
{
lean_object* v___x_5208_; lean_object* v___f_5209_; uint8_t v___x_5210_; lean_object* v___x_5211_; 
lean_inc_ref(v_ch_5205_);
lean_inc(v_inst_5203_);
v___x_5208_ = l_Std_Channel_recv___redArg(v_inst_5203_, v_ch_5205_);
lean_inc(v_prio_5206_);
v___f_5209_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5209_, 0, v_f_5204_);
lean_closure_set(v___f_5209_, 1, v_inst_5203_);
lean_closure_set(v___f_5209_, 2, v_ch_5205_);
lean_closure_set(v___f_5209_, 3, v_prio_5206_);
v___x_5210_ = 0;
v___x_5211_ = lean_io_bind_task(v___x_5208_, v___f_5209_, v_prio_5206_, v___x_5210_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5212_, lean_object* v_inst_5213_, lean_object* v_ch_5214_, lean_object* v_prio_5215_, lean_object* v_v_5216_){
_start:
{
lean_object* v___x_5218_; lean_object* v___x_5219_; 
lean_inc_ref(v_f_5212_);
v___x_5218_ = lean_apply_2(v_f_5212_, v_v_5216_, lean_box(0));
v___x_5219_ = l_Std_Channel_forAsync___redArg(v_inst_5213_, v_f_5212_, v_ch_5214_, v_prio_5215_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5220_, lean_object* v_f_5221_, lean_object* v_ch_5222_, lean_object* v_prio_5223_, lean_object* v_a_5224_){
_start:
{
lean_object* v_res_5225_; 
v_res_5225_ = l_Std_Channel_forAsync___redArg(v_inst_5220_, v_f_5221_, v_ch_5222_, v_prio_5223_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5226_, lean_object* v_inst_5227_, lean_object* v_f_5228_, lean_object* v_ch_5229_, lean_object* v_prio_5230_){
_start:
{
lean_object* v___x_5232_; 
v___x_5232_ = l_Std_Channel_forAsync___redArg(v_inst_5227_, v_f_5228_, v_ch_5229_, v_prio_5230_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5233_, lean_object* v_inst_5234_, lean_object* v_f_5235_, lean_object* v_ch_5236_, lean_object* v_prio_5237_, lean_object* v_a_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l_Std_Channel_forAsync(v_00_u03b1_5233_, v_inst_5234_, v_f_5235_, v_ch_5236_, v_prio_5237_);
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5240_, lean_object* v_channel_5241_){
_start:
{
lean_object* v___x_5242_; 
v___x_5242_ = l_Std_Channel_recvSelector___redArg(v_inst_5240_, v_channel_5241_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5243_){
_start:
{
lean_object* v___f_5244_; lean_object* v___f_5245_; lean_object* v___x_5246_; 
v___f_5244_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5244_, 0, v_inst_5243_);
v___f_5245_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1));
v___x_5246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5246_, 0, v___f_5244_);
lean_ctor_set(v___x_5246_, 1, v___f_5245_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5247_, lean_object* v_inst_5248_){
_start:
{
lean_object* v___x_5249_; 
v___x_5249_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5248_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5250_){
_start:
{
lean_object* v___x_5251_; 
v___x_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5251_, 0, v_a_5250_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5252_, lean_object* v_x_5253_){
_start:
{
if (lean_obj_tag(v_x_5253_) == 0)
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5263_; 
lean_dec_ref(v___f_5252_);
v_a_5255_ = lean_ctor_get(v_x_5253_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v_x_5253_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5257_ = v_x_5253_;
v_isShared_5258_ = v_isSharedCheck_5263_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v_x_5253_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5263_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5260_; 
if (v_isShared_5258_ == 0)
{
v___x_5260_ = v___x_5257_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5255_);
v___x_5260_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
lean_object* v___x_5261_; 
v___x_5261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
return v___x_5261_;
}
}
}
else
{
lean_object* v_a_5264_; 
v_a_5264_ = lean_ctor_get(v_x_5253_, 0);
lean_inc(v_a_5264_);
lean_dec_ref_known(v_x_5253_, 1);
if (lean_obj_tag(v_a_5264_) == 0)
{
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5273_; 
lean_dec_ref(v___f_5252_);
v_a_5265_ = lean_ctor_get(v_a_5264_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v_a_5264_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5267_ = v_a_5264_;
v_isShared_5268_ = v_isSharedCheck_5273_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v_a_5264_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5273_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5270_; 
if (v_isShared_5268_ == 0)
{
v___x_5270_ = v___x_5267_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5265_);
v___x_5270_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
lean_object* v___x_5271_; 
v___x_5271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5271_, 0, v___x_5270_);
return v___x_5271_;
}
}
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5275_; uint8_t v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v_a_5274_ = lean_ctor_get(v_a_5264_, 0);
lean_inc(v_a_5274_);
lean_dec_ref_known(v_a_5264_, 1);
v___x_5275_ = lean_unsigned_to_nat(0u);
v___x_5276_ = 0;
v___x_5277_ = lean_task_map(v___f_5252_, v_a_5274_, v___x_5275_, v___x_5276_);
v___x_5278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5277_);
return v___x_5278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5279_, lean_object* v_x_5280_, lean_object* v___y_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5279_, v_x_5280_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5283_, lean_object* v___f_5284_, lean_object* v_receiver_5285_){
_start:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; uint8_t v___x_5292_; lean_object* v___x_5293_; 
v___x_5287_ = l_Std_Channel_recv___redArg(v_inst_5283_, v_receiver_5285_);
v___x_5288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5288_, 0, v___x_5287_);
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
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5294_, lean_object* v___f_5295_, lean_object* v_receiver_5296_, lean_object* v___y_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5294_, v___f_5295_, v_receiver_5296_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5302_){
_start:
{
lean_object* v___f_5303_; lean_object* v___f_5304_; 
v___f_5303_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5304_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5304_, 0, v_inst_5302_);
lean_closure_set(v___f_5304_, 1, v___f_5303_);
return v___f_5304_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5305_, lean_object* v_inst_5306_){
_start:
{
lean_object* v___x_5307_; 
v___x_5307_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5306_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__0(lean_object* v_a_5308_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5309_, 0, v_a_5308_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_5310_, lean_object* v_x_5311_){
_start:
{
if (lean_obj_tag(v_x_5311_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5321_; 
lean_dec_ref(v___f_5310_);
v_a_5313_ = lean_ctor_get(v_x_5311_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v_x_5311_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5315_ = v_x_5311_;
v_isShared_5316_ = v_isSharedCheck_5321_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v_x_5311_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5321_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v___x_5318_; 
if (v_isShared_5316_ == 0)
{
v___x_5318_ = v___x_5315_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_a_5313_);
v___x_5318_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
lean_object* v___x_5319_; 
v___x_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5319_, 0, v___x_5318_);
return v___x_5319_;
}
}
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5323_; uint8_t v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; 
v_a_5322_ = lean_ctor_get(v_x_5311_, 0);
lean_inc(v_a_5322_);
lean_dec_ref_known(v_x_5311_, 1);
v___x_5323_ = lean_unsigned_to_nat(0u);
v___x_5324_ = 0;
v___x_5325_ = lean_task_map(v___f_5310_, v_a_5322_, v___x_5323_, v___x_5324_);
v___x_5326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5326_, 0, v___x_5325_);
return v___x_5326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_5327_, lean_object* v_x_5328_, lean_object* v___y_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__1(v___f_5327_, v_x_5328_);
return v_res_5330_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5331_, lean_object* v_receiver_5332_, lean_object* v_x_5333_){
_start:
{
lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; uint8_t v___x_5339_; lean_object* v___x_5340_; 
v___x_5335_ = l_Std_Channel_send___redArg(v_receiver_5332_, v_x_5333_);
v___x_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5336_, 0, v___x_5335_);
v___x_5337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5336_);
v___x_5338_ = lean_unsigned_to_nat(0u);
v___x_5339_ = 0;
v___x_5340_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5338_, v___x_5339_, v___x_5337_, v___f_5331_);
return v___x_5340_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5341_, lean_object* v_receiver_5342_, lean_object* v_x_5343_, lean_object* v___y_5344_){
_start:
{
lean_object* v_res_5345_; 
v_res_5345_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__2(v___f_5341_, v_receiver_5342_, v_x_5343_);
return v_res_5345_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_5351_; lean_object* v___f_5352_; lean_object* v___f_5353_; 
v___x_5351_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_5352_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___f_5353_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5353_, 0, v___f_5352_);
lean_closure_set(v___f_5353_, 1, v___x_5351_);
return v___f_5353_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___f_5354_; lean_object* v___f_5355_; lean_object* v___f_5356_; lean_object* v___x_5357_; 
v___f_5354_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_5355_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3);
v___f_5356_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___x_5357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5357_, 0, v___f_5356_);
lean_ctor_set(v___x_5357_, 1, v___f_5355_);
lean_ctor_set(v___x_5357_, 2, v___f_5354_);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5358_, lean_object* v_inst_5359_){
_start:
{
lean_object* v___x_5360_; 
v___x_5360_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4);
return v___x_5360_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5361_, lean_object* v_inst_5362_){
_start:
{
lean_object* v_res_5363_; 
v_res_5363_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_5361_, v_inst_5362_);
lean_dec(v_inst_5362_);
return v_res_5363_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object* v_ch_5364_){
_start:
{
lean_inc_ref(v_ch_5364_);
return v_ch_5364_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object* v_ch_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_Std_Channel_sync___redArg(v_ch_5365_);
lean_dec_ref(v_ch_5365_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object* v_00_u03b1_5367_, lean_object* v_ch_5368_){
_start:
{
lean_inc_ref(v_ch_5368_);
return v_ch_5368_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object* v_00_u03b1_5369_, lean_object* v_ch_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l_Std_Channel_sync(v_00_u03b1_5369_, v_ch_5370_);
lean_dec_ref(v_ch_5370_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg(lean_object* v_capacity_5372_){
_start:
{
lean_object* v___x_5374_; 
v___x_5374_ = l_Std_CloseableChannel_new___redArg(v_capacity_5372_);
return v___x_5374_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object* v_capacity_5375_, lean_object* v_a_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Std_Channel_Sync_new___redArg(v_capacity_5375_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new(lean_object* v_00_u03b1_5378_, lean_object* v_capacity_5379_){
_start:
{
lean_object* v___x_5381_; 
v___x_5381_ = l_Std_CloseableChannel_new___redArg(v_capacity_5379_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object* v_00_u03b1_5382_, lean_object* v_capacity_5383_, lean_object* v_a_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l_Std_Channel_Sync_new(v_00_u03b1_5382_, v_capacity_5383_);
return v_res_5385_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object* v_ch_5386_, lean_object* v_v_5387_){
_start:
{
uint8_t v___x_5389_; 
v___x_5389_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5386_, v_v_5387_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object* v_ch_5390_, lean_object* v_v_5391_, lean_object* v_a_5392_){
_start:
{
uint8_t v_res_5393_; lean_object* v_r_5394_; 
v_res_5393_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5390_, v_v_5391_);
v_r_5394_ = lean_box(v_res_5393_);
return v_r_5394_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend(lean_object* v_00_u03b1_5395_, lean_object* v_ch_5396_, lean_object* v_v_5397_){
_start:
{
uint8_t v___x_5399_; 
v___x_5399_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5396_, v_v_5397_);
return v___x_5399_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object* v_00_u03b1_5400_, lean_object* v_ch_5401_, lean_object* v_v_5402_, lean_object* v_a_5403_){
_start:
{
uint8_t v_res_5404_; lean_object* v_r_5405_; 
v_res_5404_ = l_Std_Channel_Sync_trySend(v_00_u03b1_5400_, v_ch_5401_, v_v_5402_);
v_r_5405_ = lean_box(v_res_5404_);
return v_r_5405_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg(lean_object* v_ch_5406_, lean_object* v_v_5407_){
_start:
{
lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5409_ = l_Std_Channel_send___redArg(v_ch_5406_, v_v_5407_);
v___x_5410_ = lean_io_wait(v___x_5409_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object* v_ch_5411_, lean_object* v_v_5412_, lean_object* v_a_5413_){
_start:
{
lean_object* v_res_5414_; 
v_res_5414_ = l_Std_Channel_Sync_send___redArg(v_ch_5411_, v_v_5412_);
return v_res_5414_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send(lean_object* v_00_u03b1_5415_, lean_object* v_ch_5416_, lean_object* v_v_5417_){
_start:
{
lean_object* v___x_5419_; 
v___x_5419_ = l_Std_Channel_Sync_send___redArg(v_ch_5416_, v_v_5417_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object* v_00_u03b1_5420_, lean_object* v_ch_5421_, lean_object* v_v_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Std_Channel_Sync_send(v_00_u03b1_5420_, v_ch_5421_, v_v_5422_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object* v_ch_5425_){
_start:
{
lean_object* v___x_5427_; 
v___x_5427_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5425_);
return v___x_5427_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5428_, lean_object* v_a_5429_){
_start:
{
lean_object* v_res_5430_; 
v_res_5430_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5428_);
return v_res_5430_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv(lean_object* v_00_u03b1_5431_, lean_object* v_ch_5432_){
_start:
{
lean_object* v___x_5434_; 
v___x_5434_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5432_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5435_, lean_object* v_ch_5436_, lean_object* v_a_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_5435_, v_ch_5436_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg(lean_object* v_inst_5439_, lean_object* v_ch_5440_){
_start:
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = l_Std_Channel_recv___redArg(v_inst_5439_, v_ch_5440_);
v___x_5443_ = lean_io_wait(v___x_5442_);
return v___x_5443_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object* v_inst_5444_, lean_object* v_ch_5445_, lean_object* v_a_5446_){
_start:
{
lean_object* v_res_5447_; 
v_res_5447_ = l_Std_Channel_Sync_recv___redArg(v_inst_5444_, v_ch_5445_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv(lean_object* v_00_u03b1_5448_, lean_object* v_inst_5449_, lean_object* v_ch_5450_){
_start:
{
lean_object* v___x_5452_; 
v___x_5452_ = l_Std_Channel_Sync_recv___redArg(v_inst_5449_, v_ch_5450_);
return v___x_5452_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object* v_00_u03b1_5453_, lean_object* v_inst_5454_, lean_object* v_ch_5455_, lean_object* v_a_5456_){
_start:
{
lean_object* v_res_5457_; 
v_res_5457_ = l_Std_Channel_Sync_recv(v_00_u03b1_5453_, v_inst_5454_, v_ch_5455_);
return v_res_5457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object* v_f_5458_, lean_object* v_b_5459_, lean_object* v_toBind_5460_, lean_object* v___f_5461_, lean_object* v_a_5462_){
_start:
{
lean_object* v___x_5463_; lean_object* v___x_5464_; 
v___x_5463_ = lean_apply_2(v_f_5458_, v_a_5462_, v_b_5459_);
v___x_5464_ = lean_apply_4(v_toBind_5460_, lean_box(0), lean_box(0), v___x_5463_, v___f_5461_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object* v_inst_5465_, lean_object* v_inst_5466_, lean_object* v_inst_5467_, lean_object* v_ch_5468_, lean_object* v_f_5469_, lean_object* v_b_5470_){
_start:
{
lean_object* v_toApplicative_5471_; lean_object* v_toBind_5472_; lean_object* v_toPure_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___f_5476_; lean_object* v___f_5477_; lean_object* v___x_5478_; 
v_toApplicative_5471_ = lean_ctor_get(v_inst_5466_, 0);
v_toBind_5472_ = lean_ctor_get(v_inst_5466_, 1);
lean_inc_n(v_toBind_5472_, 2);
v_toPure_5473_ = lean_ctor_get(v_toApplicative_5471_, 1);
lean_inc(v_toPure_5473_);
lean_inc_ref(v_ch_5468_);
lean_inc(v_inst_5465_);
v___x_5474_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_recv___boxed), 4, 3);
lean_closure_set(v___x_5474_, 0, lean_box(0));
lean_closure_set(v___x_5474_, 1, v_inst_5465_);
lean_closure_set(v___x_5474_, 2, v_ch_5468_);
lean_inc(v_inst_5467_);
v___x_5475_ = lean_apply_2(v_inst_5467_, lean_box(0), v___x_5474_);
lean_inc(v_f_5469_);
v___f_5476_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5476_, 0, v_toPure_5473_);
lean_closure_set(v___f_5476_, 1, v_inst_5465_);
lean_closure_set(v___f_5476_, 2, v_inst_5466_);
lean_closure_set(v___f_5476_, 3, v_inst_5467_);
lean_closure_set(v___f_5476_, 4, v_ch_5468_);
lean_closure_set(v___f_5476_, 5, v_f_5469_);
v___f_5477_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1), 5, 4);
lean_closure_set(v___f_5477_, 0, v_f_5469_);
lean_closure_set(v___f_5477_, 1, v_b_5470_);
lean_closure_set(v___f_5477_, 2, v_toBind_5472_);
lean_closure_set(v___f_5477_, 3, v___f_5476_);
v___x_5478_ = lean_apply_4(v_toBind_5472_, lean_box(0), lean_box(0), v___x_5475_, v___f_5477_);
return v___x_5478_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5479_, lean_object* v_inst_5480_, lean_object* v_inst_5481_, lean_object* v_inst_5482_, lean_object* v_ch_5483_, lean_object* v_f_5484_, lean_object* v_____do__lift_5485_){
_start:
{
if (lean_obj_tag(v_____do__lift_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v___x_5487_; 
lean_dec(v_f_5484_);
lean_dec_ref(v_ch_5483_);
lean_dec(v_inst_5482_);
lean_dec_ref(v_inst_5481_);
lean_dec(v_inst_5480_);
v_a_5486_ = lean_ctor_get(v_____do__lift_5485_, 0);
lean_inc(v_a_5486_);
lean_dec_ref_known(v_____do__lift_5485_, 1);
v___x_5487_ = lean_apply_2(v_toPure_5479_, lean_box(0), v_a_5486_);
return v___x_5487_;
}
else
{
lean_object* v_a_5488_; lean_object* v___x_5489_; 
lean_dec(v_toPure_5479_);
v_a_5488_ = lean_ctor_get(v_____do__lift_5485_, 0);
lean_inc(v_a_5488_);
lean_dec_ref_known(v_____do__lift_5485_, 1);
v___x_5489_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5480_, v_inst_5481_, v_inst_5482_, v_ch_5483_, v_f_5484_, v_a_5488_);
return v___x_5489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object* v_00_u03b1_5490_, lean_object* v_m_5491_, lean_object* v_00_u03b2_5492_, lean_object* v_inst_5493_, lean_object* v_inst_5494_, lean_object* v_inst_5495_, lean_object* v_ch_5496_, lean_object* v_f_5497_, lean_object* v_b_5498_){
_start:
{
lean_object* v___x_5499_; 
v___x_5499_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5493_, v_inst_5494_, v_inst_5495_, v_ch_5496_, v_f_5497_, v_b_5498_);
return v___x_5499_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5500_, lean_object* v_inst_5501_, lean_object* v_inst_5502_, lean_object* v_ch_5503_, lean_object* v_b_5504_, lean_object* v_f_5505_){
_start:
{
lean_object* v___x_5506_; 
v___x_5506_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5500_, v_inst_5501_, v_inst_5502_, v_ch_5503_, v_f_5505_, v_b_5504_);
return v___x_5506_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_00_u03b1_5507_, lean_object* v_m_5508_, lean_object* v_inst_5509_, lean_object* v_inst_5510_, lean_object* v_inst_5511_, lean_object* v_00_u03b2_5512_, lean_object* v_ch_5513_, lean_object* v_b_5514_, lean_object* v_f_5515_){
_start:
{
lean_object* v___x_5516_; 
v___x_5516_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5509_, v_inst_5510_, v_inst_5511_, v_ch_5513_, v_f_5515_, v_b_5514_);
return v___x_5516_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5517_, lean_object* v_inst_5518_, lean_object* v_inst_5519_, lean_object* v_00_u03b2_5520_, lean_object* v_ch_5521_, lean_object* v_b_5522_, lean_object* v_f_5523_){
_start:
{
lean_object* v___x_5524_; 
v___x_5524_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5517_, v_inst_5518_, v_inst_5519_, v_ch_5521_, v_f_5523_, v_b_5522_);
return v___x_5524_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5525_, lean_object* v_inst_5526_, lean_object* v_inst_5527_){
_start:
{
lean_object* v___f_5528_; 
v___f_5528_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5528_, 0, v_inst_5525_);
lean_closure_set(v___f_5528_, 1, v_inst_5526_);
lean_closure_set(v___f_5528_, 2, v_inst_5527_);
return v___f_5528_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5529_, lean_object* v_m_5530_, lean_object* v_inst_5531_, lean_object* v_inst_5532_, lean_object* v_inst_5533_){
_start:
{
lean_object* v___f_5534_; 
v___f_5534_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5534_, 0, v_inst_5531_);
lean_closure_set(v___f_5534_, 1, v_inst_5532_);
lean_closure_set(v___f_5534_, 2, v_inst_5533_);
return v___f_5534_;
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

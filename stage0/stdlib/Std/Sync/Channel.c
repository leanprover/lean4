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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_mapError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_x_20__boxed_103_; uint8_t v_y_21__boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_x_20__boxed_103_ = lean_unbox(v_x_101_);
v_y_21__boxed_104_ = lean_unbox(v_y_102_);
v_res_105_ = l_Std_CloseableChannel_instDecidableEqError(v_x_20__boxed_103_, v_y_21__boxed_104_);
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
uint8_t v___x_406__boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v___x_406__boxed_253_ = lean_unbox(v___x_251_);
v_res_254_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(v___x_406__boxed_253_);
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
v___x_284_ = l_Std_Queue_empty___redArg();
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
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_values_328_; lean_object* v_consumers_329_; uint8_t v_closed_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_356_; 
v___x_326_ = lean_box(0);
v___x_327_ = lean_st_ref_get(v___y_324_);
v_values_328_ = lean_ctor_get(v___x_327_, 0);
v_consumers_329_ = lean_ctor_get(v___x_327_, 1);
v_closed_330_ = lean_ctor_get_uint8(v___x_327_, sizeof(void*)*2);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_356_ == 0)
{
v___x_332_ = v___x_327_;
v_isShared_333_ = v_isSharedCheck_356_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_consumers_329_);
lean_inc(v_values_328_);
lean_dec(v___x_327_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_356_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; 
lean_inc_ref(v_consumers_329_);
v___x_334_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_329_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_consumers_329_);
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
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_snd_340_);
v___x_345_ = v___x_332_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_values_328_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_snd_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_348_, sizeof(void*)*2, v_closed_330_);
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
return v___x_326_;
}
}
}
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_353_; 
lean_dec(v___x_334_);
v___x_351_ = l_Std_Queue_enqueue___redArg(v_v_323_, v_values_328_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_351_);
v___x_353_ = v___x_332_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_consumers_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*2, v_closed_330_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = lean_st_ref_swap(v___y_324_, v___x_353_);
lean_dec(v___x_354_);
return v___x_326_;
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
uint8_t v___x_366_; lean_object* v___x_367_; 
v___x_366_ = 1;
v___x_367_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_361_, v___y_362_);
return v___x_366_;
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
lean_object* v___x_487_; lean_object* v_a_488_; lean_object* v___x_489_; uint8_t v___x_490_; size_t v___x_491_; size_t v___x_492_; 
v___x_487_ = lean_box(0);
v_a_488_ = lean_array_uget_borrowed(v_as_480_, v_i_482_);
v___x_489_ = lean_box(0);
v___x_490_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_488_, v___x_489_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_482_, v___x_491_);
v_i_482_ = v___x_492_;
v_b_483_ = v___x_487_;
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; uint8_t v_closed_505_; 
v___x_504_ = lean_st_ref_get(v___y_502_);
v_closed_505_ = lean_ctor_get_uint8(v___x_504_, sizeof(void*)*2);
if (v_closed_505_ == 0)
{
lean_object* v_values_506_; lean_object* v_consumers_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_530_; 
v_values_506_ = lean_ctor_get(v___x_504_, 0);
v_consumers_507_ = lean_ctor_get(v___x_504_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_530_ == 0)
{
v___x_509_ = v___x_504_;
v_isShared_510_ = v_isSharedCheck_530_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_consumers_507_);
lean_inc(v_values_506_);
lean_dec(v___x_504_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_530_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; size_t v_sz_513_; size_t v___x_514_; lean_object* v___x_515_; 
v___x_511_ = l_Std_Queue_toArray___redArg(v_consumers_507_);
v___x_512_ = lean_box(0);
v_sz_513_ = lean_array_size(v___x_511_);
v___x_514_ = ((size_t)0ULL);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v___x_511_, v_sz_513_, v___x_514_, v___x_512_);
lean_dec_ref(v___x_511_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_528_; 
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v___x_515_, 0);
lean_dec(v_unused_529_);
v___x_517_ = v___x_515_;
v_isShared_518_ = v_isSharedCheck_528_;
goto v_resetjp_516_;
}
else
{
lean_dec(v___x_515_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_528_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_520_ = 1;
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_519_);
v___x_522_ = v___x_509_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_values_506_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_519_);
v___x_522_ = v_reuseFailAlloc_527_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*2, v___x_520_);
v___x_523_ = lean_st_ref_swap(v___y_502_, v___x_522_);
lean_dec(v___x_523_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_512_);
v___x_525_ = v___x_517_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_512_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_del_object(v___x_509_);
lean_dec_ref(v_values_506_);
return v___x_515_;
}
}
}
else
{
uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v___x_504_);
v___x_531_ = 1;
v___x_532_ = lean_box(v___x_531_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___boxed(lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(v___y_534_);
lean_dec(v___y_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(lean_object* v_ch_538_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_541_; 
v___f_540_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0));
v___x_541_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_538_, v___f_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___boxed(lean_object* v_ch_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(lean_object* v_00_u03b1_545_, lean_object* v_ch_546_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___boxed(lean_object* v_00_u03b1_549_, lean_object* v_ch_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(v_00_u03b1_549_, v_ch_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(lean_object* v_00_u03b1_553_, lean_object* v_as_554_, size_t v_sz_555_, size_t v_i_556_, lean_object* v_b_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_554_, v_sz_555_, v_i_556_, v_b_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___boxed(lean_object* v_00_u03b1_561_, lean_object* v_as_562_, lean_object* v_sz_563_, lean_object* v_i_564_, lean_object* v_b_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
size_t v_sz_boxed_568_; size_t v_i_boxed_569_; lean_object* v_res_570_; 
v_sz_boxed_568_ = lean_unbox_usize(v_sz_563_);
lean_dec(v_sz_563_);
v_i_boxed_569_ = lean_unbox_usize(v_i_564_);
lean_dec(v_i_564_);
v_res_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(v_00_u03b1_561_, v_as_562_, v_sz_boxed_568_, v_i_boxed_569_, v_b_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v_as_562_);
return v_res_570_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; uint8_t v_closed_574_; 
v___x_573_ = lean_st_ref_get(v___y_571_);
v_closed_574_ = lean_ctor_get_uint8(v___x_573_, sizeof(void*)*2);
lean_dec(v___x_573_);
return v_closed_574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v_res_577_; lean_object* v_r_578_; 
v_res_577_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(v___y_575_);
lean_dec(v___y_575_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(lean_object* v_ch_580_){
_start:
{
lean_object* v___f_582_; lean_object* v___x_583_; 
v___f_582_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0));
v___x_583_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_580_, v___f_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___boxed(lean_object* v_ch_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_584_);
return v_res_586_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(lean_object* v_00_u03b1_587_, lean_object* v_ch_588_){
_start:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_588_);
v___x_591_ = lean_unbox(v___x_590_);
lean_dec(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___boxed(lean_object* v_00_u03b1_592_, lean_object* v_ch_593_, lean_object* v_a_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(v_00_u03b1_592_, v_ch_593_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_597_, lean_object* v_fst_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_toPure_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_toPure_600_ = lean_ctor_get(v_toApplicative_597_, 1);
lean_inc(v_toPure_600_);
lean_dec_ref(v_toApplicative_597_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_fst_598_);
v___x_602_ = lean_apply_2(v_toPure_600_, lean_box(0), v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_603_, lean_object* v_a_604_, lean_object* v_inst_605_, lean_object* v_toBind_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_values_608_; lean_object* v_consumers_609_; uint8_t v_closed_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_628_; 
v_values_608_ = lean_ctor_get(v_a_607_, 0);
v_consumers_609_ = lean_ctor_get(v_a_607_, 1);
v_closed_610_ = lean_ctor_get_uint8(v_a_607_, sizeof(void*)*2);
v_isSharedCheck_628_ = !lean_is_exclusive(v_a_607_);
if (v_isSharedCheck_628_ == 0)
{
v___x_612_ = v_a_607_;
v_isShared_613_ = v_isSharedCheck_628_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_consumers_609_);
lean_inc(v_values_608_);
lean_dec(v_a_607_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_628_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_Queue_dequeue_x3f___redArg(v_values_608_);
if (lean_obj_tag(v___x_614_) == 1)
{
lean_object* v_val_615_; lean_object* v_fst_616_; lean_object* v_snd_617_; lean_object* v___f_618_; lean_object* v___x_620_; 
v_val_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_val_615_);
lean_dec_ref_known(v___x_614_, 1);
v_fst_616_ = lean_ctor_get(v_val_615_, 0);
lean_inc(v_fst_616_);
v_snd_617_ = lean_ctor_get(v_val_615_, 1);
lean_inc(v_snd_617_);
lean_dec(v_val_615_);
v___f_618_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_618_, 0, v_toApplicative_603_);
lean_closure_set(v___f_618_, 1, v_fst_616_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v_snd_617_);
v___x_620_ = v___x_612_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_snd_617_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_consumers_609_);
lean_ctor_set_uint8(v_reuseFailAlloc_624_, sizeof(void*)*2, v_closed_610_);
v___x_620_ = v_reuseFailAlloc_624_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_inc(v_a_604_);
v___x_621_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_621_, 0, lean_box(0));
lean_closure_set(v___x_621_, 1, lean_box(0));
lean_closure_set(v___x_621_, 2, v_a_604_);
lean_closure_set(v___x_621_, 3, v___x_620_);
v___x_622_ = lean_apply_2(v_inst_605_, lean_box(0), v___x_621_);
v___x_623_ = lean_apply_4(v_toBind_606_, lean_box(0), lean_box(0), v___x_622_, v___f_618_);
return v___x_623_;
}
}
else
{
lean_object* v_toPure_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec(v___x_614_);
lean_del_object(v___x_612_);
lean_dec_ref(v_consumers_609_);
lean_dec(v_toBind_606_);
lean_dec(v_inst_605_);
v_toPure_625_ = lean_ctor_get(v_toApplicative_603_, 1);
lean_inc(v_toPure_625_);
lean_dec_ref(v_toApplicative_603_);
v___x_626_ = lean_box(0);
v___x_627_ = lean_apply_2(v_toPure_625_, lean_box(0), v___x_626_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_629_, lean_object* v_a_630_, lean_object* v_inst_631_, lean_object* v_toBind_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(v_toApplicative_629_, v_a_630_, v_inst_631_, v_toBind_632_, v_a_633_);
lean_dec(v_a_630_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_toApplicative_638_; lean_object* v_toBind_639_; lean_object* v___f_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_toApplicative_638_ = lean_ctor_get(v_inst_635_, 0);
lean_inc_ref(v_toApplicative_638_);
v_toBind_639_ = lean_ctor_get(v_inst_635_, 1);
lean_inc_n(v_toBind_639_, 2);
lean_dec_ref(v_inst_635_);
lean_inc(v_inst_636_);
lean_inc_n(v_a_637_, 2);
v___f_640_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_640_, 0, v_toApplicative_638_);
lean_closure_set(v___f_640_, 1, v_a_637_);
lean_closure_set(v___f_640_, 2, v_inst_636_);
lean_closure_set(v___f_640_, 3, v_toBind_639_);
v___x_641_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_641_, 0, lean_box(0));
lean_closure_set(v___x_641_, 1, lean_box(0));
lean_closure_set(v___x_641_, 2, v_a_637_);
v___x_642_ = lean_apply_2(v_inst_636_, lean_box(0), v___x_641_);
v___x_643_ = lean_apply_4(v_toBind_639_, lean_box(0), lean_box(0), v___x_642_, v___f_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_644_, v_inst_645_, v_a_646_);
lean_dec(v_a_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(lean_object* v_m_648_, lean_object* v_00_u03b1_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_650_, v_inst_651_, v_a_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___boxed(lean_object* v_m_654_, lean_object* v_00_u03b1_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(v_m_654_, v_00_u03b1_655_, v_inst_656_, v_inst_657_, v_a_658_);
lean_dec(v_a_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; lean_object* v_values_663_; lean_object* v_consumers_664_; uint8_t v_closed_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_685_; 
v___x_662_ = lean_st_ref_get(v_a_660_);
v_values_663_ = lean_ctor_get(v___x_662_, 0);
v_consumers_664_ = lean_ctor_get(v___x_662_, 1);
v_closed_665_ = lean_ctor_get_uint8(v___x_662_, sizeof(void*)*2);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_685_ == 0)
{
v___x_667_ = v___x_662_;
v_isShared_668_ = v_isSharedCheck_685_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_consumers_664_);
lean_inc(v_values_663_);
lean_dec(v___x_662_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_685_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_Queue_dequeue_x3f___redArg(v_values_663_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_683_; 
v_val_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_683_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_683_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_683_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___x_677_; 
v_fst_674_ = lean_ctor_get(v_val_670_, 0);
lean_inc(v_fst_674_);
v_snd_675_ = lean_ctor_get(v_val_670_, 1);
lean_inc(v_snd_675_);
lean_dec(v_val_670_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v_snd_675_);
v___x_677_ = v___x_667_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_snd_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_consumers_664_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*2, v_closed_665_);
v___x_677_ = v_reuseFailAlloc_682_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_st_ref_swap(v_a_660_, v___x_677_);
lean_dec(v___x_678_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_fst_674_);
v___x_680_ = v___x_672_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_fst_674_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v___x_684_; 
lean_dec(v___x_669_);
lean_del_object(v___x_667_);
lean_dec_ref(v_consumers_664_);
v___x_684_ = lean_box(0);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_686_);
lean_dec(v_a_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(lean_object* v_00_u03b1_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_693_, lean_object* v_a_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(v_00_u03b1_693_, v_a_694_);
lean_dec(v_a_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(lean_object* v_ch_698_){
_start:
{
lean_object* v___f_700_; lean_object* v___x_701_; 
v___f_700_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0));
v___x_701_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_698_, v___f_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___boxed(lean_object* v_ch_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(lean_object* v_00_u03b1_705_, lean_object* v_ch_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___boxed(lean_object* v_00_u03b1_709_, lean_object* v_ch_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(v_00_u03b1_709_, v_ch_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(lean_object* v_x_713_){
_start:
{
if (lean_obj_tag(v_x_713_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_box(0);
return v___x_714_;
}
else
{
lean_object* v_val_715_; 
v_val_715_ = lean_ctor_get(v_x_713_, 0);
lean_inc(v_val_715_);
return v_val_715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed(lean_object* v_x_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(v_x_716_);
lean_dec(v_x_716_);
return v_res_717_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_box(0);
v___x_719_ = lean_task_pure(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(lean_object* v___f_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v___y_721_);
if (lean_obj_tag(v___x_723_) == 1)
{
lean_object* v___x_724_; 
lean_dec_ref(v___f_720_);
v___x_724_ = lean_task_pure(v___x_723_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; uint8_t v_closed_726_; 
lean_dec(v___x_723_);
v___x_725_ = lean_st_ref_get(v___y_721_);
v_closed_726_ = lean_ctor_get_uint8(v___x_725_, sizeof(void*)*2);
lean_dec(v___x_725_);
if (v_closed_726_ == 0)
{
uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_values_730_; lean_object* v_consumers_731_; uint8_t v_closed_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_745_; 
v___x_727_ = 1;
v___x_728_ = lean_io_promise_new();
v___x_729_ = lean_st_ref_take(v___y_721_);
v_values_730_ = lean_ctor_get(v___x_729_, 0);
v_consumers_731_ = lean_ctor_get(v___x_729_, 1);
v_closed_732_ = lean_ctor_get_uint8(v___x_729_, sizeof(void*)*2);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_745_ == 0)
{
v___x_734_ = v___x_729_;
v_isShared_735_ = v_isSharedCheck_745_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_consumers_731_);
lean_inc(v_values_730_);
lean_dec(v___x_729_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_745_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
lean_inc(v___x_728_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_728_);
v___x_737_ = l_Std_Queue_enqueue___redArg(v___x_736_, v_consumers_731_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_737_);
v___x_739_ = v___x_734_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_values_730_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_744_, sizeof(void*)*2, v_closed_732_);
v___x_739_ = v_reuseFailAlloc_744_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = lean_st_ref_put(v___y_721_, v___x_739_);
v___x_741_ = lean_io_promise_result_opt(v___x_728_);
lean_dec(v___x_728_);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_task_map(v___f_720_, v___x_741_, v___x_742_, v___x_727_);
return v___x_743_;
}
}
}
else
{
lean_object* v___x_746_; 
lean_dec_ref(v___f_720_);
v___x_746_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed(lean_object* v___f_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(v___f_747_, v___y_748_);
lean_dec(v___y_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(lean_object* v_ch_754_){
_start:
{
lean_object* v___f_756_; lean_object* v___x_757_; 
v___f_756_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1));
v___x_757_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_754_, v___f_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___boxed(lean_object* v_ch_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(lean_object* v_00_u03b1_761_, lean_object* v_ch_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___boxed(lean_object* v_00_u03b1_765_, lean_object* v_ch_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(v_00_u03b1_765_, v_ch_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_769_, lean_object* v_a_770_){
_start:
{
uint8_t v___y_772_; lean_object* v_values_776_; uint8_t v_closed_777_; uint8_t v___x_778_; 
v_values_776_ = lean_ctor_get(v_a_770_, 0);
v_closed_777_ = lean_ctor_get_uint8(v_a_770_, sizeof(void*)*2);
v___x_778_ = l_Std_Queue_isEmpty___redArg(v_values_776_);
if (v___x_778_ == 0)
{
uint8_t v___x_779_; 
v___x_779_ = 1;
v___y_772_ = v___x_779_;
goto v___jp_771_;
}
else
{
v___y_772_ = v_closed_777_;
goto v___jp_771_;
}
v___jp_771_:
{
lean_object* v_toPure_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_toPure_773_ = lean_ctor_get(v_toApplicative_769_, 1);
lean_inc(v_toPure_773_);
lean_dec_ref(v_toApplicative_769_);
v___x_774_ = lean_box(v___y_772_);
v___x_775_ = lean_apply_2(v_toPure_773_, lean_box(0), v___x_774_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(v_toApplicative_780_, v_a_781_);
lean_dec_ref(v_a_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_toApplicative_786_; lean_object* v_toBind_787_; lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_toApplicative_786_ = lean_ctor_get(v_inst_783_, 0);
lean_inc_ref(v_toApplicative_786_);
v_toBind_787_ = lean_ctor_get(v_inst_783_, 1);
lean_inc(v_toBind_787_);
lean_dec_ref(v_inst_783_);
v___f_788_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_788_, 0, v_toApplicative_786_);
lean_inc(v_a_785_);
v___x_789_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_789_, 0, lean_box(0));
lean_closure_set(v___x_789_, 1, lean_box(0));
lean_closure_set(v___x_789_, 2, v_a_785_);
v___x_790_ = lean_apply_2(v_inst_784_, lean_box(0), v___x_789_);
v___x_791_ = lean_apply_4(v_toBind_787_, lean_box(0), lean_box(0), v___x_790_, v___f_788_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___boxed(lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(v_inst_792_, v_inst_793_, v_a_794_);
lean_dec(v_a_794_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(lean_object* v_m_796_, lean_object* v_00_u03b1_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_toApplicative_801_; lean_object* v_toBind_802_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_toApplicative_801_ = lean_ctor_get(v_inst_798_, 0);
lean_inc_ref(v_toApplicative_801_);
v_toBind_802_ = lean_ctor_get(v_inst_798_, 1);
lean_inc(v_toBind_802_);
lean_dec_ref(v_inst_798_);
v___f_803_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_803_, 0, v_toApplicative_801_);
lean_inc(v_a_800_);
v___x_804_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_804_, 0, lean_box(0));
lean_closure_set(v___x_804_, 1, lean_box(0));
lean_closure_set(v___x_804_, 2, v_a_800_);
v___x_805_ = lean_apply_2(v_inst_799_, lean_box(0), v___x_804_);
v___x_806_ = lean_apply_4(v_toBind_802_, lean_box(0), lean_box(0), v___x_805_, v___f_803_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___boxed(lean_object* v_m_807_, lean_object* v_00_u03b1_808_, lean_object* v_inst_809_, lean_object* v_inst_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(v_m_807_, v_00_u03b1_808_, v_inst_809_, v_inst_810_, v_a_811_);
lean_dec(v_a_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_fst_813_, lean_object* v_x_814_){
_start:
{
if (lean_obj_tag(v_x_814_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_fst_813_);
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
lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_833_; 
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_814_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v_x_814_, 0);
lean_dec(v_unused_834_);
v___x_826_ = v_x_814_;
v_isShared_827_ = v_isSharedCheck_833_;
goto v_resetjp_825_;
}
else
{
lean_dec(v_x_814_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_833_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v_fst_813_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_828_);
v___x_830_ = v___x_826_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_835_, lean_object* v_x_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(v_fst_835_, v_x_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_847_, lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_858_; 
v_a_850_ = lean_ctor_get(v_x_848_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_x_848_);
if (v_isSharedCheck_858_ == 0)
{
v___x_852_ = v_x_848_;
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v_x_848_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_857_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; 
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v_values_860_; lean_object* v_consumers_861_; uint8_t v_closed_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_880_; 
v_a_859_ = lean_ctor_get(v_x_848_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v_x_848_, 1);
v_values_860_ = lean_ctor_get(v_a_859_, 0);
v_consumers_861_ = lean_ctor_get(v_a_859_, 1);
v_closed_862_ = lean_ctor_get_uint8(v_a_859_, sizeof(void*)*2);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_859_);
if (v_isSharedCheck_880_ == 0)
{
v___x_864_ = v_a_859_;
v_isShared_865_ = v_isSharedCheck_880_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_consumers_861_);
lean_inc(v_values_860_);
lean_dec(v_a_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_880_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; 
v___x_866_ = l_Std_Queue_dequeue_x3f___redArg(v_values_860_);
if (lean_obj_tag(v___x_866_) == 1)
{
lean_object* v_val_867_; lean_object* v_fst_868_; lean_object* v_snd_869_; lean_object* v___f_870_; lean_object* v___x_872_; 
v_val_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v___x_866_, 1);
v_fst_868_ = lean_ctor_get(v_val_867_, 0);
lean_inc(v_fst_868_);
v_snd_869_ = lean_ctor_get(v_val_867_, 1);
lean_inc(v_snd_869_);
lean_dec(v_val_867_);
v___f_870_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_870_, 0, v_fst_868_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v_snd_869_);
v___x_872_ = v___x_864_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_snd_869_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_consumers_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_878_, sizeof(void*)*2, v_closed_862_);
v___x_872_ = v_reuseFailAlloc_878_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = 0;
v___x_875_ = lean_st_ref_swap(v_a_847_, v___x_872_);
lean_dec(v___x_875_);
v___x_876_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_877_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_873_, v___x_874_, v___x_876_, v___f_870_);
return v___x_877_;
}
}
else
{
lean_object* v___x_879_; 
lean_dec(v___x_866_);
lean_del_object(v___x_864_);
lean_dec_ref(v_consumers_861_);
v___x_879_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_881_, lean_object* v_x_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_881_, v_x_882_);
lean_dec(v_a_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(lean_object* v_a_885_){
_start:
{
lean_object* v___f_887_; lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_inc(v_a_885_);
v___f_887_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_887_, 0, v_a_885_);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = 0;
v___x_890_ = lean_st_ref_get(v_a_885_);
v___x_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
v___x_893_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_888_, v___x_889_, v___x_892_, v___f_887_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_894_);
lean_dec(v_a_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_object* v_00_u03b1_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_901_, lean_object* v_a_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(v_00_u03b1_901_, v_a_902_);
lean_dec(v_a_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_promise_905_, lean_object* v_x_906_){
_start:
{
if (lean_obj_tag(v_x_906_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_a_908_ = lean_ctor_get(v_x_906_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v_x_906_);
if (v_isSharedCheck_916_ == 0)
{
v___x_910_ = v_x_906_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v_x_906_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_915_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_io_promise_resolve(v_x_906_, v_promise_905_);
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_promise_920_, lean_object* v_x_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_920_, v_x_921_);
lean_dec(v_promise_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_924_, lean_object* v___y_925_, lean_object* v___f_926_, lean_object* v_x_927_){
_start:
{
if (lean_obj_tag(v_x_927_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_937_; 
lean_dec_ref(v___f_926_);
lean_dec_ref(v_lose_924_);
v_a_929_ = lean_ctor_get(v_x_927_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_937_ == 0)
{
v___x_931_ = v_x_927_;
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v_x_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_936_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
else
{
lean_object* v_a_938_; uint8_t v___x_939_; 
v_a_938_ = lean_ctor_get(v_x_927_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v_x_927_, 1);
v___x_939_ = lean_unbox(v_a_938_);
lean_dec(v_a_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_dec_ref(v___f_926_);
lean_inc(v___y_925_);
v___x_940_ = lean_apply_2(v_lose_924_, v___y_925_, lean_box(0));
return v___x_940_;
}
else
{
lean_object* v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec_ref(v_lose_924_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = 0;
v___x_943_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_925_);
v___x_944_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_941_, v___x_942_, v___x_943_, v___f_926_);
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_945_, lean_object* v___y_946_, lean_object* v___f_947_, lean_object* v_x_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_945_, v___y_946_, v___f_947_, v_x_948_);
lean_dec(v___y_946_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object* v_w_951_, lean_object* v_lose_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_finished_955_; lean_object* v_promise_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; uint8_t v___y_963_; uint8_t v___x_971_; 
v_finished_955_ = lean_ctor_get(v_w_951_, 0);
lean_inc(v_finished_955_);
v_promise_956_ = lean_ctor_get(v_w_951_, 1);
lean_inc(v_promise_956_);
lean_dec_ref(v_w_951_);
v___f_957_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_957_, 0, v_promise_956_);
lean_inc(v___y_953_);
v___f_958_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_958_, 0, v_lose_952_);
lean_closure_set(v___f_958_, 1, v___y_953_);
lean_closure_set(v___f_958_, 2, v___f_957_);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = 0;
v___x_961_ = lean_st_ref_take(v_finished_955_);
v___x_971_ = lean_unbox(v___x_961_);
lean_dec(v___x_961_);
if (v___x_971_ == 0)
{
uint8_t v___x_972_; 
v___x_972_ = 1;
v___y_963_ = v___x_972_;
goto v___jp_962_;
}
else
{
v___y_963_ = v___x_960_;
goto v___jp_962_;
}
v___jp_962_:
{
uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_964_ = 1;
v___x_965_ = lean_box(v___x_964_);
v___x_966_ = lean_st_ref_put(v_finished_955_, v___x_965_);
lean_dec(v_finished_955_);
v___x_967_ = lean_box(v___y_963_);
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_959_, v___x_960_, v___x_969_, v___f_958_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object* v_w_973_, lean_object* v_lose_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_973_, v_lose_974_, v___y_975_);
lean_dec(v___y_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object* v_00_u03b1_978_, lean_object* v_w_979_, lean_object* v_lose_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_979_, v_lose_980_, v___y_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_984_, lean_object* v_w_985_, lean_object* v_lose_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(v_00_u03b1_984_, v_w_985_, v_lose_986_, v___y_987_);
lean_dec(v___y_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object* v___y_990_){
_start:
{
if (lean_obj_tag(v___y_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___y_990_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___y_990_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___y_990_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___y_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1007_; 
v_a_999_ = lean_ctor_get(v___y_990_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___y_990_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1001_ = v___y_990_;
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___y_990_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_fst_1003_; lean_object* v___x_1005_; 
v_fst_1003_ = lean_ctor_get(v_a_999_, 0);
lean_inc(v_fst_1003_);
lean_dec(v_a_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_fst_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_fst_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object* v_mutex_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_io_basemutex_unlock(v_mutex_1008_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_1014_, lean_object* v_x_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_mutex_1014_, v_x_1015_);
lean_dec(v_x_1015_);
lean_dec(v_mutex_1014_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object* v_k_1018_, lean_object* v_ref_1019_, lean_object* v_x_1020_){
_start:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_ref_1019_);
lean_dec_ref(v_k_1018_);
v_a_1022_ = lean_ctor_get(v_x_1020_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_x_1020_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v_x_1020_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v_x_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
}
else
{
lean_object* v___x_1031_; 
lean_dec_ref_known(v_x_1020_, 1);
v___x_1031_ = lean_apply_2(v_k_1018_, v_ref_1019_, lean_box(0));
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_k_1032_, lean_object* v_ref_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_k_1032_, v_ref_1033_, v_x_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object* v_mutex_1037_, lean_object* v___f_1038_){
_start:
{
lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = 0;
v___x_1042_ = lean_io_basemutex_lock(v_mutex_1037_);
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
v___x_1045_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1040_, v___x_1041_, v___x_1044_, v___f_1038_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_1046_, lean_object* v___f_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(v_mutex_1046_, v___f_1047_);
lean_dec(v_mutex_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(lean_object* v_mutex_1051_, lean_object* v_k_1052_){
_start:
{
lean_object* v_ref_1054_; lean_object* v_mutex_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___y_1064_; 
v_ref_1054_ = lean_ctor_get(v_mutex_1051_, 0);
lean_inc(v_ref_1054_);
v_mutex_1055_ = lean_ctor_get(v_mutex_1051_, 1);
lean_inc_n(v_mutex_1055_, 2);
lean_dec_ref(v_mutex_1051_);
v___f_1056_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0));
v___f_1057_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1057_, 0, v_mutex_1055_);
v___f_1058_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1058_, 0, v_k_1052_);
lean_closure_set(v___f_1058_, 1, v_ref_1054_);
v___f_1059_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1059_, 0, v_mutex_1055_);
lean_closure_set(v___f_1059_, 1, v___f_1058_);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = 0;
v___x_1062_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1059_, v___f_1057_, v___x_1060_, v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1066_; 
v_a_1066_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1062_, 1);
if (lean_obj_tag(v_a_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v_a_1066_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_a_1066_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v_a_1066_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v_a_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
v___y_1064_ = v___x_1072_;
goto v___jp_1063_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_a_1075_ = lean_ctor_get(v_a_1066_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_a_1066_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1077_ = v_a_1066_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v_a_1066_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_fst_1079_; lean_object* v___x_1081_; 
v_fst_1079_ = lean_ctor_get(v_a_1075_, 0);
lean_inc(v_fst_1079_);
lean_dec(v_a_1075_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v_fst_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_fst_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
v___y_1064_ = v___x_1081_;
goto v___jp_1063_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1092_; 
v_a_1084_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1086_ = v___x_1062_;
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1062_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = lean_task_map(v___f_1056_, v_a_1084_, v___x_1060_, v___x_1061_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
v___jp_1063_:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___y_1064_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_1093_, lean_object* v_k_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1093_, v_k_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_object* v_00_u03b1_1097_, lean_object* v_00_u03b2_1098_, lean_object* v_mutex_1099_, lean_object* v_k_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1099_, v_k_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_1103_, lean_object* v_00_u03b2_1104_, lean_object* v_mutex_1105_, lean_object* v_k_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(v_00_u03b1_1103_, v_00_u03b2_1104_, v_mutex_1105_, v_k_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1119_; 
v_a_1111_ = lean_ctor_get(v_x_1109_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1113_ = v_x_1109_;
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v_x_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1129_; 
v_a_1120_ = lean_ctor_get(v_x_1109_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1122_ = v_x_1109_;
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v_x_1109_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(lean_object* v_x_1133_){
_start:
{
uint8_t v___y_1136_; 
if (lean_obj_tag(v_x_1133_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1148_; 
v_a_1140_ = lean_ctor_get(v_x_1133_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1142_ = v_x_1133_;
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v_x_1133_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v_values_1150_; uint8_t v_closed_1151_; uint8_t v___x_1152_; 
v_a_1149_ = lean_ctor_get(v_x_1133_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v_x_1133_, 1);
v_values_1150_ = lean_ctor_get(v_a_1149_, 0);
lean_inc_ref(v_values_1150_);
v_closed_1151_ = lean_ctor_get_uint8(v_a_1149_, sizeof(void*)*2);
lean_dec(v_a_1149_);
v___x_1152_ = l_Std_Queue_isEmpty___redArg(v_values_1150_);
lean_dec_ref(v_values_1150_);
if (v___x_1152_ == 0)
{
uint8_t v___x_1153_; 
v___x_1153_ = 1;
v___y_1136_ = v___x_1153_;
goto v___jp_1135_;
}
else
{
v___y_1136_ = v_closed_1151_;
goto v___jp_1135_;
}
}
v___jp_1135_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_box(v___y_1136_);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(lean_object* v_x_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(lean_object* v___x_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1157_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_1162_, v___y_1163_);
lean_dec(v___y_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(lean_object* v___y_1168_, lean_object* v_waiter_1169_, lean_object* v_x_1170_){
_start:
{
if (lean_obj_tag(v_x_1170_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_waiter_1169_);
v_a_1172_ = lean_ctor_get(v_x_1170_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_x_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1174_ = v_x_1170_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v_x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
else
{
lean_object* v_a_1181_; uint8_t v___x_1182_; 
v_a_1181_ = lean_ctor_get(v_x_1170_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v_x_1170_, 1);
v___x_1182_ = lean_unbox(v_a_1181_);
lean_dec(v_a_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v_values_1184_; lean_object* v_consumers_1185_; uint8_t v_closed_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1197_; 
v___x_1183_ = lean_st_ref_take(v___y_1168_);
v_values_1184_ = lean_ctor_get(v___x_1183_, 0);
v_consumers_1185_ = lean_ctor_get(v___x_1183_, 1);
v_closed_1186_ = lean_ctor_get_uint8(v___x_1183_, sizeof(void*)*2);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1188_ = v___x_1183_;
v_isShared_1189_ = v_isSharedCheck_1197_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_consumers_1185_);
lean_inc(v_values_1184_);
lean_dec(v___x_1183_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1197_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_waiter_1169_);
v___x_1191_ = l_Std_Queue_enqueue___redArg(v___x_1190_, v_consumers_1185_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___x_1191_);
v___x_1193_ = v___x_1188_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_values_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*2, v_closed_1186_);
v___x_1193_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_st_ref_put(v___y_1168_, v___x_1193_);
v___x_1195_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_1195_;
}
}
}
else
{
lean_object* v_lose_1198_; lean_object* v___x_1199_; 
v_lose_1198_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0));
v___x_1199_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_waiter_1169_, v_lose_1198_, v___y_1168_);
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(lean_object* v___y_1200_, lean_object* v_waiter_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_1200_, v_waiter_1201_, v_x_1202_);
lean_dec(v___y_1200_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(lean_object* v_waiter_1205_, lean_object* v___f_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___f_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_inc(v___y_1207_);
v___f_1209_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1209_, 0, v___y_1207_);
lean_closure_set(v___f_1209_, 1, v_waiter_1205_);
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = 0;
v___x_1212_ = lean_st_ref_get(v___y_1207_);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___x_1215_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1210_, v___x_1211_, v___x_1214_, v___f_1206_);
v___x_1216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1210_, v___x_1211_, v___x_1215_, v___f_1209_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(lean_object* v_waiter_1217_, lean_object* v___f_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v_waiter_1217_, v___f_1218_, v___y_1219_);
lean_dec(v___y_1219_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(lean_object* v___f_1222_, lean_object* v_ch_1223_, lean_object* v_waiter_1224_){
_start:
{
lean_object* v___f_1226_; lean_object* v___x_1227_; 
v___f_1226_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1226_, 0, v_waiter_1224_);
lean_closure_set(v___f_1226_, 1, v___f_1222_);
v___x_1227_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_1223_, v___f_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(lean_object* v___f_1228_, lean_object* v_ch_1229_, lean_object* v_waiter_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_1228_, v_ch_1229_, v_waiter_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(lean_object* v___y_1237_, lean_object* v___f_1238_, lean_object* v_x_1239_){
_start:
{
if (lean_obj_tag(v_x_1239_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v___f_1238_);
v_a_1241_ = lean_ctor_get(v_x_1239_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1239_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1243_ = v_x_1239_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v_x_1239_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
}
}
else
{
lean_object* v_a_1250_; uint8_t v___x_1251_; 
v_a_1250_ = lean_ctor_get(v_x_1239_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v_x_1239_, 1);
v___x_1251_ = lean_unbox(v_a_1250_);
lean_dec(v_a_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v___f_1238_);
v___x_1252_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; uint8_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = 0;
v___x_1255_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_1237_);
v___x_1256_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1253_, v___x_1254_, v___x_1255_, v___f_1238_);
return v___x_1256_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(lean_object* v___y_1257_, lean_object* v___f_1258_, lean_object* v_x_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_1257_, v___f_1258_, v_x_1259_);
lean_dec(v___y_1257_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(lean_object* v___f_1262_, lean_object* v___f_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___f_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_inc(v___y_1264_);
v___f_1266_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1266_, 0, v___y_1264_);
lean_closure_set(v___f_1266_, 1, v___f_1262_);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = 0;
v___x_1269_ = lean_st_ref_get(v___y_1264_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
v___x_1272_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1267_, v___x_1268_, v___x_1271_, v___f_1263_);
v___x_1273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1267_, v___x_1268_, v___x_1272_, v___f_1266_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(lean_object* v___f_1274_, lean_object* v___f_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_1274_, v___f_1275_, v___y_1276_);
lean_dec(v___y_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(lean_object* v_values_1279_, uint8_t v_closed_1280_, lean_object* v___y_1281_, lean_object* v_x_1282_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_values_1279_);
v_a_1284_ = lean_ctor_get(v_x_1282_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_x_1282_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1286_ = v_x_1282_;
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v_x_1282_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_a_1293_ = lean_ctor_get(v_x_1282_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v_x_1282_, 1);
v___x_1294_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1294_, 0, v_values_1279_);
lean_ctor_set(v___x_1294_, 1, v_a_1293_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*2, v_closed_1280_);
v___x_1295_ = lean_st_ref_swap(v___y_1281_, v___x_1294_);
lean_dec(v___x_1295_);
v___x_1296_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed(lean_object* v_values_1297_, lean_object* v_closed_1298_, lean_object* v___y_1299_, lean_object* v_x_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v_closed_boxed_1302_; lean_object* v_res_1303_; 
v_closed_boxed_1302_ = lean_unbox(v_closed_1298_);
v_res_1303_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(v_values_1297_, v_closed_boxed_1302_, v___y_1299_, v_x_1300_);
lean_dec(v___y_1299_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_1304_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v_x_1304_);
return v___x_1306_;
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1316_; 
v_a_1307_ = lean_ctor_get(v_x_1304_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_x_1304_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1309_ = v_x_1304_;
v_isShared_1310_ = v_isSharedCheck_1316_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v_x_1304_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1316_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = l_List_reverse___redArg(v_a_1307_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(v_x_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_1320_, lean_object* v___x_1321_, lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v___x_1321_);
lean_dec(v_a_1320_);
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
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1349_; 
v_a_1333_ = lean_ctor_get(v_x_1322_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1335_ = v_x_1322_;
v_isShared_1336_ = v_isSharedCheck_1349_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v_x_1322_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1349_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
uint8_t v___x_1337_; 
v___x_1337_ = l_List_isEmpty___redArg(v_a_1320_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec(v___x_1321_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_a_1333_);
lean_ctor_set(v___x_1338_, 1, v_a_1320_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1338_);
v___x_1340_ = v___x_1335_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_dec(v_a_1320_);
v___x_1343_ = l_List_reverse___redArg(v_a_1333_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1321_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1344_);
v___x_1346_ = v___x_1335_;
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
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_1350_, lean_object* v___x_1351_, lean_object* v_x_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(v_a_1350_, v___x_1351_, v_x_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(lean_object* v_x_1355_){
_start:
{
uint8_t v___y_1358_; 
if (lean_obj_tag(v_x_1355_) == 0)
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_x_1355_);
return v___x_1362_;
}
else
{
lean_object* v_a_1363_; uint8_t v___x_1364_; 
v_a_1363_ = lean_ctor_get(v_x_1355_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v_x_1355_, 1);
v___x_1364_ = lean_unbox(v_a_1363_);
lean_dec(v_a_1363_);
if (v___x_1364_ == 0)
{
uint8_t v___x_1365_; 
v___x_1365_ = 1;
v___y_1358_ = v___x_1365_;
goto v___jp_1357_;
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = 0;
v___y_1358_ = v___x_1366_;
goto v___jp_1357_;
}
}
v___jp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_box(v___y_1358_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(lean_object* v_x_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_tail_1370_, lean_object* v_x_1371_, lean_object* v_head_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_1370_, v_x_1371_, v_head_1372_, v_x_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(lean_object* v_x_1382_, lean_object* v_x_1383_){
_start:
{
if (lean_obj_tag(v_x_1382_) == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v_x_1383_);
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
else
{
lean_object* v_head_1387_; lean_object* v_tail_1388_; lean_object* v___f_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v_head_1387_ = lean_ctor_get(v_x_1382_, 0);
lean_inc_n(v_head_1387_, 2);
v_tail_1388_ = lean_ctor_get(v_x_1382_, 1);
lean_inc(v_tail_1388_);
lean_dec_ref_known(v_x_1382_, 2);
v___f_1389_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1389_, 0, v_tail_1388_);
lean_closure_set(v___f_1389_, 1, v_x_1383_);
lean_closure_set(v___f_1389_, 2, v_head_1387_);
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = 0;
if (lean_obj_tag(v_head_1387_) == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref_known(v_head_1387_, 1);
v___x_1392_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_1393_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1390_, v___x_1391_, v___x_1392_, v___f_1389_);
return v___x_1393_;
}
else
{
lean_object* v_finished_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1407_; 
v_finished_1394_ = lean_ctor_get(v_head_1387_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_head_1387_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1396_ = v_head_1387_;
v_isShared_1397_ = v_isSharedCheck_1407_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_finished_1394_);
lean_dec(v_head_1387_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1407_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_finished_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v_finished_1398_ = lean_ctor_get(v_finished_1394_, 0);
lean_inc(v_finished_1398_);
lean_dec_ref(v_finished_1394_);
v___f_1399_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_1400_ = lean_st_ref_get(v_finished_1398_);
lean_dec(v_finished_1398_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1400_);
v___x_1402_ = v___x_1396_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
v___x_1404_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1390_, v___x_1391_, v___x_1403_, v___f_1399_);
v___x_1405_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1390_, v___x_1391_, v___x_1404_, v___f_1389_);
return v___x_1405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object* v_tail_1408_, lean_object* v_x_1409_, lean_object* v_head_1410_, lean_object* v_x_1411_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v_head_1410_);
lean_dec(v_x_1409_);
lean_dec(v_tail_1408_);
v_a_1413_ = lean_ctor_get(v_x_1411_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_x_1411_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1415_ = v_x_1411_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v_x_1411_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
else
{
lean_object* v_a_1422_; uint8_t v___x_1423_; 
v_a_1422_ = lean_ctor_get(v_x_1411_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v_x_1411_, 1);
v___x_1423_ = lean_unbox(v_a_1422_);
lean_dec(v_a_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref(v_head_1410_);
v___x_1424_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1408_, v_x_1409_);
return v___x_1424_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_head_1410_);
lean_ctor_set(v___x_1425_, 1, v_x_1409_);
v___x_1426_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1408_, v___x_1425_);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1427_, v_x_1428_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object* v___x_1431_, lean_object* v_eList_1432_, lean_object* v___f_1433_, lean_object* v_x_1434_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v___f_1433_);
lean_dec(v_eList_1432_);
lean_dec(v___x_1431_);
v_a_1436_ = lean_ctor_get(v_x_1434_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1438_ = v_x_1434_;
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v_x_1434_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1444_;
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
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_a_1445_ = lean_ctor_get(v_x_1434_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v_x_1434_, 1);
lean_inc(v___x_1431_);
v___f_1446_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1446_, 0, v_a_1445_);
lean_closure_set(v___f_1446_, 1, v___x_1431_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = 0;
v___x_1449_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_1432_, v___x_1431_);
v___x_1450_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1447_, v___x_1448_, v___x_1449_, v___f_1433_);
v___x_1451_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1447_, v___x_1448_, v___x_1450_, v___f_1446_);
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v___x_1452_, lean_object* v_eList_1453_, lean_object* v___f_1454_, lean_object* v_x_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v___x_1452_, v_eList_1453_, v___f_1454_, v_x_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object* v_q_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_eList_1462_; lean_object* v_dList_1463_; lean_object* v___f_1464_; lean_object* v___x_1465_; lean_object* v___f_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_eList_1462_ = lean_ctor_get(v_q_1459_, 0);
lean_inc(v_eList_1462_);
v_dList_1463_ = lean_ctor_get(v_q_1459_, 1);
lean_inc(v_dList_1463_);
lean_dec_ref(v_q_1459_);
v___f_1464_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_1465_ = lean_box(0);
v___f_1466_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1466_, 0, v___x_1465_);
lean_closure_set(v___f_1466_, 1, v_eList_1462_);
lean_closure_set(v___f_1466_, 2, v___f_1464_);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = 0;
v___x_1469_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_1463_, v___x_1465_);
v___x_1470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1467_, v___x_1468_, v___x_1469_, v___f_1464_);
v___x_1471_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1467_, v___x_1468_, v___x_1470_, v___f_1466_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object* v_q_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1472_, v___y_1473_);
lean_dec(v___y_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object* v___y_1476_, lean_object* v_x_1477_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1487_; 
v_a_1479_ = lean_ctor_get(v_x_1477_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_x_1477_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1481_ = v_x_1477_;
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v_x_1477_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v_values_1489_; lean_object* v_consumers_1490_; uint8_t v_closed_1491_; lean_object* v___x_1492_; lean_object* v___f_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_a_1488_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v_x_1477_, 1);
v_values_1489_ = lean_ctor_get(v_a_1488_, 0);
lean_inc_ref(v_values_1489_);
v_consumers_1490_ = lean_ctor_get(v_a_1488_, 1);
lean_inc_ref(v_consumers_1490_);
v_closed_1491_ = lean_ctor_get_uint8(v_a_1488_, sizeof(void*)*2);
lean_dec(v_a_1488_);
v___x_1492_ = lean_box(v_closed_1491_);
lean_inc(v___y_1476_);
v___f_1493_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1493_, 0, v_values_1489_);
lean_closure_set(v___f_1493_, 1, v___x_1492_);
lean_closure_set(v___f_1493_, 2, v___y_1476_);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = 0;
v___x_1496_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_1490_, v___y_1476_);
v___x_1497_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1494_, v___x_1495_, v___x_1496_, v___f_1493_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object* v___y_1498_, lean_object* v_x_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1498_, v_x_1499_);
lean_dec(v___y_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object* v___y_1502_){
_start:
{
lean_object* v___f_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_inc(v___y_1502_);
v___f_1504_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1504_, 0, v___y_1502_);
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = 0;
v___x_1507_ = lean_st_ref_get(v___y_1502_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
v___x_1510_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1505_, v___x_1506_, v___x_1509_, v___f_1504_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1511_);
lean_dec(v___y_1511_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object* v_ch_1520_){
_start:
{
lean_object* v___f_1521_; lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___f_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___f_1521_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1));
lean_inc_ref_n(v_ch_1520_, 2);
v___f_1522_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1522_, 0, v___f_1521_);
lean_closure_set(v___f_1522_, 1, v_ch_1520_);
v___f_1523_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2));
v___f_1524_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3));
v___x_1525_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1525_, 0, lean_box(0));
lean_closure_set(v___x_1525_, 1, lean_box(0));
lean_closure_set(v___x_1525_, 2, v_ch_1520_);
lean_closure_set(v___x_1525_, 3, v___f_1523_);
v___x_1526_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1526_, 0, lean_box(0));
lean_closure_set(v___x_1526_, 1, lean_box(0));
lean_closure_set(v___x_1526_, 2, v_ch_1520_);
lean_closure_set(v___x_1526_, 3, v___f_1524_);
v___x_1527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___f_1522_);
lean_ctor_set(v___x_1527_, 2, v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object* v_00_u03b1_1528_, lean_object* v_ch_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object* v_00_u03b1_1531_, lean_object* v_q_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1532_, v___y_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_1536_, lean_object* v_q_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_1536_, v_q_1537_, v___y_1538_);
lean_dec(v___y_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object* v_00_u03b1_1541_, lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1542_, v_x_1543_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_1547_, v_x_1548_, v_x_1549_, v___y_1550_);
lean_dec(v___y_1550_);
return v_res_1552_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0(void){
_start:
{
uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = 0;
v___x_1554_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_1555_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*2, v___x_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg(){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0);
v___x_1558_ = l_Std_Mutex_new___redArg(v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object* v_00_u03b1_1561_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object* v_00_u03b1_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object* v_v_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_producers_1581_; lean_object* v_consumers_1582_; uint8_t v_closed_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1605_; 
v___x_1579_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0));
v___x_1580_ = lean_st_ref_get(v___y_1577_);
v_producers_1581_ = lean_ctor_get(v___x_1580_, 0);
v_consumers_1582_ = lean_ctor_get(v___x_1580_, 1);
v_closed_1583_ = lean_ctor_get_uint8(v___x_1580_, sizeof(void*)*2);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1585_ = v___x_1580_;
v_isShared_1586_ = v_isSharedCheck_1605_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_consumers_1582_);
lean_inc(v_producers_1581_);
lean_dec(v___x_1580_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1605_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_1582_);
if (lean_obj_tag(v___x_1587_) == 1)
{
lean_object* v_val_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1603_; 
v_val_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1603_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_val_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1603_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v_fst_1592_; lean_object* v_snd_1593_; lean_object* v___x_1595_; 
v_fst_1592_ = lean_ctor_get(v_val_1588_, 0);
lean_inc(v_fst_1592_);
v_snd_1593_ = lean_ctor_get(v_val_1588_, 1);
lean_inc(v_snd_1593_);
lean_dec(v_val_1588_);
lean_inc(v_v_1576_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v_v_1576_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_v_1576_);
v___x_1595_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
uint8_t v___x_1596_; lean_object* v___x_1598_; 
v___x_1596_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_1592_, v___x_1595_);
lean_dec(v_fst_1592_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v_snd_1593_);
v___x_1598_ = v___x_1585_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_producers_1581_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_snd_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1601_, sizeof(void*)*2, v_closed_1583_);
v___x_1598_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_st_ref_swap(v___y_1577_, v___x_1598_);
lean_dec(v___x_1599_);
if (v___x_1596_ == 0)
{
goto _start;
}
else
{
lean_dec(v_v_1576_);
return v___x_1579_;
}
}
}
}
}
else
{
lean_object* v___x_1604_; 
lean_dec(v___x_1587_);
lean_del_object(v___x_1585_);
lean_dec_ref(v_producers_1581_);
lean_dec(v_v_1576_);
v___x_1604_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2));
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object* v_v_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1606_, v___y_1607_);
lean_dec(v___y_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object* v_v_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; lean_object* v_fst_1614_; 
v___x_1613_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1610_, v_a_1611_);
v_fst_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_fst_1614_);
lean_dec_ref(v___x_1613_);
if (lean_obj_tag(v_fst_1614_) == 0)
{
uint8_t v___x_1615_; 
v___x_1615_ = 1;
return v___x_1615_;
}
else
{
lean_object* v_val_1616_; uint8_t v___x_1617_; 
v_val_1616_ = lean_ctor_get(v_fst_1614_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v_fst_1614_, 1);
v___x_1617_ = lean_unbox(v_val_1616_);
lean_dec(v_val_1616_);
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object* v_v_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
uint8_t v_res_1621_; lean_object* v_r_1622_; 
v_res_1621_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1618_, v_a_1619_);
lean_dec(v_a_1619_);
v_r_1622_ = lean_box(v_res_1621_);
return v_r_1622_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object* v_00_u03b1_1623_, lean_object* v_v_1624_, lean_object* v_a_1625_){
_start:
{
uint8_t v___x_1627_; 
v___x_1627_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1624_, v_a_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object* v_00_u03b1_1628_, lean_object* v_v_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_res_1632_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(v_00_u03b1_1628_, v_v_1629_, v_a_1630_);
lean_dec(v_a_1630_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object* v_00_u03b1_1634_, lean_object* v_v_1635_, lean_object* v_inst_1636_, lean_object* v_a_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1635_, v___y_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1641_, lean_object* v_v_1642_, lean_object* v_inst_1643_, lean_object* v_a_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_1641_, v_v_1642_, v_inst_1643_, v_a_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v_a_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object* v_v_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; uint8_t v_closed_1652_; 
v___x_1651_ = lean_st_ref_get(v___y_1649_);
v_closed_1652_ = lean_ctor_get_uint8(v___x_1651_, sizeof(void*)*2);
lean_dec(v___x_1651_);
if (v_closed_1652_ == 0)
{
uint8_t v___x_1653_; 
v___x_1653_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1648_, v___y_1649_);
return v___x_1653_;
}
else
{
uint8_t v___x_1654_; 
lean_dec(v_v_1648_);
v___x_1654_ = 0;
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object* v_v_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
uint8_t v_res_1658_; lean_object* v_r_1659_; 
v_res_1658_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1655_, v___y_1656_);
lean_dec(v___y_1656_);
v_r_1659_ = lean_box(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object* v_ch_1660_, lean_object* v_v_1661_){
_start:
{
lean_object* v___f_1663_; lean_object* v___x_1664_; 
v___f_1663_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1663_, 0, v_v_1661_);
v___x_1664_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1660_, v___f_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object* v_ch_1665_, lean_object* v_v_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1665_, v_v_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object* v_00_u03b1_1669_, lean_object* v_ch_1670_, lean_object* v_v_1671_){
_start:
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1670_, v_v_1671_);
v___x_1674_ = lean_unbox(v___x_1673_);
lean_dec(v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_ch_1676_, lean_object* v_v_1677_, lean_object* v_a_1678_){
_start:
{
uint8_t v_res_1679_; lean_object* v_r_1680_; 
v_res_1679_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(v_00_u03b1_1675_, v_ch_1676_, v_v_1677_);
v_r_1680_ = lean_box(v_res_1679_);
return v_r_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object* v_x_1681_){
_start:
{
if (lean_obj_tag(v_x_1681_) == 0)
{
goto v___jp_1682_;
}
else
{
lean_object* v_val_1684_; uint8_t v___x_1685_; 
v_val_1684_ = lean_ctor_get(v_x_1681_, 0);
v___x_1685_ = lean_unbox(v_val_1684_);
if (v___x_1685_ == 0)
{
goto v___jp_1682_;
}
else
{
lean_object* v___x_1686_; 
v___x_1686_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
return v___x_1686_;
}
}
v___jp_1682_:
{
lean_object* v___x_1683_; 
v___x_1683_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object* v_x_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_1687_);
lean_dec(v_x_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object* v_v_1689_, lean_object* v___f_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; uint8_t v_closed_1694_; 
v___x_1693_ = lean_st_ref_get(v___y_1691_);
v_closed_1694_ = lean_ctor_get_uint8(v___x_1693_, sizeof(void*)*2);
lean_dec(v___x_1693_);
if (v_closed_1694_ == 0)
{
uint8_t v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = 1;
lean_inc(v_v_1689_);
v___x_1696_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1689_, v___y_1691_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v_producers_1699_; lean_object* v_consumers_1700_; uint8_t v_closed_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1714_; 
v___x_1697_ = lean_io_promise_new();
v___x_1698_ = lean_st_ref_take(v___y_1691_);
v_producers_1699_ = lean_ctor_get(v___x_1698_, 0);
v_consumers_1700_ = lean_ctor_get(v___x_1698_, 1);
v_closed_1701_ = lean_ctor_get_uint8(v___x_1698_, sizeof(void*)*2);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1703_ = v___x_1698_;
v_isShared_1704_ = v_isSharedCheck_1714_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_consumers_1700_);
lean_inc(v_producers_1699_);
lean_dec(v___x_1698_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1714_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_inc(v___x_1697_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_v_1689_);
lean_ctor_set(v___x_1705_, 1, v___x_1697_);
v___x_1706_ = l_Std_Queue_enqueue___redArg(v___x_1705_, v_producers_1699_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1706_);
v___x_1708_ = v___x_1703_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_consumers_1700_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, sizeof(void*)*2, v_closed_1701_);
v___x_1708_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1709_ = lean_st_ref_put(v___y_1691_, v___x_1708_);
v___x_1710_ = lean_io_promise_result_opt(v___x_1697_);
lean_dec(v___x_1697_);
v___x_1711_ = lean_unsigned_to_nat(0u);
v___x_1712_ = lean_task_map(v___f_1690_, v___x_1710_, v___x_1711_, v___x_1695_);
return v___x_1712_;
}
}
}
else
{
lean_object* v___x_1715_; 
lean_dec_ref(v___f_1690_);
lean_dec(v_v_1689_);
v___x_1715_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_1715_;
}
}
else
{
lean_object* v___x_1716_; 
lean_dec_ref(v___f_1690_);
lean_dec(v_v_1689_);
v___x_1716_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object* v_v_1717_, lean_object* v___f_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1717_, v___f_1718_, v___y_1719_);
lean_dec(v___y_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object* v_ch_1723_, lean_object* v_v_1724_){
_start:
{
lean_object* v___f_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; 
v___f_1726_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0));
v___f_1727_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1727_, 0, v_v_1724_);
lean_closure_set(v___f_1727_, 1, v___f_1726_);
v___x_1728_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1723_, v___f_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object* v_ch_1729_, lean_object* v_v_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1729_, v_v_1730_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object* v_00_u03b1_1733_, lean_object* v_ch_1734_, lean_object* v_v_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1734_, v_v_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object* v_00_u03b1_1738_, lean_object* v_ch_1739_, lean_object* v_v_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(v_00_u03b1_1738_, v_ch_1739_, v_v_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object* v_as_1743_, size_t v_sz_1744_, size_t v_i_1745_, lean_object* v_b_1746_){
_start:
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_usize_dec_lt(v_i_1745_, v_sz_1744_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v_b_1746_);
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; lean_object* v_a_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; size_t v___x_1754_; size_t v___x_1755_; 
v___x_1750_ = lean_box(0);
v_a_1751_ = lean_array_uget_borrowed(v_as_1743_, v_i_1745_);
v___x_1752_ = lean_box(0);
v___x_1753_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_1751_, v___x_1752_);
v___x_1754_ = ((size_t)1ULL);
v___x_1755_ = lean_usize_add(v_i_1745_, v___x_1754_);
v_i_1745_ = v___x_1755_;
v_b_1746_ = v___x_1750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object* v_as_1757_, lean_object* v_sz_1758_, lean_object* v_i_1759_, lean_object* v_b_1760_, lean_object* v___y_1761_){
_start:
{
size_t v_sz_boxed_1762_; size_t v_i_boxed_1763_; lean_object* v_res_1764_; 
v_sz_boxed_1762_ = lean_unbox_usize(v_sz_1758_);
lean_dec(v_sz_1758_);
v_i_boxed_1763_ = lean_unbox_usize(v_i_1759_);
lean_dec(v_i_1759_);
v_res_1764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1757_, v_sz_boxed_1762_, v_i_boxed_1763_, v_b_1760_);
lean_dec_ref(v_as_1757_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; uint8_t v_closed_1768_; 
v___x_1767_ = lean_st_ref_get(v___y_1765_);
v_closed_1768_ = lean_ctor_get_uint8(v___x_1767_, sizeof(void*)*2);
if (v_closed_1768_ == 0)
{
lean_object* v_producers_1769_; lean_object* v_consumers_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1793_; 
v_producers_1769_ = lean_ctor_get(v___x_1767_, 0);
v_consumers_1770_ = lean_ctor_get(v___x_1767_, 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1772_ = v___x_1767_;
v_isShared_1773_ = v_isSharedCheck_1793_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_consumers_1770_);
lean_inc(v_producers_1769_);
lean_dec(v___x_1767_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1793_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; size_t v_sz_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1774_ = l_Std_Queue_toArray___redArg(v_consumers_1770_);
v___x_1775_ = lean_box(0);
v_sz_1776_ = lean_array_size(v___x_1774_);
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_1774_, v_sz_1776_, v___x_1777_, v___x_1775_);
lean_dec_ref(v___x_1774_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1791_; 
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v___x_1778_, 0);
lean_dec(v_unused_1792_);
v___x_1780_ = v___x_1778_;
v_isShared_1781_ = v_isSharedCheck_1791_;
goto v_resetjp_1779_;
}
else
{
lean_dec(v___x_1778_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1791_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1785_; 
v___x_1782_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_1783_ = 1;
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v___x_1782_);
v___x_1785_ = v___x_1772_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_producers_1769_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1782_);
v___x_1785_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
lean_ctor_set_uint8(v___x_1785_, sizeof(void*)*2, v___x_1783_);
v___x_1786_ = lean_st_ref_swap(v___y_1765_, v___x_1785_);
lean_dec(v___x_1786_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1775_);
v___x_1788_ = v___x_1780_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1775_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_del_object(v___x_1772_);
lean_dec_ref(v_producers_1769_);
return v___x_1778_;
}
}
}
else
{
uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v___x_1767_);
v___x_1794_ = 1;
v___x_1795_ = lean_box(v___x_1794_);
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1797_);
lean_dec(v___y_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object* v_ch_1801_){
_start:
{
lean_object* v___f_1803_; lean_object* v___x_1804_; 
v___f_1803_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0));
v___x_1804_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_1801_, v___f_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object* v_ch_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object* v_00_u03b1_1808_, lean_object* v_ch_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object* v_00_u03b1_1812_, lean_object* v_ch_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(v_00_u03b1_1812_, v_ch_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object* v_00_u03b1_1816_, lean_object* v_as_1817_, size_t v_sz_1818_, size_t v_i_1819_, lean_object* v_b_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1817_, v_sz_1818_, v_i_1819_, v_b_1820_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_as_1825_, lean_object* v_sz_1826_, lean_object* v_i_1827_, lean_object* v_b_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
size_t v_sz_boxed_1831_; size_t v_i_boxed_1832_; lean_object* v_res_1833_; 
v_sz_boxed_1831_ = lean_unbox_usize(v_sz_1826_);
lean_dec(v_sz_1826_);
v_i_boxed_1832_ = lean_unbox_usize(v_i_1827_);
lean_dec(v_i_1827_);
v_res_1833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_1824_, v_as_1825_, v_sz_boxed_1831_, v_i_boxed_1832_, v_b_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v_as_1825_);
return v_res_1833_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; uint8_t v_closed_1837_; 
v___x_1836_ = lean_st_ref_get(v___y_1834_);
v_closed_1837_ = lean_ctor_get_uint8(v___x_1836_, sizeof(void*)*2);
lean_dec(v___x_1836_);
return v_closed_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_res_1840_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1838_);
lean_dec(v___y_1838_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object* v_ch_1843_){
_start:
{
lean_object* v___f_1845_; lean_object* v___x_1846_; 
v___f_1845_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0));
v___x_1846_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1843_, v___f_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object* v_ch_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object* v_00_u03b1_1850_, lean_object* v_ch_1851_){
_start:
{
lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1851_);
v___x_1854_ = lean_unbox(v___x_1853_);
lean_dec(v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object* v_00_u03b1_1855_, lean_object* v_ch_1856_, lean_object* v_a_1857_){
_start:
{
uint8_t v_res_1858_; lean_object* v_r_1859_; 
v_res_1858_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(v_00_u03b1_1855_, v_ch_1856_);
v_r_1859_ = lean_box(v_res_1858_);
return v_r_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object* v_snd_1860_, lean_object* v_inst_1861_, lean_object* v_toBind_1862_, lean_object* v___f_1863_, lean_object* v_a_1864_){
_start:
{
uint8_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1865_ = 1;
v___x_1866_ = lean_box(v___x_1865_);
v___x_1867_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1867_, 0, lean_box(0));
lean_closure_set(v___x_1867_, 1, v___x_1866_);
lean_closure_set(v___x_1867_, 2, v_snd_1860_);
v___x_1868_ = lean_apply_2(v_inst_1861_, lean_box(0), v___x_1867_);
v___x_1869_ = lean_apply_4(v_toBind_1862_, lean_box(0), lean_box(0), v___x_1868_, v___f_1863_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_1870_, lean_object* v_inst_1871_, lean_object* v_toBind_1872_, lean_object* v_a_1873_, lean_object* v_inst_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_producers_1876_; lean_object* v_consumers_1877_; uint8_t v_closed_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1899_; 
v_producers_1876_ = lean_ctor_get(v_a_1875_, 0);
v_consumers_1877_ = lean_ctor_get(v_a_1875_, 1);
v_closed_1878_ = lean_ctor_get_uint8(v_a_1875_, sizeof(void*)*2);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_a_1875_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1880_ = v_a_1875_;
v_isShared_1881_ = v_isSharedCheck_1899_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_consumers_1877_);
lean_inc(v_producers_1876_);
lean_dec(v_a_1875_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1899_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1876_);
if (lean_obj_tag(v___x_1882_) == 1)
{
lean_object* v_val_1883_; lean_object* v_fst_1884_; lean_object* v_snd_1885_; lean_object* v_fst_1886_; lean_object* v_snd_1887_; lean_object* v___f_1888_; lean_object* v___f_1889_; lean_object* v___x_1891_; 
v_val_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_val_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v_fst_1884_ = lean_ctor_get(v_val_1883_, 0);
lean_inc(v_fst_1884_);
v_snd_1885_ = lean_ctor_get(v_val_1883_, 1);
lean_inc(v_snd_1885_);
lean_dec(v_val_1883_);
v_fst_1886_ = lean_ctor_get(v_fst_1884_, 0);
lean_inc(v_fst_1886_);
v_snd_1887_ = lean_ctor_get(v_fst_1884_, 1);
lean_inc(v_snd_1887_);
lean_dec(v_fst_1884_);
v___f_1888_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1888_, 0, v_toApplicative_1870_);
lean_closure_set(v___f_1888_, 1, v_fst_1886_);
lean_inc(v_toBind_1872_);
v___f_1889_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1889_, 0, v_snd_1887_);
lean_closure_set(v___f_1889_, 1, v_inst_1871_);
lean_closure_set(v___f_1889_, 2, v_toBind_1872_);
lean_closure_set(v___f_1889_, 3, v___f_1888_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_snd_1885_);
v___x_1891_ = v___x_1880_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_snd_1885_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_consumers_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*2, v_closed_1878_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_inc(v_a_1873_);
v___x_1892_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1892_, 0, lean_box(0));
lean_closure_set(v___x_1892_, 1, lean_box(0));
lean_closure_set(v___x_1892_, 2, v_a_1873_);
lean_closure_set(v___x_1892_, 3, v___x_1891_);
v___x_1893_ = lean_apply_2(v_inst_1874_, lean_box(0), v___x_1892_);
v___x_1894_ = lean_apply_4(v_toBind_1872_, lean_box(0), lean_box(0), v___x_1893_, v___f_1889_);
return v___x_1894_;
}
}
else
{
lean_object* v_toPure_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v___x_1882_);
lean_del_object(v___x_1880_);
lean_dec_ref(v_consumers_1877_);
lean_dec(v_inst_1874_);
lean_dec(v_toBind_1872_);
lean_dec(v_inst_1871_);
v_toPure_1896_ = lean_ctor_get(v_toApplicative_1870_, 1);
lean_inc(v_toPure_1896_);
lean_dec_ref(v_toApplicative_1870_);
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_apply_2(v_toPure_1896_, lean_box(0), v___x_1897_);
return v___x_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_1900_, lean_object* v_inst_1901_, lean_object* v_toBind_1902_, lean_object* v_a_1903_, lean_object* v_inst_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(v_toApplicative_1900_, v_inst_1901_, v_toBind_1902_, v_a_1903_, v_inst_1904_, v_a_1905_);
lean_dec(v_a_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_toApplicative_1911_; lean_object* v_toBind_1912_; lean_object* v___f_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_toApplicative_1911_ = lean_ctor_get(v_inst_1907_, 0);
lean_inc_ref(v_toApplicative_1911_);
v_toBind_1912_ = lean_ctor_get(v_inst_1907_, 1);
lean_inc_n(v_toBind_1912_, 2);
lean_dec_ref(v_inst_1907_);
lean_inc(v_inst_1908_);
lean_inc_n(v_a_1910_, 2);
v___f_1913_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1913_, 0, v_toApplicative_1911_);
lean_closure_set(v___f_1913_, 1, v_inst_1909_);
lean_closure_set(v___f_1913_, 2, v_toBind_1912_);
lean_closure_set(v___f_1913_, 3, v_a_1910_);
lean_closure_set(v___f_1913_, 4, v_inst_1908_);
v___x_1914_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1914_, 0, lean_box(0));
lean_closure_set(v___x_1914_, 1, lean_box(0));
lean_closure_set(v___x_1914_, 2, v_a_1910_);
v___x_1915_ = lean_apply_2(v_inst_1908_, lean_box(0), v___x_1914_);
v___x_1916_ = lean_apply_4(v_toBind_1912_, lean_box(0), lean_box(0), v___x_1915_, v___f_1913_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1917_, v_inst_1918_, v_inst_1919_, v_a_1920_);
lean_dec(v_a_1920_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object* v_m_1922_, lean_object* v_00_u03b1_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1924_, v_inst_1925_, v_inst_1926_, v_a_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(lean_object* v_m_1929_, lean_object* v_00_u03b1_1930_, lean_object* v_inst_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(v_m_1929_, v_00_u03b1_1930_, v_inst_1931_, v_inst_1932_, v_inst_1933_, v_a_1934_);
lean_dec(v_a_1934_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v_producers_1939_; lean_object* v_consumers_1940_; uint8_t v_closed_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1966_; 
v___x_1938_ = lean_st_ref_get(v_a_1936_);
v_producers_1939_ = lean_ctor_get(v___x_1938_, 0);
v_consumers_1940_ = lean_ctor_get(v___x_1938_, 1);
v_closed_1941_ = lean_ctor_get_uint8(v___x_1938_, sizeof(void*)*2);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1943_ = v___x_1938_;
v_isShared_1944_ = v_isSharedCheck_1966_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_consumers_1940_);
lean_inc(v_producers_1939_);
lean_dec(v___x_1938_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1966_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1939_);
if (lean_obj_tag(v___x_1945_) == 1)
{
lean_object* v_val_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1964_; 
v_val_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1964_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_val_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1964_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_fst_1950_; lean_object* v_snd_1951_; lean_object* v_fst_1952_; lean_object* v_snd_1953_; lean_object* v___x_1955_; 
v_fst_1950_ = lean_ctor_get(v_val_1946_, 0);
lean_inc(v_fst_1950_);
v_snd_1951_ = lean_ctor_get(v_val_1946_, 1);
lean_inc(v_snd_1951_);
lean_dec(v_val_1946_);
v_fst_1952_ = lean_ctor_get(v_fst_1950_, 0);
lean_inc(v_fst_1952_);
v_snd_1953_ = lean_ctor_get(v_fst_1950_, 1);
lean_inc(v_snd_1953_);
lean_dec(v_fst_1950_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v_snd_1951_);
v___x_1955_ = v___x_1943_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_snd_1951_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_consumers_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1963_, sizeof(void*)*2, v_closed_1941_);
v___x_1955_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; uint8_t v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1956_ = lean_st_ref_swap(v_a_1936_, v___x_1955_);
lean_dec(v___x_1956_);
v___x_1957_ = 1;
v___x_1958_ = lean_box(v___x_1957_);
v___x_1959_ = lean_io_promise_resolve(v___x_1958_, v_snd_1953_);
lean_dec(v_snd_1953_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v_fst_1952_);
v___x_1961_ = v___x_1948_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_fst_1952_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v___x_1965_; 
lean_dec(v___x_1945_);
lean_del_object(v___x_1943_);
lean_dec_ref(v_consumers_1940_);
v___x_1965_ = lean_box(0);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object* v_a_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1967_);
lean_dec(v_a_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object* v_00_u03b1_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_a_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_1974_, v_a_1975_);
lean_dec(v_a_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object* v_ch_1979_){
_start:
{
lean_object* v___f_1981_; lean_object* v___x_1982_; 
v___f_1981_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0));
v___x_1982_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1979_, v___f_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object* v_ch_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object* v_00_u03b1_1986_, lean_object* v_ch_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_1987_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_ch_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(v_00_u03b1_1990_, v_ch_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object* v___f_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_st_ref_get(v___y_1995_);
v___x_1998_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_1995_);
if (lean_obj_tag(v___x_1998_) == 1)
{
lean_object* v___x_1999_; 
lean_dec(v___x_1997_);
lean_dec_ref(v___f_1994_);
v___x_1999_ = lean_task_pure(v___x_1998_);
return v___x_1999_;
}
else
{
uint8_t v_closed_2000_; 
lean_dec(v___x_1998_);
v_closed_2000_ = lean_ctor_get_uint8(v___x_1997_, sizeof(void*)*2);
if (v_closed_2000_ == 0)
{
lean_object* v_producers_2001_; lean_object* v_consumers_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2017_; 
v_producers_2001_ = lean_ctor_get(v___x_1997_, 0);
v_consumers_2002_ = lean_ctor_get(v___x_1997_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2004_ = v___x_1997_;
v_isShared_2005_ = v_isSharedCheck_2017_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_consumers_2002_);
lean_inc(v_producers_2001_);
lean_dec(v___x_1997_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2017_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2006_ = 1;
v___x_2007_ = lean_io_promise_new();
lean_inc(v___x_2007_);
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
v___x_2009_ = l_Std_Queue_enqueue___redArg(v___x_2008_, v_consumers_2002_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v___x_2009_);
v___x_2011_ = v___x_2004_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_producers_2001_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*2, v_closed_2000_);
v___x_2011_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2012_ = lean_st_ref_swap(v___y_1995_, v___x_2011_);
lean_dec(v___x_2012_);
v___x_2013_ = lean_io_promise_result_opt(v___x_2007_);
lean_dec(v___x_2007_);
v___x_2014_ = lean_unsigned_to_nat(0u);
v___x_2015_ = lean_task_map(v___f_1994_, v___x_2013_, v___x_2014_, v___x_2006_);
return v___x_2015_;
}
}
}
else
{
lean_object* v___x_2018_; 
lean_dec(v___x_1997_);
lean_dec_ref(v___f_1994_);
v___x_2018_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object* v___f_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2019_, v___y_2020_);
lean_dec(v___y_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object* v_ch_2025_){
_start:
{
lean_object* v___f_2027_; lean_object* v___x_2028_; 
v___f_2027_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0));
v___x_2028_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2025_, v___f_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object* v_ch_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object* v_00_u03b1_2032_, lean_object* v_ch_2033_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2033_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object* v_00_u03b1_2036_, lean_object* v_ch_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(v_00_u03b1_2036_, v_ch_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_2040_, lean_object* v_a_2041_){
_start:
{
uint8_t v___y_2043_; lean_object* v_producers_2047_; uint8_t v_closed_2048_; uint8_t v___x_2049_; 
v_producers_2047_ = lean_ctor_get(v_a_2041_, 0);
v_closed_2048_ = lean_ctor_get_uint8(v_a_2041_, sizeof(void*)*2);
v___x_2049_ = l_Std_Queue_isEmpty___redArg(v_producers_2047_);
if (v___x_2049_ == 0)
{
uint8_t v___x_2050_; 
v___x_2050_ = 1;
v___y_2043_ = v___x_2050_;
goto v___jp_2042_;
}
else
{
v___y_2043_ = v_closed_2048_;
goto v___jp_2042_;
}
v___jp_2042_:
{
lean_object* v_toPure_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_toPure_2044_ = lean_ctor_get(v_toApplicative_2040_, 1);
lean_inc(v_toPure_2044_);
lean_dec_ref(v_toApplicative_2040_);
v___x_2045_ = lean_box(v___y_2043_);
v___x_2046_ = lean_apply_2(v_toPure_2044_, lean_box(0), v___x_2045_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(v_toApplicative_2051_, v_a_2052_);
lean_dec_ref(v_a_2052_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object* v_inst_2054_, lean_object* v_inst_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_toApplicative_2057_; lean_object* v_toBind_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_toApplicative_2057_ = lean_ctor_get(v_inst_2054_, 0);
lean_inc_ref(v_toApplicative_2057_);
v_toBind_2058_ = lean_ctor_get(v_inst_2054_, 1);
lean_inc(v_toBind_2058_);
lean_dec_ref(v_inst_2054_);
v___f_2059_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2059_, 0, v_toApplicative_2057_);
lean_inc(v_a_2056_);
v___x_2060_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2060_, 0, lean_box(0));
lean_closure_set(v___x_2060_, 1, lean_box(0));
lean_closure_set(v___x_2060_, 2, v_a_2056_);
v___x_2061_ = lean_apply_2(v_inst_2055_, lean_box(0), v___x_2060_);
v___x_2062_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2061_, v___f_2059_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(v_inst_2063_, v_inst_2064_, v_a_2065_);
lean_dec(v_a_2065_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object* v_m_2067_, lean_object* v_00_u03b1_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_toApplicative_2072_; lean_object* v_toBind_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_toApplicative_2072_ = lean_ctor_get(v_inst_2069_, 0);
lean_inc_ref(v_toApplicative_2072_);
v_toBind_2073_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc(v_toBind_2073_);
lean_dec_ref(v_inst_2069_);
v___f_2074_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2074_, 0, v_toApplicative_2072_);
lean_inc(v_a_2071_);
v___x_2075_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2075_, 0, lean_box(0));
lean_closure_set(v___x_2075_, 1, lean_box(0));
lean_closure_set(v___x_2075_, 2, v_a_2071_);
v___x_2076_ = lean_apply_2(v_inst_2070_, lean_box(0), v___x_2075_);
v___x_2077_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v___x_2076_, v___f_2074_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(lean_object* v_m_2078_, lean_object* v_00_u03b1_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(v_m_2078_, v_00_u03b1_2079_, v_inst_2080_, v_inst_2081_, v_a_2082_);
lean_dec(v_a_2082_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object* v_snd_2084_, lean_object* v___f_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v___f_2085_);
v_a_2088_ = lean_ctor_get(v_x_2086_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_x_2086_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2090_ = v_x_2086_;
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v_x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
}
else
{
lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2110_; 
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2086_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_x_2086_, 0);
lean_dec(v_unused_2111_);
v___x_2098_ = v_x_2086_;
v_isShared_2099_ = v_isSharedCheck_2110_;
goto v_resetjp_2097_;
}
else
{
lean_dec(v_x_2086_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2110_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
uint8_t v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2100_ = 1;
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = 0;
v___x_2103_ = lean_box(v___x_2100_);
v___x_2104_ = lean_io_promise_resolve(v___x_2103_, v_snd_2084_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2104_);
v___x_2106_ = v___x_2098_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
v___x_2108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2101_, v___x_2102_, v___x_2107_, v___f_2085_);
return v___x_2108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_snd_2112_, lean_object* v___f_2113_, lean_object* v_x_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2112_, v___f_2113_, v_x_2114_);
lean_dec(v_snd_2112_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object* v_a_2117_, lean_object* v_x_2118_){
_start:
{
if (lean_obj_tag(v_x_2118_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2128_; 
v_a_2120_ = lean_ctor_get(v_x_2118_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_x_2118_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2122_ = v_x_2118_;
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v_x_2118_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v_producers_2130_; lean_object* v_consumers_2131_; uint8_t v_closed_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2153_; 
v_a_2129_ = lean_ctor_get(v_x_2118_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v_x_2118_, 1);
v_producers_2130_ = lean_ctor_get(v_a_2129_, 0);
v_consumers_2131_ = lean_ctor_get(v_a_2129_, 1);
v_closed_2132_ = lean_ctor_get_uint8(v_a_2129_, sizeof(void*)*2);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2134_ = v_a_2129_;
v_isShared_2135_ = v_isSharedCheck_2153_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_consumers_2131_);
lean_inc(v_producers_2130_);
lean_dec(v_a_2129_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2153_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2130_);
if (lean_obj_tag(v___x_2136_) == 1)
{
lean_object* v_val_2137_; lean_object* v_fst_2138_; lean_object* v_snd_2139_; lean_object* v_fst_2140_; lean_object* v_snd_2141_; lean_object* v___f_2142_; lean_object* v___f_2143_; lean_object* v___x_2145_; 
v_val_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_val_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v_fst_2138_ = lean_ctor_get(v_val_2137_, 0);
lean_inc(v_fst_2138_);
v_snd_2139_ = lean_ctor_get(v_val_2137_, 1);
lean_inc(v_snd_2139_);
lean_dec(v_val_2137_);
v_fst_2140_ = lean_ctor_get(v_fst_2138_, 0);
lean_inc(v_fst_2140_);
v_snd_2141_ = lean_ctor_get(v_fst_2138_, 1);
lean_inc(v_snd_2141_);
lean_dec(v_fst_2138_);
v___f_2142_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2142_, 0, v_fst_2140_);
v___f_2143_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2143_, 0, v_snd_2141_);
lean_closure_set(v___f_2143_, 1, v___f_2142_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v_snd_2139_);
v___x_2145_ = v___x_2134_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_snd_2139_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_consumers_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2, v_closed_2132_);
v___x_2145_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v___x_2147_ = 0;
v___x_2148_ = lean_st_ref_swap(v_a_2117_, v___x_2145_);
lean_dec(v___x_2148_);
v___x_2149_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_2150_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2146_, v___x_2147_, v___x_2149_, v___f_2143_);
return v___x_2150_;
}
}
else
{
lean_object* v___x_2152_; 
lean_dec(v___x_2136_);
lean_del_object(v___x_2134_);
lean_dec_ref(v_consumers_2131_);
v___x_2152_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_2152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_a_2154_, lean_object* v_x_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2154_, v_x_2155_);
lean_dec(v_a_2154_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object* v_a_2158_){
_start:
{
lean_object* v___f_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_inc(v_a_2158_);
v___f_2160_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2160_, 0, v_a_2158_);
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = 0;
v___x_2163_ = lean_st_ref_get(v_a_2158_);
v___x_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
v___x_2166_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2161_, v___x_2162_, v___x_2165_, v___f_2160_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object* v_a_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2167_);
lean_dec(v_a_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object* v_00_u03b1_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2171_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_2174_, lean_object* v_a_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_2174_, v_a_2175_);
lean_dec(v_a_2175_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_2178_, lean_object* v___y_2179_, lean_object* v___f_2180_, lean_object* v_x_2181_){
_start:
{
if (lean_obj_tag(v_x_2181_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v___f_2180_);
lean_dec_ref(v_lose_2178_);
v_a_2183_ = lean_ctor_get(v_x_2181_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_x_2181_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2185_ = v_x_2181_;
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v_x_2181_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
return v___x_2189_;
}
}
}
else
{
lean_object* v_a_2192_; uint8_t v___x_2193_; 
v_a_2192_ = lean_ctor_get(v_x_2181_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v_x_2181_, 1);
v___x_2193_ = lean_unbox(v_a_2192_);
lean_dec(v_a_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec_ref(v___f_2180_);
lean_inc(v___y_2179_);
v___x_2194_ = lean_apply_2(v_lose_2178_, v___y_2179_, lean_box(0));
return v___x_2194_;
}
else
{
lean_object* v___x_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec_ref(v_lose_2178_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = 0;
v___x_2197_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2179_);
v___x_2198_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2195_, v___x_2196_, v___x_2197_, v___f_2180_);
return v___x_2198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_2199_, lean_object* v___y_2200_, lean_object* v___f_2201_, lean_object* v_x_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2199_, v___y_2200_, v___f_2201_, v_x_2202_);
lean_dec(v___y_2200_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object* v_w_2205_, lean_object* v_lose_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_finished_2209_; lean_object* v_promise_2210_; lean_object* v___f_2211_; lean_object* v___f_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; uint8_t v___y_2217_; uint8_t v___x_2225_; 
v_finished_2209_ = lean_ctor_get(v_w_2205_, 0);
lean_inc(v_finished_2209_);
v_promise_2210_ = lean_ctor_get(v_w_2205_, 1);
lean_inc(v_promise_2210_);
lean_dec_ref(v_w_2205_);
v___f_2211_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2211_, 0, v_promise_2210_);
lean_inc(v___y_2207_);
v___f_2212_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2212_, 0, v_lose_2206_);
lean_closure_set(v___f_2212_, 1, v___y_2207_);
lean_closure_set(v___f_2212_, 2, v___f_2211_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = 0;
v___x_2215_ = lean_st_ref_take(v_finished_2209_);
v___x_2225_ = lean_unbox(v___x_2215_);
lean_dec(v___x_2215_);
if (v___x_2225_ == 0)
{
uint8_t v___x_2226_; 
v___x_2226_ = 1;
v___y_2217_ = v___x_2226_;
goto v___jp_2216_;
}
else
{
v___y_2217_ = v___x_2214_;
goto v___jp_2216_;
}
v___jp_2216_:
{
uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2218_ = 1;
v___x_2219_ = lean_box(v___x_2218_);
v___x_2220_ = lean_st_ref_put(v_finished_2209_, v___x_2219_);
lean_dec(v_finished_2209_);
v___x_2221_ = lean_box(v___y_2217_);
v___x_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v___x_2224_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2213_, v___x_2214_, v___x_2223_, v___f_2212_);
return v___x_2224_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object* v_w_2227_, lean_object* v_lose_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2227_, v_lose_2228_, v___y_2229_);
lean_dec(v___y_2229_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object* v_00_u03b1_2232_, lean_object* v_w_2233_, lean_object* v_lose_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2233_, v_lose_2234_, v___y_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_2238_, lean_object* v_w_2239_, lean_object* v_lose_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_2238_, v_w_2239_, v_lose_2240_, v___y_2241_);
lean_dec(v___y_2241_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object* v_x_2244_){
_start:
{
uint8_t v___y_2247_; 
if (lean_obj_tag(v_x_2244_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2259_; 
v_a_2251_ = lean_ctor_get(v_x_2244_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_x_2244_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2253_ = v_x_2244_;
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v_x_2244_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v_producers_2261_; uint8_t v_closed_2262_; uint8_t v___x_2263_; 
v_a_2260_ = lean_ctor_get(v_x_2244_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v_x_2244_, 1);
v_producers_2261_ = lean_ctor_get(v_a_2260_, 0);
lean_inc_ref(v_producers_2261_);
v_closed_2262_ = lean_ctor_get_uint8(v_a_2260_, sizeof(void*)*2);
lean_dec(v_a_2260_);
v___x_2263_ = l_Std_Queue_isEmpty___redArg(v_producers_2261_);
lean_dec_ref(v_producers_2261_);
if (v___x_2263_ == 0)
{
uint8_t v___x_2264_; 
v___x_2264_ = 1;
v___y_2247_ = v___x_2264_;
goto v___jp_2246_;
}
else
{
v___y_2247_ = v_closed_2262_;
goto v___jp_2246_;
}
}
v___jp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_box(v___y_2247_);
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object* v_x_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2265_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object* v___y_2268_, lean_object* v_waiter_2269_, lean_object* v_x_2270_){
_start:
{
if (lean_obj_tag(v_x_2270_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_waiter_2269_);
v_a_2272_ = lean_ctor_get(v_x_2270_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_x_2270_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2274_ = v_x_2270_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v_x_2270_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
}
}
else
{
lean_object* v_a_2281_; uint8_t v___x_2282_; 
v_a_2281_ = lean_ctor_get(v_x_2270_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v_x_2270_, 1);
v___x_2282_ = lean_unbox(v_a_2281_);
lean_dec(v_a_2281_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v_producers_2284_; lean_object* v_consumers_2285_; uint8_t v_closed_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2297_; 
v___x_2283_ = lean_st_ref_take(v___y_2268_);
v_producers_2284_ = lean_ctor_get(v___x_2283_, 0);
v_consumers_2285_ = lean_ctor_get(v___x_2283_, 1);
v_closed_2286_ = lean_ctor_get_uint8(v___x_2283_, sizeof(void*)*2);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2288_ = v___x_2283_;
v_isShared_2289_ = v_isSharedCheck_2297_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_consumers_2285_);
lean_inc(v_producers_2284_);
lean_dec(v___x_2283_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2297_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_waiter_2269_);
v___x_2291_ = l_Std_Queue_enqueue___redArg(v___x_2290_, v_consumers_2285_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v___x_2291_);
v___x_2293_ = v___x_2288_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_producers_2284_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___x_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2296_, sizeof(void*)*2, v_closed_2286_);
v___x_2293_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_st_ref_put(v___y_2268_, v___x_2293_);
v___x_2295_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2295_;
}
}
}
else
{
lean_object* v_lose_2298_; lean_object* v___x_2299_; 
v_lose_2298_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0));
v___x_2299_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_2269_, v_lose_2298_, v___y_2268_);
return v___x_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object* v___y_2300_, lean_object* v_waiter_2301_, lean_object* v_x_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2300_, v_waiter_2301_, v_x_2302_);
lean_dec(v___y_2300_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object* v_waiter_2305_, lean_object* v___f_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___f_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_inc(v___y_2307_);
v___f_2309_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2309_, 0, v___y_2307_);
lean_closure_set(v___f_2309_, 1, v_waiter_2305_);
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = 0;
v___x_2312_ = lean_st_ref_get(v___y_2307_);
v___x_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
v___x_2315_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2310_, v___x_2311_, v___x_2314_, v___f_2306_);
v___x_2316_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2310_, v___x_2311_, v___x_2315_, v___f_2309_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object* v_waiter_2317_, lean_object* v___f_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v_waiter_2317_, v___f_2318_, v___y_2319_);
lean_dec(v___y_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object* v___f_2322_, lean_object* v_ch_2323_, lean_object* v_waiter_2324_){
_start:
{
lean_object* v___f_2326_; lean_object* v___x_2327_; 
v___f_2326_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2326_, 0, v_waiter_2324_);
lean_closure_set(v___f_2326_, 1, v___f_2322_);
v___x_2327_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_2323_, v___f_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object* v___f_2328_, lean_object* v_ch_2329_, lean_object* v_waiter_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2328_, v_ch_2329_, v_waiter_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object* v___y_2333_, lean_object* v___f_2334_, lean_object* v_x_2335_){
_start:
{
if (lean_obj_tag(v_x_2335_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v___f_2334_);
v_a_2337_ = lean_ctor_get(v_x_2335_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_x_2335_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2339_ = v_x_2335_;
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v_x_2335_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
}
}
else
{
lean_object* v_a_2346_; uint8_t v___x_2347_; 
v_a_2346_ = lean_ctor_get(v_x_2335_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v_x_2335_, 1);
v___x_2347_ = lean_unbox(v_a_2346_);
lean_dec(v_a_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec_ref(v___f_2334_);
v___x_2348_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_2348_;
}
else
{
lean_object* v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = 0;
v___x_2351_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2333_);
v___x_2352_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2349_, v___x_2350_, v___x_2351_, v___f_2334_);
return v___x_2352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object* v___y_2353_, lean_object* v___f_2354_, lean_object* v_x_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2353_, v___f_2354_, v_x_2355_);
lean_dec(v___y_2353_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object* v___f_2358_, lean_object* v___f_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___f_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_inc(v___y_2360_);
v___f_2362_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2362_, 0, v___y_2360_);
lean_closure_set(v___f_2362_, 1, v___f_2358_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = 0;
v___x_2365_ = lean_st_ref_get(v___y_2360_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
v___x_2368_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2363_, v___x_2364_, v___x_2367_, v___f_2359_);
v___x_2369_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2363_, v___x_2364_, v___x_2368_, v___f_2362_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object* v___f_2370_, lean_object* v___f_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2370_, v___f_2371_, v___y_2372_);
lean_dec(v___y_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object* v_producers_2375_, uint8_t v_closed_2376_, lean_object* v___y_2377_, lean_object* v_x_2378_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v_producers_2375_);
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
lean_object* v_a_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_a_2389_ = lean_ctor_get(v_x_2378_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v_x_2378_, 1);
v___x_2390_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2390_, 0, v_producers_2375_);
lean_ctor_set(v___x_2390_, 1, v_a_2389_);
lean_ctor_set_uint8(v___x_2390_, sizeof(void*)*2, v_closed_2376_);
v___x_2391_ = lean_st_ref_swap(v___y_2377_, v___x_2390_);
lean_dec(v___x_2391_);
v___x_2392_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object* v_producers_2393_, lean_object* v_closed_2394_, lean_object* v___y_2395_, lean_object* v_x_2396_, lean_object* v___y_2397_){
_start:
{
uint8_t v_closed_boxed_2398_; lean_object* v_res_2399_; 
v_closed_boxed_2398_ = lean_unbox(v_closed_2394_);
v_res_2399_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2393_, v_closed_boxed_2398_, v___y_2395_, v_x_2396_);
lean_dec(v___y_2395_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_2400_, lean_object* v_x_2401_, lean_object* v_head_2402_, lean_object* v_x_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2400_, v_x_2401_, v_head_2402_, v_x_2403_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
if (lean_obj_tag(v_x_2406_) == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v_x_2407_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
else
{
lean_object* v_head_2411_; lean_object* v_tail_2412_; lean_object* v___f_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v_head_2411_ = lean_ctor_get(v_x_2406_, 0);
lean_inc_n(v_head_2411_, 2);
v_tail_2412_ = lean_ctor_get(v_x_2406_, 1);
lean_inc(v_tail_2412_);
lean_dec_ref_known(v_x_2406_, 2);
v___f_2413_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2413_, 0, v_tail_2412_);
lean_closure_set(v___f_2413_, 1, v_x_2407_);
lean_closure_set(v___f_2413_, 2, v_head_2411_);
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = 0;
if (lean_obj_tag(v_head_2411_) == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec_ref_known(v_head_2411_, 1);
v___x_2416_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_2417_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2414_, v___x_2415_, v___x_2416_, v___f_2413_);
return v___x_2417_;
}
else
{
lean_object* v_finished_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2431_; 
v_finished_2418_ = lean_ctor_get(v_head_2411_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_head_2411_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2420_ = v_head_2411_;
v_isShared_2421_ = v_isSharedCheck_2431_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_finished_2418_);
lean_dec(v_head_2411_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2431_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_finished_2422_; lean_object* v___f_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v_finished_2422_ = lean_ctor_get(v_finished_2418_, 0);
lean_inc(v_finished_2422_);
lean_dec_ref(v_finished_2418_);
v___f_2423_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_2424_ = lean_st_ref_get(v_finished_2422_);
lean_dec(v_finished_2422_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2424_);
v___x_2426_ = v___x_2420_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
v___x_2428_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2414_, v___x_2415_, v___x_2427_, v___f_2423_);
v___x_2429_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2414_, v___x_2415_, v___x_2428_, v___f_2413_);
return v___x_2429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_2432_, lean_object* v_x_2433_, lean_object* v_head_2434_, lean_object* v_x_2435_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2445_; 
lean_dec_ref(v_head_2434_);
lean_dec(v_x_2433_);
lean_dec(v_tail_2432_);
v_a_2437_ = lean_ctor_get(v_x_2435_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_x_2435_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2439_ = v_x_2435_;
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v_x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2437_);
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
else
{
lean_object* v_a_2446_; uint8_t v___x_2447_; 
v_a_2446_ = lean_ctor_get(v_x_2435_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v_x_2435_, 1);
v___x_2447_ = lean_unbox(v_a_2446_);
lean_dec(v_a_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref(v_head_2434_);
v___x_2448_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2432_, v_x_2433_);
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2449_, 0, v_head_2434_);
lean_ctor_set(v___x_2449_, 1, v_x_2433_);
v___x_2450_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2432_, v___x_2449_);
return v___x_2450_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object* v_x_2451_, lean_object* v_x_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2451_, v_x_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object* v___x_2455_, lean_object* v_eList_2456_, lean_object* v___f_2457_, lean_object* v_x_2458_){
_start:
{
if (lean_obj_tag(v_x_2458_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v___f_2457_);
lean_dec(v_eList_2456_);
lean_dec(v___x_2455_);
v_a_2460_ = lean_ctor_get(v_x_2458_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_x_2458_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2462_ = v_x_2458_;
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v_x_2458_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___f_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_a_2469_ = lean_ctor_get(v_x_2458_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v_x_2458_, 1);
lean_inc(v___x_2455_);
v___f_2470_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2470_, 0, v_a_2469_);
lean_closure_set(v___f_2470_, 1, v___x_2455_);
v___x_2471_ = lean_unsigned_to_nat(0u);
v___x_2472_ = 0;
v___x_2473_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_2456_, v___x_2455_);
v___x_2474_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2471_, v___x_2472_, v___x_2473_, v___f_2457_);
v___x_2475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2471_, v___x_2472_, v___x_2474_, v___f_2470_);
return v___x_2475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v___x_2476_, lean_object* v_eList_2477_, lean_object* v___f_2478_, lean_object* v_x_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v___x_2476_, v_eList_2477_, v___f_2478_, v_x_2479_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object* v_q_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_eList_2485_; lean_object* v_dList_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_eList_2485_ = lean_ctor_get(v_q_2482_, 0);
lean_inc(v_eList_2485_);
v_dList_2486_ = lean_ctor_get(v_q_2482_, 1);
lean_inc(v_dList_2486_);
lean_dec_ref(v_q_2482_);
v___f_2487_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_2488_ = lean_box(0);
v___f_2489_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2489_, 0, v___x_2488_);
lean_closure_set(v___f_2489_, 1, v_eList_2485_);
lean_closure_set(v___f_2489_, 2, v___f_2487_);
v___x_2490_ = lean_unsigned_to_nat(0u);
v___x_2491_ = 0;
v___x_2492_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_2486_, v___x_2488_);
v___x_2493_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2490_, v___x_2491_, v___x_2492_, v___f_2487_);
v___x_2494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2490_, v___x_2491_, v___x_2493_, v___f_2489_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object* v_q_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2495_, v___y_2496_);
lean_dec(v___y_2496_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object* v___y_2499_, lean_object* v_x_2500_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2510_; 
v_a_2502_ = lean_ctor_get(v_x_2500_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_x_2500_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2504_ = v_x_2500_;
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v_x_2500_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v_producers_2512_; lean_object* v_consumers_2513_; uint8_t v_closed_2514_; lean_object* v___x_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_a_2511_ = lean_ctor_get(v_x_2500_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v_x_2500_, 1);
v_producers_2512_ = lean_ctor_get(v_a_2511_, 0);
lean_inc_ref(v_producers_2512_);
v_consumers_2513_ = lean_ctor_get(v_a_2511_, 1);
lean_inc_ref(v_consumers_2513_);
v_closed_2514_ = lean_ctor_get_uint8(v_a_2511_, sizeof(void*)*2);
lean_dec(v_a_2511_);
v___x_2515_ = lean_box(v_closed_2514_);
lean_inc(v___y_2499_);
v___f_2516_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2516_, 0, v_producers_2512_);
lean_closure_set(v___f_2516_, 1, v___x_2515_);
lean_closure_set(v___f_2516_, 2, v___y_2499_);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = 0;
v___x_2519_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_2513_, v___y_2499_);
v___x_2520_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2517_, v___x_2518_, v___x_2519_, v___f_2516_);
return v___x_2520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object* v___y_2521_, lean_object* v_x_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2521_, v_x_2522_);
lean_dec(v___y_2521_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object* v___y_2525_){
_start:
{
lean_object* v___f_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_inc(v___y_2525_);
v___f_2527_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2527_, 0, v___y_2525_);
v___x_2528_ = lean_unsigned_to_nat(0u);
v___x_2529_ = 0;
v___x_2530_ = lean_st_ref_get(v___y_2525_);
v___x_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
v___x_2533_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2528_, v___x_2529_, v___x_2532_, v___f_2527_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2534_);
lean_dec(v___y_2534_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object* v_ch_2542_){
_start:
{
lean_object* v___f_2543_; lean_object* v___f_2544_; lean_object* v___f_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___f_2543_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0));
lean_inc_ref_n(v_ch_2542_, 2);
v___f_2544_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2544_, 0, v___f_2543_);
lean_closure_set(v___f_2544_, 1, v_ch_2542_);
v___f_2545_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1));
v___f_2546_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2));
v___x_2547_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2547_, 0, lean_box(0));
lean_closure_set(v___x_2547_, 1, lean_box(0));
lean_closure_set(v___x_2547_, 2, v_ch_2542_);
lean_closure_set(v___x_2547_, 3, v___f_2545_);
v___x_2548_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2548_, 0, lean_box(0));
lean_closure_set(v___x_2548_, 1, lean_box(0));
lean_closure_set(v___x_2548_, 2, v_ch_2542_);
lean_closure_set(v___x_2548_, 3, v___f_2546_);
v___x_2549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___f_2544_);
lean_ctor_set(v___x_2549_, 2, v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object* v_00_u03b1_2550_, lean_object* v_ch_2551_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object* v_00_u03b1_2553_, lean_object* v_q_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2554_, v___y_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_2558_, lean_object* v_q_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_2558_, v_q_2559_, v___y_2560_);
lean_dec(v___y_2560_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object* v_00_u03b1_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2564_, v_x_2565_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_2569_, v_x_2570_, v_x_2571_, v___y_2572_);
lean_dec(v___y_2572_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object* v_c_2575_, uint8_t v_b_2576_){
_start:
{
lean_object* v_promise_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_promise_2578_ = lean_ctor_get(v_c_2575_, 0);
v___x_2579_ = lean_box(v_b_2576_);
v___x_2580_ = lean_io_promise_resolve(v___x_2579_, v_promise_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object* v_c_2581_, lean_object* v_b_2582_, lean_object* v_a_2583_){
_start:
{
uint8_t v_b_boxed_2584_; lean_object* v_res_2585_; 
v_b_boxed_2584_ = lean_unbox(v_b_2582_);
v_res_2585_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2581_, v_b_boxed_2584_);
lean_dec_ref(v_c_2581_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object* v_00_u03b1_2586_, lean_object* v_c_2587_, uint8_t v_b_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2587_, v_b_2588_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object* v_00_u03b1_2591_, lean_object* v_c_2592_, lean_object* v_b_2593_, lean_object* v_a_2594_){
_start:
{
uint8_t v_b_boxed_2595_; lean_object* v_res_2596_; 
v_b_boxed_2595_ = lean_unbox(v_b_2593_);
v_res_2596_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(v_00_u03b1_2591_, v_c_2592_, v_b_boxed_2595_);
lean_dec_ref(v_c_2592_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object* v_x_2597_){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_box(0);
v___x_2600_ = lean_st_mk_ref(v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2601_);
lean_dec(v_x_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object* v_n_2604_, lean_object* v_f_2605_, lean_object* v_xs_2606_, lean_object* v_k_2607_, lean_object* v_acc_2608_){
_start:
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_nat_dec_lt(v_k_2607_, v_n_2604_);
if (v___x_2610_ == 0)
{
lean_dec(v_k_2607_);
lean_dec_ref(v_f_2605_);
return v_acc_2608_;
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2611_ = lean_array_fget_borrowed(v_xs_2606_, v_k_2607_);
lean_inc_ref(v_f_2605_);
lean_inc(v___x_2611_);
v___x_2612_ = lean_apply_2(v_f_2605_, v___x_2611_, lean_box(0));
v___x_2613_ = lean_unsigned_to_nat(1u);
v___x_2614_ = lean_nat_add(v_k_2607_, v___x_2613_);
lean_dec(v_k_2607_);
v___x_2615_ = lean_array_push(v_acc_2608_, v___x_2612_);
v_k_2607_ = v___x_2614_;
v_acc_2608_ = v___x_2615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_2617_, lean_object* v_f_2618_, lean_object* v_xs_2619_, lean_object* v_k_2620_, lean_object* v_acc_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2617_, v_f_2618_, v_xs_2619_, v_k_2620_, v_acc_2621_);
lean_dec_ref(v_xs_2619_);
lean_dec(v_n_2617_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object* v_capacity_2627_){
_start:
{
lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___f_2629_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0));
lean_inc(v_capacity_2627_);
v___x_2630_ = l_Array_range(v_capacity_2627_);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1));
v___x_2633_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_2627_, v___f_2629_, v___x_2630_, v___x_2631_, v___x_2632_);
lean_dec_ref(v___x_2630_);
v___x_2634_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2635_ = 0;
v___x_2636_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2636_, 0, v___x_2634_);
lean_ctor_set(v___x_2636_, 1, v___x_2634_);
lean_ctor_set(v___x_2636_, 2, v_capacity_2627_);
lean_ctor_set(v___x_2636_, 3, v___x_2633_);
lean_ctor_set(v___x_2636_, 4, v___x_2631_);
lean_ctor_set(v___x_2636_, 5, v___x_2631_);
lean_ctor_set(v___x_2636_, 6, v___x_2631_);
lean_ctor_set_uint8(v___x_2636_, sizeof(void*)*7, v___x_2635_);
v___x_2637_ = l_Std_Mutex_new___redArg(v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object* v_capacity_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2638_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object* v_00_u03b1_2641_, lean_object* v_capacity_2642_, lean_object* v_hcap_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2642_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object* v_00_u03b1_2646_, lean_object* v_capacity_2647_, lean_object* v_hcap_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(v_00_u03b1_2646_, v_capacity_2647_, v_hcap_2648_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object* v_00_u03b1_2651_, lean_object* v_00_u03b2_2652_, lean_object* v_n_2653_, lean_object* v_f_2654_, lean_object* v_xs_2655_, lean_object* v_k_2656_, lean_object* v_h_2657_, lean_object* v_acc_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2653_, v_f_2654_, v_xs_2655_, v_k_2656_, v_acc_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_2661_, lean_object* v_00_u03b2_2662_, lean_object* v_n_2663_, lean_object* v_f_2664_, lean_object* v_xs_2665_, lean_object* v_k_2666_, lean_object* v_h_2667_, lean_object* v_acc_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_2661_, v_00_u03b2_2662_, v_n_2663_, v_f_2664_, v_xs_2665_, v_k_2666_, v_h_2667_, v_acc_2668_);
lean_dec_ref(v_xs_2665_);
lean_dec(v_n_2663_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object* v_idx_2671_, lean_object* v_cap_2672_){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2673_ = lean_unsigned_to_nat(1u);
v___x_2674_ = lean_nat_add(v_idx_2671_, v___x_2673_);
v___x_2675_ = lean_nat_dec_eq(v___x_2674_, v_cap_2672_);
if (v___x_2675_ == 0)
{
return v___x_2674_;
}
else
{
lean_object* v___x_2676_; 
lean_dec(v___x_2674_);
v___x_2676_ = lean_unsigned_to_nat(0u);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object* v_idx_2677_, lean_object* v_cap_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(v_idx_2677_, v_cap_2678_);
lean_dec(v_cap_2678_);
lean_dec(v_idx_2677_);
return v_res_2679_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object* v_v_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_st_2684_; lean_object* v___y_2685_; lean_object* v___x_2688_; lean_object* v_producers_2689_; lean_object* v_consumers_2690_; lean_object* v_capacity_2691_; lean_object* v_buf_2692_; lean_object* v_bufCount_2693_; lean_object* v_sendIdx_2694_; lean_object* v_recvIdx_2695_; uint8_t v_closed_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2722_; 
v___x_2688_ = lean_st_ref_get(v_a_2681_);
v_producers_2689_ = lean_ctor_get(v___x_2688_, 0);
v_consumers_2690_ = lean_ctor_get(v___x_2688_, 1);
v_capacity_2691_ = lean_ctor_get(v___x_2688_, 2);
v_buf_2692_ = lean_ctor_get(v___x_2688_, 3);
v_bufCount_2693_ = lean_ctor_get(v___x_2688_, 4);
v_sendIdx_2694_ = lean_ctor_get(v___x_2688_, 5);
v_recvIdx_2695_ = lean_ctor_get(v___x_2688_, 6);
v_closed_2696_ = lean_ctor_get_uint8(v___x_2688_, sizeof(void*)*7);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2698_ = v___x_2688_;
v_isShared_2699_ = v_isSharedCheck_2722_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_recvIdx_2695_);
lean_inc(v_sendIdx_2694_);
lean_inc(v_bufCount_2693_);
lean_inc(v_buf_2692_);
lean_inc(v_capacity_2691_);
lean_inc(v_consumers_2690_);
lean_inc(v_producers_2689_);
lean_dec(v___x_2688_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2722_;
goto v_resetjp_2697_;
}
v___jp_2683_:
{
lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2686_ = lean_st_ref_swap(v___y_2685_, v_st_2684_);
lean_dec(v___x_2686_);
v___x_2687_ = 1;
return v___x_2687_;
}
v_resetjp_2697_:
{
uint8_t v___x_2700_; 
v___x_2700_ = lean_nat_dec_eq(v_bufCount_2693_, v_capacity_2691_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___y_2707_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2701_ = lean_array_fget_borrowed(v_buf_2692_, v_sendIdx_2694_);
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v_v_2680_);
v___x_2703_ = lean_st_ref_swap(v___x_2701_, v___x_2702_);
lean_dec(v___x_2703_);
v___x_2704_ = lean_unsigned_to_nat(1u);
v___x_2705_ = lean_nat_add(v_bufCount_2693_, v___x_2704_);
lean_dec(v_bufCount_2693_);
v___x_2718_ = lean_nat_add(v_sendIdx_2694_, v___x_2704_);
lean_dec(v_sendIdx_2694_);
v___x_2719_ = lean_nat_dec_eq(v___x_2718_, v_capacity_2691_);
if (v___x_2719_ == 0)
{
v___y_2707_ = v___x_2718_;
goto v___jp_2706_;
}
else
{
lean_object* v___x_2720_; 
lean_dec(v___x_2718_);
v___x_2720_ = lean_unsigned_to_nat(0u);
v___y_2707_ = v___x_2720_;
goto v___jp_2706_;
}
v___jp_2706_:
{
lean_object* v___x_2709_; 
lean_inc(v_recvIdx_2695_);
lean_inc(v___y_2707_);
lean_inc(v___x_2705_);
lean_inc_ref(v_buf_2692_);
lean_inc(v_capacity_2691_);
lean_inc_ref(v_consumers_2690_);
lean_inc_ref(v_producers_2689_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 5, v___y_2707_);
lean_ctor_set(v___x_2698_, 4, v___x_2705_);
v___x_2709_ = v___x_2698_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_producers_2689_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_consumers_2690_);
lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_capacity_2691_);
lean_ctor_set(v_reuseFailAlloc_2717_, 3, v_buf_2692_);
lean_ctor_set(v_reuseFailAlloc_2717_, 4, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2717_, 5, v___y_2707_);
lean_ctor_set(v_reuseFailAlloc_2717_, 6, v_recvIdx_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*7, v_closed_2696_);
v___x_2709_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_2690_);
if (lean_obj_tag(v___x_2710_) == 1)
{
lean_object* v_val_2711_; lean_object* v_fst_2712_; lean_object* v_snd_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec_ref(v___x_2709_);
v_val_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v_fst_2712_ = lean_ctor_get(v_val_2711_, 0);
lean_inc(v_fst_2712_);
v_snd_2713_ = lean_ctor_get(v_val_2711_, 1);
lean_inc(v_snd_2713_);
lean_dec(v_val_2711_);
v___x_2714_ = 1;
v___x_2715_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_2712_, v___x_2714_);
lean_dec(v_fst_2712_);
v___x_2716_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2716_, 0, v_producers_2689_);
lean_ctor_set(v___x_2716_, 1, v_snd_2713_);
lean_ctor_set(v___x_2716_, 2, v_capacity_2691_);
lean_ctor_set(v___x_2716_, 3, v_buf_2692_);
lean_ctor_set(v___x_2716_, 4, v___x_2705_);
lean_ctor_set(v___x_2716_, 5, v___y_2707_);
lean_ctor_set(v___x_2716_, 6, v_recvIdx_2695_);
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*7, v_closed_2696_);
v_st_2684_ = v___x_2716_;
v___y_2685_ = v_a_2681_;
goto v___jp_2683_;
}
else
{
lean_dec(v___x_2710_);
lean_dec(v___y_2707_);
lean_dec(v___x_2705_);
lean_dec(v_recvIdx_2695_);
lean_dec_ref(v_buf_2692_);
lean_dec(v_capacity_2691_);
lean_dec_ref(v_producers_2689_);
v_st_2684_ = v___x_2709_;
v___y_2685_ = v_a_2681_;
goto v___jp_2683_;
}
}
}
}
else
{
uint8_t v___x_2721_; 
lean_del_object(v___x_2698_);
lean_dec(v_recvIdx_2695_);
lean_dec(v_sendIdx_2694_);
lean_dec(v_bufCount_2693_);
lean_dec_ref(v_buf_2692_);
lean_dec(v_capacity_2691_);
lean_dec_ref(v_consumers_2690_);
lean_dec_ref(v_producers_2689_);
lean_dec(v_v_2680_);
v___x_2721_ = 0;
return v___x_2721_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
uint8_t v_res_2726_; lean_object* v_r_2727_; 
v_res_2726_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2723_, v_a_2724_);
lean_dec(v_a_2724_);
v_r_2727_ = lean_box(v_res_2726_);
return v_r_2727_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object* v_00_u03b1_2728_, lean_object* v_v_2729_, lean_object* v_a_2730_){
_start:
{
uint8_t v___x_2732_; 
v___x_2732_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2729_, v_a_2730_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_2733_, lean_object* v_v_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
uint8_t v_res_2737_; lean_object* v_r_2738_; 
v_res_2737_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(v_00_u03b1_2733_, v_v_2734_, v_a_2735_);
lean_dec(v_a_2735_);
v_r_2738_ = lean_box(v_res_2737_);
return v_r_2738_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object* v_v_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; uint8_t v_closed_2743_; 
v___x_2742_ = lean_st_ref_get(v___y_2740_);
v_closed_2743_ = lean_ctor_get_uint8(v___x_2742_, sizeof(void*)*7);
lean_dec(v___x_2742_);
if (v_closed_2743_ == 0)
{
uint8_t v___x_2744_; 
v___x_2744_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2739_, v___y_2740_);
return v___x_2744_;
}
else
{
uint8_t v___x_2745_; 
lean_dec(v_v_2739_);
v___x_2745_ = 0;
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v_res_2749_; lean_object* v_r_2750_; 
v_res_2749_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2746_, v___y_2747_);
lean_dec(v___y_2747_);
v_r_2750_ = lean_box(v_res_2749_);
return v_r_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object* v_ch_2751_, lean_object* v_v_2752_){
_start:
{
lean_object* v___f_2754_; lean_object* v___x_2755_; 
v___f_2754_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2754_, 0, v_v_2752_);
v___x_2755_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2751_, v___f_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object* v_ch_2756_, lean_object* v_v_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2756_, v_v_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object* v_00_u03b1_2760_, lean_object* v_ch_2761_, lean_object* v_v_2762_){
_start:
{
lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2764_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2761_, v_v_2762_);
v___x_2765_ = lean_unbox(v___x_2764_);
lean_dec(v___x_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(lean_object* v_00_u03b1_2766_, lean_object* v_ch_2767_, lean_object* v_v_2768_, lean_object* v_a_2769_){
_start:
{
uint8_t v_res_2770_; lean_object* v_r_2771_; 
v_res_2770_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(v_00_u03b1_2766_, v_ch_2767_, v_v_2768_);
v_r_2771_ = lean_box(v_res_2770_);
return v_r_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(lean_object* v_v_2772_, lean_object* v___f_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; uint8_t v_closed_2777_; 
v___x_2776_ = lean_st_ref_get(v___y_2774_);
v_closed_2777_ = lean_ctor_get_uint8(v___x_2776_, sizeof(void*)*7);
lean_dec(v___x_2776_);
if (v_closed_2777_ == 0)
{
uint8_t v___x_2778_; 
v___x_2778_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2772_, v___y_2774_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v_producers_2781_; lean_object* v_consumers_2782_; lean_object* v_capacity_2783_; lean_object* v_buf_2784_; lean_object* v_bufCount_2785_; lean_object* v_sendIdx_2786_; lean_object* v_recvIdx_2787_; uint8_t v_closed_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2800_; 
v___x_2779_ = lean_io_promise_new();
v___x_2780_ = lean_st_ref_take(v___y_2774_);
v_producers_2781_ = lean_ctor_get(v___x_2780_, 0);
v_consumers_2782_ = lean_ctor_get(v___x_2780_, 1);
v_capacity_2783_ = lean_ctor_get(v___x_2780_, 2);
v_buf_2784_ = lean_ctor_get(v___x_2780_, 3);
v_bufCount_2785_ = lean_ctor_get(v___x_2780_, 4);
v_sendIdx_2786_ = lean_ctor_get(v___x_2780_, 5);
v_recvIdx_2787_ = lean_ctor_get(v___x_2780_, 6);
v_closed_2788_ = lean_ctor_get_uint8(v___x_2780_, sizeof(void*)*7);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2790_ = v___x_2780_;
v_isShared_2791_ = v_isSharedCheck_2800_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_recvIdx_2787_);
lean_inc(v_sendIdx_2786_);
lean_inc(v_bufCount_2785_);
lean_inc(v_buf_2784_);
lean_inc(v_capacity_2783_);
lean_inc(v_consumers_2782_);
lean_inc(v_producers_2781_);
lean_dec(v___x_2780_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2800_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2792_; lean_object* v___x_2794_; 
lean_inc(v___x_2779_);
v___x_2792_ = l_Std_Queue_enqueue___redArg(v___x_2779_, v_producers_2781_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2792_);
v___x_2794_ = v___x_2790_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_consumers_2782_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_capacity_2783_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v_buf_2784_);
lean_ctor_set(v_reuseFailAlloc_2799_, 4, v_bufCount_2785_);
lean_ctor_set(v_reuseFailAlloc_2799_, 5, v_sendIdx_2786_);
lean_ctor_set(v_reuseFailAlloc_2799_, 6, v_recvIdx_2787_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*7, v_closed_2788_);
v___x_2794_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2795_ = lean_st_ref_put(v___y_2774_, v___x_2794_);
v___x_2796_ = lean_io_promise_result_opt(v___x_2779_);
lean_dec(v___x_2779_);
v___x_2797_ = lean_unsigned_to_nat(0u);
v___x_2798_ = lean_io_bind_task(v___x_2796_, v___f_2773_, v___x_2797_, v___x_2778_);
return v___x_2798_;
}
}
}
else
{
lean_object* v___x_2801_; 
lean_dec_ref(v___f_2773_);
v___x_2801_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_2801_;
}
}
else
{
lean_object* v___x_2802_; 
lean_dec_ref(v___f_2773_);
lean_dec(v_v_2772_);
v___x_2802_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_2803_, lean_object* v___f_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(v_v_2803_, v___f_2804_, v___y_2805_);
lean_dec(v___y_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(lean_object* v_ch_2808_, lean_object* v_v_2809_, lean_object* v_res_2810_){
_start:
{
if (lean_obj_tag(v_res_2810_) == 0)
{
lean_dec(v_v_2809_);
lean_dec_ref(v_ch_2808_);
goto v___jp_2812_;
}
else
{
lean_object* v_val_2814_; uint8_t v___x_2815_; 
v_val_2814_ = lean_ctor_get(v_res_2810_, 0);
v___x_2815_ = lean_unbox(v_val_2814_);
if (v___x_2815_ == 0)
{
lean_dec(v_v_2809_);
lean_dec_ref(v_ch_2808_);
goto v___jp_2812_;
}
else
{
lean_object* v___x_2816_; 
v___x_2816_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2808_, v_v_2809_);
return v___x_2816_;
}
}
v___jp_2812_:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_2817_, lean_object* v_v_2818_, lean_object* v_res_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(v_ch_2817_, v_v_2818_, v_res_2819_);
lean_dec(v_res_2819_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(lean_object* v_ch_2822_, lean_object* v_v_2823_){
_start:
{
lean_object* v___f_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; 
lean_inc(v_v_2823_);
lean_inc_ref(v_ch_2822_);
v___f_2825_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2825_, 0, v_ch_2822_);
lean_closure_set(v___f_2825_, 1, v_v_2823_);
v___f_2826_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2826_, 0, v_v_2823_);
lean_closure_set(v___f_2826_, 1, v___f_2825_);
v___x_2827_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2822_, v___f_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(lean_object* v_ch_2828_, lean_object* v_v_2829_, lean_object* v_a_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2828_, v_v_2829_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_object* v_00_u03b1_2832_, lean_object* v_ch_2833_, lean_object* v_v_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2833_, v_v_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_ch_2838_, lean_object* v_v_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(v_00_u03b1_2837_, v_ch_2838_, v_v_2839_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t v___x_2842_, lean_object* v_as_2843_, size_t v_sz_2844_, size_t v_i_2845_, lean_object* v_b_2846_){
_start:
{
uint8_t v___x_2848_; 
v___x_2848_ = lean_usize_dec_lt(v_i_2845_, v_sz_2844_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v_b_2846_);
return v___x_2849_;
}
else
{
lean_object* v___x_2850_; lean_object* v_a_2851_; lean_object* v___x_2852_; size_t v___x_2853_; size_t v___x_2854_; 
v___x_2850_ = lean_box(0);
v_a_2851_ = lean_array_uget_borrowed(v_as_2843_, v_i_2845_);
v___x_2852_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_2851_, v___x_2842_);
v___x_2853_ = ((size_t)1ULL);
v___x_2854_ = lean_usize_add(v_i_2845_, v___x_2853_);
v_i_2845_ = v___x_2854_;
v_b_2846_ = v___x_2850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_2856_, lean_object* v_as_2857_, lean_object* v_sz_2858_, lean_object* v_i_2859_, lean_object* v_b_2860_, lean_object* v___y_2861_){
_start:
{
uint8_t v___x_1125__boxed_2862_; size_t v_sz_boxed_2863_; size_t v_i_boxed_2864_; lean_object* v_res_2865_; 
v___x_1125__boxed_2862_ = lean_unbox(v___x_2856_);
v_sz_boxed_2863_ = lean_unbox_usize(v_sz_2858_);
lean_dec(v_sz_2858_);
v_i_boxed_2864_ = lean_unbox_usize(v_i_2859_);
lean_dec(v_i_2859_);
v_res_2865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1125__boxed_2862_, v_as_2857_, v_sz_boxed_2863_, v_i_boxed_2864_, v_b_2860_);
lean_dec_ref(v_as_2857_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; uint8_t v_closed_2869_; 
v___x_2868_ = lean_st_ref_get(v___y_2866_);
v_closed_2869_ = lean_ctor_get_uint8(v___x_2868_, sizeof(void*)*7);
if (v_closed_2869_ == 0)
{
lean_object* v_producers_2870_; lean_object* v_consumers_2871_; lean_object* v_capacity_2872_; lean_object* v_buf_2873_; lean_object* v_bufCount_2874_; lean_object* v_sendIdx_2875_; lean_object* v_recvIdx_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2899_; 
v_producers_2870_ = lean_ctor_get(v___x_2868_, 0);
v_consumers_2871_ = lean_ctor_get(v___x_2868_, 1);
v_capacity_2872_ = lean_ctor_get(v___x_2868_, 2);
v_buf_2873_ = lean_ctor_get(v___x_2868_, 3);
v_bufCount_2874_ = lean_ctor_get(v___x_2868_, 4);
v_sendIdx_2875_ = lean_ctor_get(v___x_2868_, 5);
v_recvIdx_2876_ = lean_ctor_get(v___x_2868_, 6);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2878_ = v___x_2868_;
v_isShared_2879_ = v_isSharedCheck_2899_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_recvIdx_2876_);
lean_inc(v_sendIdx_2875_);
lean_inc(v_bufCount_2874_);
lean_inc(v_buf_2873_);
lean_inc(v_capacity_2872_);
lean_inc(v_consumers_2871_);
lean_inc(v_producers_2870_);
lean_dec(v___x_2868_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2899_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; size_t v_sz_2882_; size_t v___x_2883_; lean_object* v___x_2884_; 
v___x_2880_ = l_Std_Queue_toArray___redArg(v_consumers_2871_);
v___x_2881_ = lean_box(0);
v_sz_2882_ = lean_array_size(v___x_2880_);
v___x_2883_ = ((size_t)0ULL);
v___x_2884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_2869_, v___x_2880_, v_sz_2882_, v___x_2883_, v___x_2881_);
lean_dec_ref(v___x_2880_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2897_; 
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v___x_2884_, 0);
lean_dec(v_unused_2898_);
v___x_2886_ = v___x_2884_;
v_isShared_2887_ = v_isSharedCheck_2897_;
goto v_resetjp_2885_;
}
else
{
lean_dec(v___x_2884_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2897_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; uint8_t v___x_2889_; lean_object* v___x_2891_; 
v___x_2888_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2889_ = 1;
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 1, v___x_2888_);
v___x_2891_ = v___x_2878_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_producers_2870_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_capacity_2872_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_buf_2873_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v_bufCount_2874_);
lean_ctor_set(v_reuseFailAlloc_2896_, 5, v_sendIdx_2875_);
lean_ctor_set(v_reuseFailAlloc_2896_, 6, v_recvIdx_2876_);
v___x_2891_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*7, v___x_2889_);
v___x_2892_ = lean_st_ref_swap(v___y_2866_, v___x_2891_);
lean_dec(v___x_2892_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2881_);
v___x_2894_ = v___x_2886_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2881_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
else
{
lean_del_object(v___x_2878_);
lean_dec(v_recvIdx_2876_);
lean_dec(v_sendIdx_2875_);
lean_dec(v_bufCount_2874_);
lean_dec_ref(v_buf_2873_);
lean_dec(v_capacity_2872_);
lean_dec_ref(v_producers_2870_);
return v___x_2884_;
}
}
}
else
{
uint8_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec(v___x_2868_);
v___x_2900_ = 1;
v___x_2901_ = lean_box(v___x_2900_);
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_2903_);
lean_dec(v___y_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_2907_){
_start:
{
lean_object* v___f_2909_; lean_object* v___x_2910_; 
v___f_2909_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_2910_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_2907_, v___f_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_2914_, lean_object* v_ch_2915_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_2918_, lean_object* v_ch_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_2918_, v_ch_2919_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_2922_, uint8_t v___x_2923_, lean_object* v_as_2924_, size_t v_sz_2925_, size_t v_i_2926_, lean_object* v_b_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_2923_, v_as_2924_, v_sz_2925_, v_i_2926_, v_b_2927_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_2931_, lean_object* v___x_2932_, lean_object* v_as_2933_, lean_object* v_sz_2934_, lean_object* v_i_2935_, lean_object* v_b_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
uint8_t v___x_1221__boxed_2939_; size_t v_sz_boxed_2940_; size_t v_i_boxed_2941_; lean_object* v_res_2942_; 
v___x_1221__boxed_2939_ = lean_unbox(v___x_2932_);
v_sz_boxed_2940_ = lean_unbox_usize(v_sz_2934_);
lean_dec(v_sz_2934_);
v_i_boxed_2941_ = lean_unbox_usize(v_i_2935_);
lean_dec(v_i_2935_);
v_res_2942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_2931_, v___x_1221__boxed_2939_, v_as_2933_, v_sz_boxed_2940_, v_i_boxed_2941_, v_b_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v_as_2933_);
return v_res_2942_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_2943_){
_start:
{
lean_object* v___x_2945_; uint8_t v_closed_2946_; 
v___x_2945_ = lean_st_ref_get(v___y_2943_);
v_closed_2946_ = lean_ctor_get_uint8(v___x_2945_, sizeof(void*)*7);
lean_dec(v___x_2945_);
return v_closed_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v_res_2949_; lean_object* v_r_2950_; 
v_res_2949_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_2947_);
lean_dec(v___y_2947_);
v_r_2950_ = lean_box(v_res_2949_);
return v_r_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_2952_){
_start:
{
lean_object* v___f_2954_; lean_object* v___x_2955_; 
v___f_2954_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_2955_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2952_, v___f_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_2956_);
return v_res_2958_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_2959_, lean_object* v_ch_2960_){
_start:
{
lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_2960_);
v___x_2963_ = lean_unbox(v___x_2962_);
lean_dec(v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_2964_, lean_object* v_ch_2965_, lean_object* v_a_2966_){
_start:
{
uint8_t v_res_2967_; lean_object* v_r_2968_; 
v_res_2967_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_2964_, v_ch_2965_);
v_r_2968_ = lean_box(v_res_2967_);
return v_r_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_toPure_2972_; lean_object* v___x_2973_; 
v_toPure_2972_ = lean_ctor_get(v_toApplicative_2969_, 1);
lean_inc(v_toPure_2972_);
lean_dec_ref(v_toApplicative_2969_);
v___x_2973_ = lean_apply_2(v_toPure_2972_, lean_box(0), v_a_2970_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_2974_, lean_object* v_toBind_2975_, lean_object* v___f_2976_, lean_object* v_____r_2977_, lean_object* v_st_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_inc(v___y_2979_);
v___x_2980_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_2980_, 0, lean_box(0));
lean_closure_set(v___x_2980_, 1, lean_box(0));
lean_closure_set(v___x_2980_, 2, v___y_2979_);
lean_closure_set(v___x_2980_, 3, v_st_2978_);
v___x_2981_ = lean_apply_2(v_inst_2974_, lean_box(0), v___x_2980_);
v___x_2982_ = lean_apply_4(v_toBind_2975_, lean_box(0), lean_box(0), v___x_2981_, v___f_2976_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_inst_2983_, lean_object* v_toBind_2984_, lean_object* v___f_2985_, lean_object* v_____r_2986_, lean_object* v_st_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_2983_, v_toBind_2984_, v___f_2985_, v_____r_2986_, v_st_2987_, v___y_2988_);
lean_dec(v___y_2988_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_2990_, lean_object* v_consumers_2991_, lean_object* v_capacity_2992_, lean_object* v_buf_2993_, lean_object* v___x_2994_, lean_object* v_sendIdx_2995_, lean_object* v___y_2996_, uint8_t v_closed_2997_, lean_object* v___f_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3001_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3001_, 0, v_snd_2990_);
lean_ctor_set(v___x_3001_, 1, v_consumers_2991_);
lean_ctor_set(v___x_3001_, 2, v_capacity_2992_);
lean_ctor_set(v___x_3001_, 3, v_buf_2993_);
lean_ctor_set(v___x_3001_, 4, v___x_2994_);
lean_ctor_set(v___x_3001_, 5, v_sendIdx_2995_);
lean_ctor_set(v___x_3001_, 6, v___y_2996_);
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*7, v_closed_2997_);
v___x_3002_ = lean_box(0);
lean_inc(v_a_2999_);
v___x_3003_ = lean_apply_3(v___f_2998_, v___x_3002_, v___x_3001_, v_a_2999_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_3004_, lean_object* v_consumers_3005_, lean_object* v_capacity_3006_, lean_object* v_buf_3007_, lean_object* v___x_3008_, lean_object* v_sendIdx_3009_, lean_object* v___y_3010_, lean_object* v_closed_3011_, lean_object* v___f_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
uint8_t v_closed_boxed_3015_; lean_object* v_res_3016_; 
v_closed_boxed_3015_ = lean_unbox(v_closed_3011_);
v_res_3016_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3004_, v_consumers_3005_, v_capacity_3006_, v_buf_3007_, v___x_3008_, v_sendIdx_3009_, v___y_3010_, v_closed_boxed_3015_, v___f_3012_, v_a_3013_, v_a_3014_);
lean_dec(v_a_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3017_, lean_object* v_inst_3018_, lean_object* v_toBind_3019_, lean_object* v_bufCount_3020_, lean_object* v_producers_3021_, lean_object* v_consumers_3022_, lean_object* v_capacity_3023_, lean_object* v_buf_3024_, lean_object* v_sendIdx_3025_, uint8_t v_closed_3026_, lean_object* v_a_3027_, uint8_t v___x_3028_, lean_object* v_inst_3029_, lean_object* v_recvIdx_3030_, lean_object* v___x_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v___f_3033_; lean_object* v___f_3034_; lean_object* v___y_3036_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___f_3033_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3033_, 0, v_toApplicative_3017_);
lean_closure_set(v___f_3033_, 1, v_a_3032_);
lean_inc_ref(v___f_3033_);
lean_inc(v_toBind_3019_);
lean_inc(v_inst_3018_);
v___f_3034_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3034_, 0, v_inst_3018_);
lean_closure_set(v___f_3034_, 1, v_toBind_3019_);
lean_closure_set(v___f_3034_, 2, v___f_3033_);
v___x_3052_ = lean_unsigned_to_nat(1u);
v___x_3053_ = lean_nat_add(v_recvIdx_3030_, v___x_3052_);
v___x_3054_ = lean_nat_dec_eq(v___x_3053_, v_capacity_3023_);
if (v___x_3054_ == 0)
{
lean_dec(v___x_3031_);
v___y_3036_ = v___x_3053_;
goto v___jp_3035_;
}
else
{
lean_dec(v___x_3053_);
v___y_3036_ = v___x_3031_;
goto v___jp_3035_;
}
v___jp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3037_ = lean_unsigned_to_nat(1u);
v___x_3038_ = lean_nat_sub(v_bufCount_3020_, v___x_3037_);
lean_inc(v___y_3036_);
lean_inc(v_sendIdx_3025_);
lean_inc(v___x_3038_);
lean_inc_ref(v_buf_3024_);
lean_inc(v_capacity_3023_);
lean_inc_ref(v_consumers_3022_);
lean_inc_ref(v_producers_3021_);
v___x_3039_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3039_, 0, v_producers_3021_);
lean_ctor_set(v___x_3039_, 1, v_consumers_3022_);
lean_ctor_set(v___x_3039_, 2, v_capacity_3023_);
lean_ctor_set(v___x_3039_, 3, v_buf_3024_);
lean_ctor_set(v___x_3039_, 4, v___x_3038_);
lean_ctor_set(v___x_3039_, 5, v_sendIdx_3025_);
lean_ctor_set(v___x_3039_, 6, v___y_3036_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*7, v_closed_3026_);
v___x_3040_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3021_);
if (lean_obj_tag(v___x_3040_) == 1)
{
lean_object* v_val_3041_; lean_object* v_fst_3042_; lean_object* v_snd_3043_; lean_object* v___x_3044_; lean_object* v___f_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_dec_ref_known(v___x_3039_, 7);
lean_dec_ref(v___f_3033_);
lean_dec(v_inst_3018_);
v_val_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_val_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v_fst_3042_ = lean_ctor_get(v_val_3041_, 0);
lean_inc(v_fst_3042_);
v_snd_3043_ = lean_ctor_get(v_val_3041_, 1);
lean_inc(v_snd_3043_);
lean_dec(v_val_3041_);
v___x_3044_ = lean_box(v_closed_3026_);
lean_inc(v_a_3027_);
v___f_3045_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3045_, 0, v_snd_3043_);
lean_closure_set(v___f_3045_, 1, v_consumers_3022_);
lean_closure_set(v___f_3045_, 2, v_capacity_3023_);
lean_closure_set(v___f_3045_, 3, v_buf_3024_);
lean_closure_set(v___f_3045_, 4, v___x_3038_);
lean_closure_set(v___f_3045_, 5, v_sendIdx_3025_);
lean_closure_set(v___f_3045_, 6, v___y_3036_);
lean_closure_set(v___f_3045_, 7, v___x_3044_);
lean_closure_set(v___f_3045_, 8, v___f_3034_);
lean_closure_set(v___f_3045_, 9, v_a_3027_);
v___x_3046_ = lean_box(v___x_3028_);
v___x_3047_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3047_, 0, lean_box(0));
lean_closure_set(v___x_3047_, 1, v___x_3046_);
lean_closure_set(v___x_3047_, 2, v_fst_3042_);
v___x_3048_ = lean_apply_2(v_inst_3029_, lean_box(0), v___x_3047_);
v___x_3049_ = lean_apply_4(v_toBind_3019_, lean_box(0), lean_box(0), v___x_3048_, v___f_3045_);
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec(v___x_3040_);
lean_dec(v___x_3038_);
lean_dec(v___y_3036_);
lean_dec_ref(v___f_3034_);
lean_dec(v_inst_3029_);
lean_dec(v_sendIdx_3025_);
lean_dec_ref(v_buf_3024_);
lean_dec(v_capacity_3023_);
lean_dec_ref(v_consumers_3022_);
v___x_3050_ = lean_box(0);
v___x_3051_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3018_, v_toBind_3019_, v___f_3033_, v___x_3050_, v___x_3039_, v_a_3027_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3055_, lean_object* v_inst_3056_, lean_object* v_toBind_3057_, lean_object* v_bufCount_3058_, lean_object* v_producers_3059_, lean_object* v_consumers_3060_, lean_object* v_capacity_3061_, lean_object* v_buf_3062_, lean_object* v_sendIdx_3063_, lean_object* v_closed_3064_, lean_object* v_a_3065_, lean_object* v___x_3066_, lean_object* v_inst_3067_, lean_object* v_recvIdx_3068_, lean_object* v___x_3069_, lean_object* v_a_3070_){
_start:
{
uint8_t v_closed_boxed_3071_; uint8_t v___x_543__boxed_3072_; lean_object* v_res_3073_; 
v_closed_boxed_3071_ = lean_unbox(v_closed_3064_);
v___x_543__boxed_3072_ = lean_unbox(v___x_3066_);
v_res_3073_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3055_, v_inst_3056_, v_toBind_3057_, v_bufCount_3058_, v_producers_3059_, v_consumers_3060_, v_capacity_3061_, v_buf_3062_, v_sendIdx_3063_, v_closed_boxed_3071_, v_a_3065_, v___x_543__boxed_3072_, v_inst_3067_, v_recvIdx_3068_, v___x_3069_, v_a_3070_);
lean_dec(v_recvIdx_3068_);
lean_dec(v_a_3065_);
lean_dec(v_bufCount_3058_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3074_, lean_object* v_inst_3075_, lean_object* v_toBind_3076_, lean_object* v_a_3077_, lean_object* v_inst_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_producers_3080_; lean_object* v_consumers_3081_; lean_object* v_capacity_3082_; lean_object* v_buf_3083_; lean_object* v_bufCount_3084_; lean_object* v_sendIdx_3085_; lean_object* v_recvIdx_3086_; uint8_t v_closed_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_producers_3080_ = lean_ctor_get(v_a_3079_, 0);
lean_inc_ref(v_producers_3080_);
v_consumers_3081_ = lean_ctor_get(v_a_3079_, 1);
lean_inc_ref(v_consumers_3081_);
v_capacity_3082_ = lean_ctor_get(v_a_3079_, 2);
lean_inc(v_capacity_3082_);
v_buf_3083_ = lean_ctor_get(v_a_3079_, 3);
lean_inc_ref(v_buf_3083_);
v_bufCount_3084_ = lean_ctor_get(v_a_3079_, 4);
lean_inc(v_bufCount_3084_);
v_sendIdx_3085_ = lean_ctor_get(v_a_3079_, 5);
lean_inc(v_sendIdx_3085_);
v_recvIdx_3086_ = lean_ctor_get(v_a_3079_, 6);
lean_inc(v_recvIdx_3086_);
v_closed_3087_ = lean_ctor_get_uint8(v_a_3079_, sizeof(void*)*7);
lean_dec_ref(v_a_3079_);
v___x_3088_ = lean_unsigned_to_nat(0u);
v___x_3089_ = lean_nat_dec_eq(v_bufCount_3084_, v___x_3088_);
if (v___x_3089_ == 0)
{
uint8_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___f_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3090_ = 1;
v___x_3091_ = lean_box(v_closed_3087_);
v___x_3092_ = lean_box(v___x_3090_);
lean_inc(v_recvIdx_3086_);
lean_inc(v_a_3077_);
lean_inc_ref(v_buf_3083_);
lean_inc(v_toBind_3076_);
lean_inc(v_inst_3075_);
v___f_3093_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3093_, 0, v_toApplicative_3074_);
lean_closure_set(v___f_3093_, 1, v_inst_3075_);
lean_closure_set(v___f_3093_, 2, v_toBind_3076_);
lean_closure_set(v___f_3093_, 3, v_bufCount_3084_);
lean_closure_set(v___f_3093_, 4, v_producers_3080_);
lean_closure_set(v___f_3093_, 5, v_consumers_3081_);
lean_closure_set(v___f_3093_, 6, v_capacity_3082_);
lean_closure_set(v___f_3093_, 7, v_buf_3083_);
lean_closure_set(v___f_3093_, 8, v_sendIdx_3085_);
lean_closure_set(v___f_3093_, 9, v___x_3091_);
lean_closure_set(v___f_3093_, 10, v_a_3077_);
lean_closure_set(v___f_3093_, 11, v___x_3092_);
lean_closure_set(v___f_3093_, 12, v_inst_3078_);
lean_closure_set(v___f_3093_, 13, v_recvIdx_3086_);
lean_closure_set(v___f_3093_, 14, v___x_3088_);
v___x_3094_ = lean_array_fget(v_buf_3083_, v_recvIdx_3086_);
lean_dec(v_recvIdx_3086_);
lean_dec_ref(v_buf_3083_);
v___x_3095_ = lean_box(0);
v___x_3096_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3096_, 0, lean_box(0));
lean_closure_set(v___x_3096_, 1, lean_box(0));
lean_closure_set(v___x_3096_, 2, v___x_3094_);
lean_closure_set(v___x_3096_, 3, v___x_3095_);
v___x_3097_ = lean_apply_2(v_inst_3075_, lean_box(0), v___x_3096_);
v___x_3098_ = lean_apply_4(v_toBind_3076_, lean_box(0), lean_box(0), v___x_3097_, v___f_3093_);
return v___x_3098_;
}
else
{
lean_object* v_toPure_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_dec(v_recvIdx_3086_);
lean_dec(v_sendIdx_3085_);
lean_dec(v_bufCount_3084_);
lean_dec_ref(v_buf_3083_);
lean_dec(v_capacity_3082_);
lean_dec_ref(v_consumers_3081_);
lean_dec_ref(v_producers_3080_);
lean_dec(v_inst_3078_);
lean_dec(v_toBind_3076_);
lean_dec(v_inst_3075_);
v_toPure_3099_ = lean_ctor_get(v_toApplicative_3074_, 1);
lean_inc(v_toPure_3099_);
lean_dec_ref(v_toApplicative_3074_);
v___x_3100_ = lean_box(0);
v___x_3101_ = lean_apply_2(v_toPure_3099_, lean_box(0), v___x_3100_);
return v___x_3101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_3102_, lean_object* v_inst_3103_, lean_object* v_toBind_3104_, lean_object* v_a_3105_, lean_object* v_inst_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(v_toApplicative_3102_, v_inst_3103_, v_toBind_3104_, v_a_3105_, v_inst_3106_, v_a_3107_);
lean_dec(v_a_3105_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_inst_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_toApplicative_3113_; lean_object* v_toBind_3114_; lean_object* v___f_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_toApplicative_3113_ = lean_ctor_get(v_inst_3109_, 0);
lean_inc_ref(v_toApplicative_3113_);
v_toBind_3114_ = lean_ctor_get(v_inst_3109_, 1);
lean_inc_n(v_toBind_3114_, 2);
lean_dec_ref(v_inst_3109_);
lean_inc_n(v_a_3112_, 2);
lean_inc(v_inst_3110_);
v___f_3115_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_3115_, 0, v_toApplicative_3113_);
lean_closure_set(v___f_3115_, 1, v_inst_3110_);
lean_closure_set(v___f_3115_, 2, v_toBind_3114_);
lean_closure_set(v___f_3115_, 3, v_a_3112_);
lean_closure_set(v___f_3115_, 4, v_inst_3111_);
v___x_3116_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3116_, 0, lean_box(0));
lean_closure_set(v___x_3116_, 1, lean_box(0));
lean_closure_set(v___x_3116_, 2, v_a_3112_);
v___x_3117_ = lean_apply_2(v_inst_3110_, lean_box(0), v___x_3116_);
v___x_3118_ = lean_apply_4(v_toBind_3114_, lean_box(0), lean_box(0), v___x_3117_, v___f_3115_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3119_, v_inst_3120_, v_inst_3121_, v_a_3122_);
lean_dec(v_a_3122_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3124_, lean_object* v_00_u03b1_3125_, lean_object* v_inst_3126_, lean_object* v_inst_3127_, lean_object* v_inst_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3126_, v_inst_3127_, v_inst_3128_, v_a_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object* v_m_3131_, lean_object* v_00_u03b1_3132_, lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_inst_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(v_m_3131_, v_00_u03b1_3132_, v_inst_3133_, v_inst_3134_, v_inst_3135_, v_a_3136_);
lean_dec(v_a_3136_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v_producers_3141_; lean_object* v_consumers_3142_; lean_object* v_capacity_3143_; lean_object* v_buf_3144_; lean_object* v_bufCount_3145_; lean_object* v_sendIdx_3146_; lean_object* v_recvIdx_3147_; uint8_t v_closed_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3180_; 
v___x_3140_ = lean_st_ref_get(v_a_3138_);
v_producers_3141_ = lean_ctor_get(v___x_3140_, 0);
v_consumers_3142_ = lean_ctor_get(v___x_3140_, 1);
v_capacity_3143_ = lean_ctor_get(v___x_3140_, 2);
v_buf_3144_ = lean_ctor_get(v___x_3140_, 3);
v_bufCount_3145_ = lean_ctor_get(v___x_3140_, 4);
v_sendIdx_3146_ = lean_ctor_get(v___x_3140_, 5);
v_recvIdx_3147_ = lean_ctor_get(v___x_3140_, 6);
v_closed_3148_ = lean_ctor_get_uint8(v___x_3140_, sizeof(void*)*7);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3150_ = v___x_3140_;
v_isShared_3151_ = v_isSharedCheck_3180_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_recvIdx_3147_);
lean_inc(v_sendIdx_3146_);
lean_inc(v_bufCount_3145_);
lean_inc(v_buf_3144_);
lean_inc(v_capacity_3143_);
lean_inc(v_consumers_3142_);
lean_inc(v_producers_3141_);
lean_dec(v___x_3140_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3180_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = lean_nat_dec_eq(v_bufCount_3145_, v___x_3152_);
if (v___x_3153_ == 0)
{
uint8_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v_st_3159_; lean_object* v___y_3160_; lean_object* v___y_3163_; lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3154_ = 1;
v___x_3155_ = lean_array_fget_borrowed(v_buf_3144_, v_recvIdx_3147_);
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_st_ref_swap(v___x_3155_, v___x_3156_);
v___x_3176_ = lean_unsigned_to_nat(1u);
v___x_3177_ = lean_nat_add(v_recvIdx_3147_, v___x_3176_);
lean_dec(v_recvIdx_3147_);
v___x_3178_ = lean_nat_dec_eq(v___x_3177_, v_capacity_3143_);
if (v___x_3178_ == 0)
{
v___y_3163_ = v___x_3177_;
goto v___jp_3162_;
}
else
{
lean_dec(v___x_3177_);
v___y_3163_ = v___x_3152_;
goto v___jp_3162_;
}
v___jp_3158_:
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_st_ref_swap(v___y_3160_, v_st_3159_);
lean_dec(v___x_3161_);
return v___x_3157_;
}
v___jp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3165_ = lean_nat_sub(v_bufCount_3145_, v___x_3164_);
lean_dec(v_bufCount_3145_);
lean_inc(v___y_3163_);
lean_inc(v_sendIdx_3146_);
lean_inc(v___x_3165_);
lean_inc_ref(v_buf_3144_);
lean_inc(v_capacity_3143_);
lean_inc_ref(v_consumers_3142_);
lean_inc_ref(v_producers_3141_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 6, v___y_3163_);
lean_ctor_set(v___x_3150_, 4, v___x_3165_);
v___x_3167_ = v___x_3150_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_producers_3141_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_consumers_3142_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_capacity_3143_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v_buf_3144_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3175_, 5, v_sendIdx_3146_);
lean_ctor_set(v_reuseFailAlloc_3175_, 6, v___y_3163_);
lean_ctor_set_uint8(v_reuseFailAlloc_3175_, sizeof(void*)*7, v_closed_3148_);
v___x_3167_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3141_);
if (lean_obj_tag(v___x_3168_) == 1)
{
lean_object* v_val_3169_; lean_object* v_fst_3170_; lean_object* v_snd_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec_ref(v___x_3167_);
v_val_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_val_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v_fst_3170_ = lean_ctor_get(v_val_3169_, 0);
lean_inc(v_fst_3170_);
v_snd_3171_ = lean_ctor_get(v_val_3169_, 1);
lean_inc(v_snd_3171_);
lean_dec(v_val_3169_);
v___x_3172_ = lean_box(v___x_3154_);
v___x_3173_ = lean_io_promise_resolve(v___x_3172_, v_fst_3170_);
lean_dec(v_fst_3170_);
v___x_3174_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3174_, 0, v_snd_3171_);
lean_ctor_set(v___x_3174_, 1, v_consumers_3142_);
lean_ctor_set(v___x_3174_, 2, v_capacity_3143_);
lean_ctor_set(v___x_3174_, 3, v_buf_3144_);
lean_ctor_set(v___x_3174_, 4, v___x_3165_);
lean_ctor_set(v___x_3174_, 5, v_sendIdx_3146_);
lean_ctor_set(v___x_3174_, 6, v___y_3163_);
lean_ctor_set_uint8(v___x_3174_, sizeof(void*)*7, v_closed_3148_);
v_st_3159_ = v___x_3174_;
v___y_3160_ = v_a_3138_;
goto v___jp_3158_;
}
else
{
lean_dec(v___x_3168_);
lean_dec(v___x_3165_);
lean_dec(v___y_3163_);
lean_dec(v_sendIdx_3146_);
lean_dec_ref(v_buf_3144_);
lean_dec(v_capacity_3143_);
lean_dec_ref(v_consumers_3142_);
v_st_3159_ = v___x_3167_;
v___y_3160_ = v_a_3138_;
goto v___jp_3158_;
}
}
}
}
else
{
lean_object* v___x_3179_; 
lean_del_object(v___x_3150_);
lean_dec(v_recvIdx_3147_);
lean_dec(v_sendIdx_3146_);
lean_dec(v_bufCount_3145_);
lean_dec_ref(v_buf_3144_);
lean_dec(v_capacity_3143_);
lean_dec_ref(v_consumers_3142_);
lean_dec_ref(v_producers_3141_);
v___x_3179_ = lean_box(0);
return v___x_3179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3181_);
lean_dec(v_a_3181_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3185_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3188_, lean_object* v_a_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3188_, v_a_3189_);
lean_dec(v_a_3189_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3193_){
_start:
{
lean_object* v___f_3195_; lean_object* v___x_3196_; 
v___f_3195_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3196_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3193_, v___f_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3197_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3200_, lean_object* v_ch_3201_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3201_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3204_, lean_object* v_ch_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3204_, v_ch_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3209_);
if (lean_obj_tag(v___x_3211_) == 1)
{
lean_object* v___x_3212_; 
lean_dec_ref(v___f_3208_);
v___x_3212_ = lean_task_pure(v___x_3211_);
return v___x_3212_;
}
else
{
lean_object* v___x_3213_; uint8_t v_closed_3214_; 
lean_dec(v___x_3211_);
v___x_3213_ = lean_st_ref_get(v___y_3209_);
v_closed_3214_ = lean_ctor_get_uint8(v___x_3213_, sizeof(void*)*7);
lean_dec(v___x_3213_);
if (v_closed_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v_producers_3217_; lean_object* v_consumers_3218_; lean_object* v_capacity_3219_; lean_object* v_buf_3220_; lean_object* v_bufCount_3221_; lean_object* v_sendIdx_3222_; lean_object* v_recvIdx_3223_; uint8_t v_closed_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3238_; 
v___x_3215_ = lean_io_promise_new();
v___x_3216_ = lean_st_ref_take(v___y_3209_);
v_producers_3217_ = lean_ctor_get(v___x_3216_, 0);
v_consumers_3218_ = lean_ctor_get(v___x_3216_, 1);
v_capacity_3219_ = lean_ctor_get(v___x_3216_, 2);
v_buf_3220_ = lean_ctor_get(v___x_3216_, 3);
v_bufCount_3221_ = lean_ctor_get(v___x_3216_, 4);
v_sendIdx_3222_ = lean_ctor_get(v___x_3216_, 5);
v_recvIdx_3223_ = lean_ctor_get(v___x_3216_, 6);
v_closed_3224_ = lean_ctor_get_uint8(v___x_3216_, sizeof(void*)*7);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3226_ = v___x_3216_;
v_isShared_3227_ = v_isSharedCheck_3238_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_recvIdx_3223_);
lean_inc(v_sendIdx_3222_);
lean_inc(v_bufCount_3221_);
lean_inc(v_buf_3220_);
lean_inc(v_capacity_3219_);
lean_inc(v_consumers_3218_);
lean_inc(v_producers_3217_);
lean_dec(v___x_3216_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3238_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3228_ = lean_box(0);
lean_inc(v___x_3215_);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3215_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = l_Std_Queue_enqueue___redArg(v___x_3229_, v_consumers_3218_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 1, v___x_3230_);
v___x_3232_ = v___x_3226_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_producers_3217_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3237_, 2, v_capacity_3219_);
lean_ctor_set(v_reuseFailAlloc_3237_, 3, v_buf_3220_);
lean_ctor_set(v_reuseFailAlloc_3237_, 4, v_bufCount_3221_);
lean_ctor_set(v_reuseFailAlloc_3237_, 5, v_sendIdx_3222_);
lean_ctor_set(v_reuseFailAlloc_3237_, 6, v_recvIdx_3223_);
lean_ctor_set_uint8(v_reuseFailAlloc_3237_, sizeof(void*)*7, v_closed_3224_);
v___x_3232_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3233_ = lean_st_ref_put(v___y_3209_, v___x_3232_);
v___x_3234_ = lean_io_promise_result_opt(v___x_3215_);
lean_dec(v___x_3215_);
v___x_3235_ = lean_unsigned_to_nat(0u);
v___x_3236_ = lean_io_bind_task(v___x_3234_, v___f_3208_, v___x_3235_, v_closed_3214_);
return v___x_3236_;
}
}
}
else
{
lean_object* v___x_3239_; 
lean_dec_ref(v___f_3208_);
v___x_3239_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3240_, v___y_3241_);
lean_dec(v___y_3241_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3244_, lean_object* v_res_3245_){
_start:
{
if (lean_obj_tag(v_res_3245_) == 0)
{
lean_dec_ref(v_ch_3244_);
goto v___jp_3247_;
}
else
{
lean_object* v_val_3249_; uint8_t v___x_3250_; 
v_val_3249_ = lean_ctor_get(v_res_3245_, 0);
v___x_3250_ = lean_unbox(v_val_3249_);
if (v___x_3250_ == 0)
{
lean_dec_ref(v_ch_3244_);
goto v___jp_3247_;
}
else
{
lean_object* v___x_3251_; 
v___x_3251_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3244_);
return v___x_3251_;
}
}
v___jp_3247_:
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3252_, lean_object* v_res_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3252_, v_res_3253_);
lean_dec(v_res_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3256_){
_start:
{
lean_object* v___f_3258_; lean_object* v___f_3259_; lean_object* v___x_3260_; 
lean_inc_ref(v_ch_3256_);
v___f_3258_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3258_, 0, v_ch_3256_);
v___f_3259_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3259_, 0, v___f_3258_);
v___x_3260_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3256_, v___f_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3264_, lean_object* v_ch_3265_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3268_, lean_object* v_ch_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3268_, v_ch_3269_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3272_, lean_object* v_a_3273_){
_start:
{
uint8_t v___y_3275_; lean_object* v_bufCount_3279_; uint8_t v_closed_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v_bufCount_3279_ = lean_ctor_get(v_a_3273_, 4);
v_closed_3280_ = lean_ctor_get_uint8(v_a_3273_, sizeof(void*)*7);
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = lean_nat_dec_eq(v_bufCount_3279_, v___x_3281_);
if (v___x_3282_ == 0)
{
uint8_t v___x_3283_; 
v___x_3283_ = 1;
v___y_3275_ = v___x_3283_;
goto v___jp_3274_;
}
else
{
v___y_3275_ = v_closed_3280_;
goto v___jp_3274_;
}
v___jp_3274_:
{
lean_object* v_toPure_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_toPure_3276_ = lean_ctor_get(v_toApplicative_3272_, 1);
lean_inc(v_toPure_3276_);
lean_dec_ref(v_toApplicative_3272_);
v___x_3277_ = lean_box(v___y_3275_);
v___x_3278_ = lean_apply_2(v_toPure_3276_, lean_box(0), v___x_3277_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3284_, v_a_3285_);
lean_dec_ref(v_a_3285_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_toApplicative_3290_; lean_object* v_toBind_3291_; lean_object* v___f_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v_toApplicative_3290_ = lean_ctor_get(v_inst_3287_, 0);
lean_inc_ref(v_toApplicative_3290_);
v_toBind_3291_ = lean_ctor_get(v_inst_3287_, 1);
lean_inc(v_toBind_3291_);
lean_dec_ref(v_inst_3287_);
v___f_3292_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3292_, 0, v_toApplicative_3290_);
lean_inc(v_a_3289_);
v___x_3293_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3293_, 0, lean_box(0));
lean_closure_set(v___x_3293_, 1, lean_box(0));
lean_closure_set(v___x_3293_, 2, v_a_3289_);
v___x_3294_ = lean_apply_2(v_inst_3288_, lean_box(0), v___x_3293_);
v___x_3295_ = lean_apply_4(v_toBind_3291_, lean_box(0), lean_box(0), v___x_3294_, v___f_3292_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object* v_inst_3296_, lean_object* v_inst_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(v_inst_3296_, v_inst_3297_, v_a_3298_);
lean_dec(v_a_3298_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3300_, lean_object* v_00_u03b1_3301_, lean_object* v_inst_3302_, lean_object* v_inst_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v_toApplicative_3305_; lean_object* v_toBind_3306_; lean_object* v___f_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_toApplicative_3305_ = lean_ctor_get(v_inst_3302_, 0);
lean_inc_ref(v_toApplicative_3305_);
v_toBind_3306_ = lean_ctor_get(v_inst_3302_, 1);
lean_inc(v_toBind_3306_);
lean_dec_ref(v_inst_3302_);
v___f_3307_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3307_, 0, v_toApplicative_3305_);
lean_inc(v_a_3304_);
v___x_3308_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3308_, 0, lean_box(0));
lean_closure_set(v___x_3308_, 1, lean_box(0));
lean_closure_set(v___x_3308_, 2, v_a_3304_);
v___x_3309_ = lean_apply_2(v_inst_3303_, lean_box(0), v___x_3308_);
v___x_3310_ = lean_apply_4(v_toBind_3306_, lean_box(0), lean_box(0), v___x_3309_, v___f_3307_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object* v_m_3311_, lean_object* v_00_u03b1_3312_, lean_object* v_inst_3313_, lean_object* v_inst_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(v_m_3311_, v_00_u03b1_3312_, v_inst_3313_, v_inst_3314_, v_a_3315_);
lean_dec(v_a_3315_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3317_){
_start:
{
lean_object* v___x_3319_; lean_object* v_producers_3320_; lean_object* v_consumers_3321_; lean_object* v_capacity_3322_; lean_object* v_buf_3323_; lean_object* v_bufCount_3324_; lean_object* v_sendIdx_3325_; lean_object* v_recvIdx_3326_; uint8_t v_closed_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3361_; 
v___x_3319_ = lean_st_ref_get(v_a_3317_);
v_producers_3320_ = lean_ctor_get(v___x_3319_, 0);
v_consumers_3321_ = lean_ctor_get(v___x_3319_, 1);
v_capacity_3322_ = lean_ctor_get(v___x_3319_, 2);
v_buf_3323_ = lean_ctor_get(v___x_3319_, 3);
v_bufCount_3324_ = lean_ctor_get(v___x_3319_, 4);
v_sendIdx_3325_ = lean_ctor_get(v___x_3319_, 5);
v_recvIdx_3326_ = lean_ctor_get(v___x_3319_, 6);
v_closed_3327_ = lean_ctor_get_uint8(v___x_3319_, sizeof(void*)*7);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3329_ = v___x_3319_;
v_isShared_3330_ = v_isSharedCheck_3361_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_recvIdx_3326_);
lean_inc(v_sendIdx_3325_);
lean_inc(v_bufCount_3324_);
lean_inc(v_buf_3323_);
lean_inc(v_capacity_3322_);
lean_inc(v_consumers_3321_);
lean_inc(v_producers_3320_);
lean_dec(v___x_3319_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3361_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = lean_nat_dec_eq(v_bufCount_3324_, v___x_3331_);
if (v___x_3332_ == 0)
{
uint8_t v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v_st_3338_; lean_object* v___y_3339_; lean_object* v___y_3343_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3333_ = 1;
v___x_3334_ = lean_array_fget_borrowed(v_buf_3323_, v_recvIdx_3326_);
v___x_3335_ = lean_box(0);
v___x_3336_ = lean_st_ref_swap(v___x_3334_, v___x_3335_);
v___x_3356_ = lean_unsigned_to_nat(1u);
v___x_3357_ = lean_nat_add(v_recvIdx_3326_, v___x_3356_);
lean_dec(v_recvIdx_3326_);
v___x_3358_ = lean_nat_dec_eq(v___x_3357_, v_capacity_3322_);
if (v___x_3358_ == 0)
{
v___y_3343_ = v___x_3357_;
goto v___jp_3342_;
}
else
{
lean_dec(v___x_3357_);
v___y_3343_ = v___x_3331_;
goto v___jp_3342_;
}
v___jp_3337_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_st_ref_swap(v___y_3339_, v_st_3338_);
lean_dec(v___x_3340_);
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3336_);
return v___x_3341_;
}
v___jp_3342_:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3344_ = lean_unsigned_to_nat(1u);
v___x_3345_ = lean_nat_sub(v_bufCount_3324_, v___x_3344_);
lean_dec(v_bufCount_3324_);
lean_inc(v___y_3343_);
lean_inc(v_sendIdx_3325_);
lean_inc(v___x_3345_);
lean_inc_ref(v_buf_3323_);
lean_inc(v_capacity_3322_);
lean_inc_ref(v_consumers_3321_);
lean_inc_ref(v_producers_3320_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 6, v___y_3343_);
lean_ctor_set(v___x_3329_, 4, v___x_3345_);
v___x_3347_ = v___x_3329_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_producers_3320_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_consumers_3321_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_capacity_3322_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_buf_3323_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3355_, 5, v_sendIdx_3325_);
lean_ctor_set(v_reuseFailAlloc_3355_, 6, v___y_3343_);
lean_ctor_set_uint8(v_reuseFailAlloc_3355_, sizeof(void*)*7, v_closed_3327_);
v___x_3347_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3320_);
if (lean_obj_tag(v___x_3348_) == 1)
{
lean_object* v_val_3349_; lean_object* v_fst_3350_; lean_object* v_snd_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_dec_ref(v___x_3347_);
v_val_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_val_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v_fst_3350_ = lean_ctor_get(v_val_3349_, 0);
lean_inc(v_fst_3350_);
v_snd_3351_ = lean_ctor_get(v_val_3349_, 1);
lean_inc(v_snd_3351_);
lean_dec(v_val_3349_);
v___x_3352_ = lean_box(v___x_3333_);
v___x_3353_ = lean_io_promise_resolve(v___x_3352_, v_fst_3350_);
lean_dec(v_fst_3350_);
v___x_3354_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3354_, 0, v_snd_3351_);
lean_ctor_set(v___x_3354_, 1, v_consumers_3321_);
lean_ctor_set(v___x_3354_, 2, v_capacity_3322_);
lean_ctor_set(v___x_3354_, 3, v_buf_3323_);
lean_ctor_set(v___x_3354_, 4, v___x_3345_);
lean_ctor_set(v___x_3354_, 5, v_sendIdx_3325_);
lean_ctor_set(v___x_3354_, 6, v___y_3343_);
lean_ctor_set_uint8(v___x_3354_, sizeof(void*)*7, v_closed_3327_);
v_st_3338_ = v___x_3354_;
v___y_3339_ = v_a_3317_;
goto v___jp_3337_;
}
else
{
lean_dec(v___x_3348_);
lean_dec(v___x_3345_);
lean_dec(v___y_3343_);
lean_dec(v_sendIdx_3325_);
lean_dec_ref(v_buf_3323_);
lean_dec(v_capacity_3322_);
lean_dec_ref(v_consumers_3321_);
v_st_3338_ = v___x_3347_;
v___y_3339_ = v_a_3317_;
goto v___jp_3337_;
}
}
}
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_del_object(v___x_3329_);
lean_dec(v_recvIdx_3326_);
lean_dec(v_sendIdx_3325_);
lean_dec(v_bufCount_3324_);
lean_dec_ref(v_buf_3323_);
lean_dec(v_capacity_3322_);
lean_dec_ref(v_consumers_3321_);
lean_dec_ref(v_producers_3320_);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
return v___x_3360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3362_);
lean_dec(v_a_3362_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3366_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3369_, lean_object* v_a_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3369_, v_a_3370_);
lean_dec(v_a_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3373_, lean_object* v_lose_3374_){
_start:
{
lean_object* v_finished_3376_; lean_object* v_promise_3377_; lean_object* v___x_3378_; uint8_t v___y_3380_; uint8_t v___x_3388_; 
v_finished_3376_ = lean_ctor_get(v_w_3373_, 0);
v_promise_3377_ = lean_ctor_get(v_w_3373_, 1);
v___x_3378_ = lean_st_ref_take(v_finished_3376_);
v___x_3388_ = lean_unbox(v___x_3378_);
lean_dec(v___x_3378_);
if (v___x_3388_ == 0)
{
uint8_t v___x_3389_; 
v___x_3389_ = 1;
v___y_3380_ = v___x_3389_;
goto v___jp_3379_;
}
else
{
uint8_t v___x_3390_; 
v___x_3390_ = 0;
v___y_3380_ = v___x_3390_;
goto v___jp_3379_;
}
v___jp_3379_:
{
uint8_t v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = 1;
v___x_3382_ = lean_box(v___x_3381_);
v___x_3383_ = lean_st_ref_put(v_finished_3376_, v___x_3382_);
if (v___y_3380_ == 0)
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_apply_1(v_lose_3374_, lean_box(0));
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec_ref(v_lose_3374_);
v___x_3385_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__2));
v___x_3386_ = lean_io_promise_resolve(v___x_3385_, v_promise_3377_);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
return v___x_3387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3391_, lean_object* v_lose_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3391_, v_lose_3392_);
lean_dec_ref(v_w_3391_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3395_, lean_object* v_w_3396_, lean_object* v_lose_3397_){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3396_, v_lose_3397_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3400_, lean_object* v_w_3401_, lean_object* v_lose_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3400_, v_w_3401_, v_lose_3402_);
lean_dec_ref(v_w_3401_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3405_, lean_object* v_lose_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_finished_3409_; lean_object* v_promise_3410_; lean_object* v___x_3411_; uint8_t v___y_3413_; uint8_t v___x_3429_; 
v_finished_3409_ = lean_ctor_get(v_w_3405_, 0);
v_promise_3410_ = lean_ctor_get(v_w_3405_, 1);
v___x_3411_ = lean_st_ref_take(v_finished_3409_);
v___x_3429_ = lean_unbox(v___x_3411_);
lean_dec(v___x_3411_);
if (v___x_3429_ == 0)
{
uint8_t v___x_3430_; 
v___x_3430_ = 1;
v___y_3413_ = v___x_3430_;
goto v___jp_3412_;
}
else
{
uint8_t v___x_3431_; 
v___x_3431_ = 0;
v___y_3413_ = v___x_3431_;
goto v___jp_3412_;
}
v___jp_3412_:
{
uint8_t v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3414_ = 1;
v___x_3415_ = lean_box(v___x_3414_);
v___x_3416_ = lean_st_ref_put(v_finished_3409_, v___x_3415_);
if (v___y_3413_ == 0)
{
lean_object* v___x_3417_; 
lean_inc(v___y_3407_);
v___x_3417_ = lean_apply_2(v_lose_3406_, v___y_3407_, lean_box(0));
return v___x_3417_;
}
else
{
lean_object* v___x_3418_; lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3428_; 
lean_dec_ref(v_lose_3406_);
v___x_3418_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3407_);
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3428_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3428_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
v___x_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3423_, 0, v_a_3419_);
v___x_3424_ = lean_io_promise_resolve(v___x_3423_, v_promise_3410_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3424_);
v___x_3426_ = v___x_3421_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3432_, lean_object* v_lose_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3432_, v_lose_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v_w_3432_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3437_, lean_object* v_w_3438_, lean_object* v_lose_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3438_, v_lose_3439_, v___y_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3443_, lean_object* v_w_3444_, lean_object* v_lose_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3443_, v_w_3444_, v_lose_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v_w_3444_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3449_, lean_object* v_k_3450_){
_start:
{
lean_object* v_ref_3452_; lean_object* v_mutex_3453_; lean_object* v___x_3454_; lean_object* v_r_3455_; 
v_ref_3452_ = lean_ctor_get(v_mutex_3449_, 0);
lean_inc(v_ref_3452_);
v_mutex_3453_ = lean_ctor_get(v_mutex_3449_, 1);
lean_inc(v_mutex_3453_);
lean_dec_ref(v_mutex_3449_);
v___x_3454_ = lean_io_basemutex_lock(v_mutex_3453_);
v_r_3455_ = lean_apply_2(v_k_3450_, v_ref_3452_, lean_box(0));
if (lean_obj_tag(v_r_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3464_; 
v_a_3456_ = lean_ctor_get(v_r_3455_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_r_3455_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3458_ = v_r_3455_;
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v_r_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3460_ = lean_io_basemutex_unlock(v_mutex_3453_);
lean_dec(v_mutex_3453_);
if (v_isShared_3459_ == 0)
{
v___x_3462_ = v___x_3458_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3456_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3473_; 
v_a_3465_ = lean_ctor_get(v_r_3455_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_r_3455_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3467_ = v_r_3455_;
v_isShared_3468_ = v_isSharedCheck_3473_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v_r_3455_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3473_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3469_ = lean_io_basemutex_unlock(v_mutex_3453_);
lean_dec(v_mutex_3453_);
if (v_isShared_3468_ == 0)
{
v___x_3471_ = v___x_3467_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3465_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3474_, lean_object* v_k_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3474_, v_k_3475_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3478_, lean_object* v_00_u03b2_3479_, lean_object* v_mutex_3480_, lean_object* v_k_3481_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3480_, v_k_3481_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3484_, lean_object* v_00_u03b2_3485_, lean_object* v_mutex_3486_, lean_object* v_k_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3484_, v_00_u03b2_3485_, v_mutex_3486_, v_k_3487_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3490_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3493_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; lean_object* v_producers_3500_; lean_object* v_consumers_3501_; lean_object* v_capacity_3502_; lean_object* v_buf_3503_; lean_object* v_bufCount_3504_; lean_object* v_sendIdx_3505_; lean_object* v_recvIdx_3506_; uint8_t v_closed_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3530_; 
v___x_3499_ = lean_st_ref_get(v___y_3497_);
v_producers_3500_ = lean_ctor_get(v___x_3499_, 0);
v_consumers_3501_ = lean_ctor_get(v___x_3499_, 1);
v_capacity_3502_ = lean_ctor_get(v___x_3499_, 2);
v_buf_3503_ = lean_ctor_get(v___x_3499_, 3);
v_bufCount_3504_ = lean_ctor_get(v___x_3499_, 4);
v_sendIdx_3505_ = lean_ctor_get(v___x_3499_, 5);
v_recvIdx_3506_ = lean_ctor_get(v___x_3499_, 6);
v_closed_3507_ = lean_ctor_get_uint8(v___x_3499_, sizeof(void*)*7);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3509_ = v___x_3499_;
v_isShared_3510_ = v_isSharedCheck_3530_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_recvIdx_3506_);
lean_inc(v_sendIdx_3505_);
lean_inc(v_bufCount_3504_);
lean_inc(v_buf_3503_);
lean_inc(v_capacity_3502_);
lean_inc(v_consumers_3501_);
lean_inc(v_producers_3500_);
lean_dec(v___x_3499_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3530_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3501_);
if (lean_obj_tag(v___x_3511_) == 1)
{
lean_object* v_val_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3527_; 
v_val_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3527_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_val_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3527_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_fst_3516_; lean_object* v_snd_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
v_fst_3516_ = lean_ctor_get(v_val_3512_, 0);
lean_inc(v_fst_3516_);
v_snd_3517_ = lean_ctor_get(v_val_3512_, 1);
lean_inc(v_snd_3517_);
lean_dec(v_val_3512_);
v___x_3518_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3516_, v_____do__lift_3496_);
lean_dec(v_fst_3516_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 1, v_snd_3517_);
v___x_3520_ = v___x_3509_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_producers_3500_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_snd_3517_);
lean_ctor_set(v_reuseFailAlloc_3526_, 2, v_capacity_3502_);
lean_ctor_set(v_reuseFailAlloc_3526_, 3, v_buf_3503_);
lean_ctor_set(v_reuseFailAlloc_3526_, 4, v_bufCount_3504_);
lean_ctor_set(v_reuseFailAlloc_3526_, 5, v_sendIdx_3505_);
lean_ctor_set(v_reuseFailAlloc_3526_, 6, v_recvIdx_3506_);
lean_ctor_set_uint8(v_reuseFailAlloc_3526_, sizeof(void*)*7, v_closed_3507_);
v___x_3520_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v___x_3521_ = lean_box(0);
v___x_3522_ = lean_st_ref_swap(v___y_3497_, v___x_3520_);
lean_dec(v___x_3522_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set_tag(v___x_3514_, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3521_);
v___x_3524_ = v___x_3514_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3521_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
lean_dec(v___x_3511_);
lean_del_object(v___x_3509_);
lean_dec(v_recvIdx_3506_);
lean_dec(v_sendIdx_3505_);
lean_dec(v_bufCount_3504_);
lean_dec_ref(v_buf_3503_);
lean_dec(v_capacity_3502_);
lean_dec_ref(v_producers_3500_);
v___x_3528_ = lean_box(0);
v___x_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
return v___x_3529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
uint8_t v_____do__lift_3555__boxed_3534_; lean_object* v_res_3535_; 
v_____do__lift_3555__boxed_3534_ = lean_unbox(v_____do__lift_3531_);
v_res_3535_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3555__boxed_3534_, v___y_3532_);
lean_dec(v___y_3532_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3536_, lean_object* v___f_3537_, uint8_t v_____do__lift_3538_, lean_object* v___y_3539_){
_start:
{
if (v_____do__lift_3538_ == 0)
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v_producers_3543_; lean_object* v_consumers_3544_; lean_object* v_capacity_3545_; lean_object* v_buf_3546_; lean_object* v_bufCount_3547_; lean_object* v_sendIdx_3548_; lean_object* v_recvIdx_3549_; uint8_t v_closed_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3564_; 
v___x_3541_ = lean_io_promise_new();
v___x_3542_ = lean_st_ref_take(v___y_3539_);
v_producers_3543_ = lean_ctor_get(v___x_3542_, 0);
v_consumers_3544_ = lean_ctor_get(v___x_3542_, 1);
v_capacity_3545_ = lean_ctor_get(v___x_3542_, 2);
v_buf_3546_ = lean_ctor_get(v___x_3542_, 3);
v_bufCount_3547_ = lean_ctor_get(v___x_3542_, 4);
v_sendIdx_3548_ = lean_ctor_get(v___x_3542_, 5);
v_recvIdx_3549_ = lean_ctor_get(v___x_3542_, 6);
v_closed_3550_ = lean_ctor_get_uint8(v___x_3542_, sizeof(void*)*7);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3552_ = v___x_3542_;
v_isShared_3553_ = v_isSharedCheck_3564_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_recvIdx_3549_);
lean_inc(v_sendIdx_3548_);
lean_inc(v_bufCount_3547_);
lean_inc(v_buf_3546_);
lean_inc(v_capacity_3545_);
lean_inc(v_consumers_3544_);
lean_inc(v_producers_3543_);
lean_dec(v___x_3542_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3564_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3554_, 0, v_waiter_3536_);
lean_inc(v___x_3541_);
v___x_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3541_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = l_Std_Queue_enqueue___redArg(v___x_3555_, v_consumers_3544_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v___x_3556_);
v___x_3558_ = v___x_3552_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_producers_3543_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_capacity_3545_);
lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_buf_3546_);
lean_ctor_set(v_reuseFailAlloc_3563_, 4, v_bufCount_3547_);
lean_ctor_set(v_reuseFailAlloc_3563_, 5, v_sendIdx_3548_);
lean_ctor_set(v_reuseFailAlloc_3563_, 6, v_recvIdx_3549_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*7, v_closed_3550_);
v___x_3558_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3559_ = lean_st_ref_put(v___y_3539_, v___x_3558_);
v___x_3560_ = lean_io_promise_result_opt(v___x_3541_);
lean_dec(v___x_3541_);
v___x_3561_ = lean_unsigned_to_nat(0u);
v___x_3562_ = l_EIO_chainTask___redArg(v___x_3560_, v___f_3537_, v___x_3561_, v_____do__lift_3538_);
return v___x_3562_;
}
}
}
else
{
lean_object* v___x_3565_; lean_object* v_lose_3566_; lean_object* v___x_3567_; 
lean_dec_ref(v___f_3537_);
v___x_3565_ = lean_box(v_____do__lift_3538_);
v_lose_3566_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3566_, 0, v___x_3565_);
v___x_3567_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3536_, v_lose_3566_, v___y_3539_);
lean_dec_ref(v_waiter_3536_);
return v___x_3567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3568_, lean_object* v___f_3569_, lean_object* v_____do__lift_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
uint8_t v_____do__lift_3613__boxed_3573_; lean_object* v_res_3574_; 
v_____do__lift_3613__boxed_3573_ = lean_unbox(v_____do__lift_3570_);
v_res_3574_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3568_, v___f_3569_, v_____do__lift_3613__boxed_3573_, v___y_3571_);
lean_dec(v___y_3571_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v___x_3578_; lean_object* v_bufCount_3579_; uint8_t v_closed_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3578_ = lean_st_ref_get(v___y_3576_);
v_bufCount_3579_ = lean_ctor_get(v___x_3578_, 4);
lean_inc(v_bufCount_3579_);
v_closed_3580_ = lean_ctor_get_uint8(v___x_3578_, sizeof(void*)*7);
lean_dec(v___x_3578_);
v___x_3581_ = lean_unsigned_to_nat(0u);
v___x_3582_ = lean_nat_dec_eq(v_bufCount_3579_, v___x_3581_);
lean_dec(v_bufCount_3579_);
if (v___x_3582_ == 0)
{
uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = 1;
v___x_3584_ = lean_box(v___x_3583_);
lean_inc(v___y_3576_);
v___x_3585_ = lean_apply_3(v___f_3575_, v___x_3584_, v___y_3576_, lean_box(0));
return v___x_3585_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = lean_box(v_closed_3580_);
lean_inc(v___y_3576_);
v___x_3587_ = lean_apply_3(v___f_3575_, v___x_3586_, v___y_3576_, lean_box(0));
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3588_, v___y_3589_);
lean_dec(v___y_3589_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3594_, lean_object* v_ch_3595_, lean_object* v_x_3596_){
_start:
{
if (lean_obj_tag(v_x_3596_) == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_dec_ref(v_ch_3595_);
lean_dec_ref(v_waiter_3594_);
v___x_3598_ = lean_box(0);
v___x_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
return v___x_3599_;
}
else
{
lean_object* v_val_3600_; uint8_t v___x_3601_; 
v_val_3600_ = lean_ctor_get(v_x_3596_, 0);
v___x_3601_ = lean_unbox(v_val_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___f_3602_; lean_object* v___x_3603_; 
lean_dec_ref(v_ch_3595_);
v___f_3602_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3603_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3594_, v___f_3602_);
lean_dec_ref(v_waiter_3594_);
return v___x_3603_;
}
else
{
lean_object* v___x_3604_; 
v___x_3604_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3595_, v_waiter_3594_);
return v___x_3604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3605_, lean_object* v_ch_3606_, lean_object* v_x_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3605_, v_ch_3606_, v_x_3607_);
lean_dec(v_x_3607_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3610_, lean_object* v_waiter_3611_){
_start:
{
lean_object* v___f_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___x_3616_; 
lean_inc_ref(v_ch_3610_);
lean_inc_ref(v_waiter_3611_);
v___f_3613_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3613_, 0, v_waiter_3611_);
lean_closure_set(v___f_3613_, 1, v_ch_3610_);
v___f_3614_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3614_, 0, v_waiter_3611_);
lean_closure_set(v___f_3614_, 1, v___f_3613_);
v___f_3615_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3615_, 0, v___f_3614_);
v___x_3616_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3610_, v___f_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3617_, lean_object* v_waiter_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3617_, v_waiter_3618_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3621_, lean_object* v_ch_3622_, lean_object* v_waiter_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3622_, v_waiter_3623_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3626_, lean_object* v_ch_3627_, lean_object* v_waiter_3628_, lean_object* v_a_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3626_, v_ch_3627_, v_waiter_3628_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3631_, lean_object* v_x_3632_){
_start:
{
if (lean_obj_tag(v_x_3632_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v_x_3631_);
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
lean_object* v___x_3643_; 
lean_dec_ref_known(v_x_3632_, 1);
v___x_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3643_, 0, v_x_3631_);
return v___x_3643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3644_, lean_object* v_x_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3644_, v_x_3645_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3648_, uint8_t v___x_3649_, lean_object* v___f_3650_, lean_object* v_____r_3651_, lean_object* v_st_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_st_ref_swap(v___y_3653_, v_st_3652_);
lean_dec(v___x_3655_);
v___x_3656_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_3657_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3648_, v___x_3649_, v___x_3656_, v___f_3650_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3658_, lean_object* v___x_3659_, lean_object* v___f_3660_, lean_object* v_____r_3661_, lean_object* v_st_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
uint8_t v___x_6366__boxed_3665_; lean_object* v_res_3666_; 
v___x_6366__boxed_3665_ = lean_unbox(v___x_3659_);
v_res_3666_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3658_, v___x_6366__boxed_3665_, v___f_3660_, v_____r_3661_, v_st_3662_, v___y_3663_);
lean_dec(v___y_3663_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3667_, lean_object* v_consumers_3668_, lean_object* v_capacity_3669_, lean_object* v_buf_3670_, lean_object* v___x_3671_, lean_object* v_sendIdx_3672_, lean_object* v___y_3673_, uint8_t v_closed_3674_, lean_object* v___f_3675_, lean_object* v_a_3676_, lean_object* v_x_3677_){
_start:
{
if (lean_obj_tag(v_x_3677_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3687_; 
lean_dec_ref(v___f_3675_);
lean_dec(v___y_3673_);
lean_dec(v_sendIdx_3672_);
lean_dec(v___x_3671_);
lean_dec_ref(v_buf_3670_);
lean_dec(v_capacity_3669_);
lean_dec_ref(v_consumers_3668_);
lean_dec_ref(v_snd_3667_);
v_a_3679_ = lean_ctor_get(v_x_3677_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_x_3677_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3681_ = v_x_3677_;
v_isShared_3682_ = v_isSharedCheck_3687_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v_x_3677_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3687_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; 
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
return v___x_3685_;
}
}
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_dec_ref_known(v_x_3677_, 1);
v___x_3688_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3688_, 0, v_snd_3667_);
lean_ctor_set(v___x_3688_, 1, v_consumers_3668_);
lean_ctor_set(v___x_3688_, 2, v_capacity_3669_);
lean_ctor_set(v___x_3688_, 3, v_buf_3670_);
lean_ctor_set(v___x_3688_, 4, v___x_3671_);
lean_ctor_set(v___x_3688_, 5, v_sendIdx_3672_);
lean_ctor_set(v___x_3688_, 6, v___y_3673_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*7, v_closed_3674_);
v___x_3689_ = lean_box(0);
lean_inc(v_a_3676_);
v___x_3690_ = lean_apply_4(v___f_3675_, v___x_3689_, v___x_3688_, v_a_3676_, lean_box(0));
return v___x_3690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3691_, lean_object* v_consumers_3692_, lean_object* v_capacity_3693_, lean_object* v_buf_3694_, lean_object* v___x_3695_, lean_object* v_sendIdx_3696_, lean_object* v___y_3697_, lean_object* v_closed_3698_, lean_object* v___f_3699_, lean_object* v_a_3700_, lean_object* v_x_3701_, lean_object* v___y_3702_){
_start:
{
uint8_t v_closed_boxed_3703_; lean_object* v_res_3704_; 
v_closed_boxed_3703_ = lean_unbox(v_closed_3698_);
v_res_3704_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3691_, v_consumers_3692_, v_capacity_3693_, v_buf_3694_, v___x_3695_, v_sendIdx_3696_, v___y_3697_, v_closed_boxed_3703_, v___f_3699_, v_a_3700_, v_x_3701_);
lean_dec(v_a_3700_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3705_, uint8_t v___x_3706_, lean_object* v_bufCount_3707_, lean_object* v_producers_3708_, lean_object* v_consumers_3709_, lean_object* v_capacity_3710_, lean_object* v_buf_3711_, lean_object* v_sendIdx_3712_, uint8_t v_closed_3713_, lean_object* v_a_3714_, uint8_t v___x_3715_, lean_object* v_recvIdx_3716_, lean_object* v_x_3717_){
_start:
{
if (lean_obj_tag(v_x_3717_) == 0)
{
lean_object* v___x_3719_; 
lean_dec(v_sendIdx_3712_);
lean_dec_ref(v_buf_3711_);
lean_dec(v_capacity_3710_);
lean_dec_ref(v_consumers_3709_);
lean_dec_ref(v_producers_3708_);
lean_dec(v___x_3705_);
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v_x_3717_);
return v___x_3719_;
}
else
{
lean_object* v___f_3720_; lean_object* v___x_3721_; lean_object* v___f_3722_; lean_object* v___y_3724_; lean_object* v___x_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; 
v___f_3720_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3720_, 0, v_x_3717_);
v___x_3721_ = lean_box(v___x_3706_);
lean_inc_ref(v___f_3720_);
lean_inc(v___x_3705_);
v___f_3722_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3722_, 0, v___x_3705_);
lean_closure_set(v___f_3722_, 1, v___x_3721_);
lean_closure_set(v___f_3722_, 2, v___f_3720_);
v___x_3747_ = lean_unsigned_to_nat(1u);
v___x_3748_ = lean_nat_add(v_recvIdx_3716_, v___x_3747_);
v___x_3749_ = lean_nat_dec_eq(v___x_3748_, v_capacity_3710_);
if (v___x_3749_ == 0)
{
v___y_3724_ = v___x_3748_;
goto v___jp_3723_;
}
else
{
lean_dec(v___x_3748_);
lean_inc(v___x_3705_);
v___y_3724_ = v___x_3705_;
goto v___jp_3723_;
}
v___jp_3723_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3725_ = lean_unsigned_to_nat(1u);
v___x_3726_ = lean_nat_sub(v_bufCount_3707_, v___x_3725_);
lean_inc(v___y_3724_);
lean_inc(v_sendIdx_3712_);
lean_inc(v___x_3726_);
lean_inc_ref(v_buf_3711_);
lean_inc(v_capacity_3710_);
lean_inc_ref(v_consumers_3709_);
lean_inc_ref(v_producers_3708_);
v___x_3727_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3727_, 0, v_producers_3708_);
lean_ctor_set(v___x_3727_, 1, v_consumers_3709_);
lean_ctor_set(v___x_3727_, 2, v_capacity_3710_);
lean_ctor_set(v___x_3727_, 3, v_buf_3711_);
lean_ctor_set(v___x_3727_, 4, v___x_3726_);
lean_ctor_set(v___x_3727_, 5, v_sendIdx_3712_);
lean_ctor_set(v___x_3727_, 6, v___y_3724_);
lean_ctor_set_uint8(v___x_3727_, sizeof(void*)*7, v_closed_3713_);
v___x_3728_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3708_);
if (lean_obj_tag(v___x_3728_) == 1)
{
lean_object* v_val_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3744_; 
lean_dec_ref_known(v___x_3727_, 7);
lean_dec_ref(v___f_3720_);
v_val_3729_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3731_ = v___x_3728_;
v_isShared_3732_ = v_isSharedCheck_3744_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_val_3729_);
lean_dec(v___x_3728_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3744_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v_fst_3733_; lean_object* v_snd_3734_; lean_object* v___x_3735_; lean_object* v___f_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
v_fst_3733_ = lean_ctor_get(v_val_3729_, 0);
lean_inc(v_fst_3733_);
v_snd_3734_ = lean_ctor_get(v_val_3729_, 1);
lean_inc(v_snd_3734_);
lean_dec(v_val_3729_);
v___x_3735_ = lean_box(v_closed_3713_);
lean_inc(v_a_3714_);
v___f_3736_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3736_, 0, v_snd_3734_);
lean_closure_set(v___f_3736_, 1, v_consumers_3709_);
lean_closure_set(v___f_3736_, 2, v_capacity_3710_);
lean_closure_set(v___f_3736_, 3, v_buf_3711_);
lean_closure_set(v___f_3736_, 4, v___x_3726_);
lean_closure_set(v___f_3736_, 5, v_sendIdx_3712_);
lean_closure_set(v___f_3736_, 6, v___y_3724_);
lean_closure_set(v___f_3736_, 7, v___x_3735_);
lean_closure_set(v___f_3736_, 8, v___f_3722_);
lean_closure_set(v___f_3736_, 9, v_a_3714_);
v___x_3737_ = lean_box(v___x_3715_);
v___x_3738_ = lean_io_promise_resolve(v___x_3737_, v_fst_3733_);
lean_dec(v_fst_3733_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 0, v___x_3738_);
v___x_3740_ = v___x_3731_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
v___x_3742_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3705_, v___x_3706_, v___x_3741_, v___f_3736_);
return v___x_3742_;
}
}
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec(v___x_3728_);
lean_dec(v___x_3726_);
lean_dec(v___y_3724_);
lean_dec_ref(v___f_3722_);
lean_dec(v_sendIdx_3712_);
lean_dec_ref(v_buf_3711_);
lean_dec(v_capacity_3710_);
lean_dec_ref(v_consumers_3709_);
v___x_3745_ = lean_box(0);
v___x_3746_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3705_, v___x_3706_, v___f_3720_, v___x_3745_, v___x_3727_, v_a_3714_);
return v___x_3746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3750_, lean_object* v___x_3751_, lean_object* v_bufCount_3752_, lean_object* v_producers_3753_, lean_object* v_consumers_3754_, lean_object* v_capacity_3755_, lean_object* v_buf_3756_, lean_object* v_sendIdx_3757_, lean_object* v_closed_3758_, lean_object* v_a_3759_, lean_object* v___x_3760_, lean_object* v_recvIdx_3761_, lean_object* v_x_3762_, lean_object* v___y_3763_){
_start:
{
uint8_t v___x_6435__boxed_3764_; uint8_t v_closed_boxed_3765_; uint8_t v___x_6436__boxed_3766_; lean_object* v_res_3767_; 
v___x_6435__boxed_3764_ = lean_unbox(v___x_3751_);
v_closed_boxed_3765_ = lean_unbox(v_closed_3758_);
v___x_6436__boxed_3766_ = lean_unbox(v___x_3760_);
v_res_3767_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3750_, v___x_6435__boxed_3764_, v_bufCount_3752_, v_producers_3753_, v_consumers_3754_, v_capacity_3755_, v_buf_3756_, v_sendIdx_3757_, v_closed_boxed_3765_, v_a_3759_, v___x_6436__boxed_3766_, v_recvIdx_3761_, v_x_3762_);
lean_dec(v_recvIdx_3761_);
lean_dec(v_a_3759_);
lean_dec(v_bufCount_3752_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3768_, lean_object* v_x_3769_){
_start:
{
if (lean_obj_tag(v_x_3769_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3779_; 
v_a_3771_ = lean_ctor_get(v_x_3769_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_x_3769_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3773_ = v_x_3769_;
v_isShared_3774_ = v_isSharedCheck_3779_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v_x_3769_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3779_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3777_; 
v___x_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
return v___x_3777_;
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3808_; 
v_a_3780_ = lean_ctor_get(v_x_3769_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_x_3769_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3782_ = v_x_3769_;
v_isShared_3783_ = v_isSharedCheck_3808_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v_x_3769_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3808_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v_producers_3784_; lean_object* v_consumers_3785_; lean_object* v_capacity_3786_; lean_object* v_buf_3787_; lean_object* v_bufCount_3788_; lean_object* v_sendIdx_3789_; lean_object* v_recvIdx_3790_; uint8_t v_closed_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v_producers_3784_ = lean_ctor_get(v_a_3780_, 0);
lean_inc_ref(v_producers_3784_);
v_consumers_3785_ = lean_ctor_get(v_a_3780_, 1);
lean_inc_ref(v_consumers_3785_);
v_capacity_3786_ = lean_ctor_get(v_a_3780_, 2);
lean_inc(v_capacity_3786_);
v_buf_3787_ = lean_ctor_get(v_a_3780_, 3);
lean_inc_ref(v_buf_3787_);
v_bufCount_3788_ = lean_ctor_get(v_a_3780_, 4);
lean_inc(v_bufCount_3788_);
v_sendIdx_3789_ = lean_ctor_get(v_a_3780_, 5);
lean_inc(v_sendIdx_3789_);
v_recvIdx_3790_ = lean_ctor_get(v_a_3780_, 6);
lean_inc(v_recvIdx_3790_);
v_closed_3791_ = lean_ctor_get_uint8(v_a_3780_, sizeof(void*)*7);
lean_dec(v_a_3780_);
v___x_3792_ = lean_unsigned_to_nat(0u);
v___x_3793_ = lean_nat_dec_eq(v_bufCount_3788_, v___x_3792_);
if (v___x_3793_ == 0)
{
uint8_t v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___f_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3803_; 
v___x_3794_ = 1;
v___x_3795_ = lean_box(v___x_3793_);
v___x_3796_ = lean_box(v_closed_3791_);
v___x_3797_ = lean_box(v___x_3794_);
lean_inc(v_recvIdx_3790_);
lean_inc(v_a_3768_);
lean_inc_ref(v_buf_3787_);
v___f_3798_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_3798_, 0, v___x_3792_);
lean_closure_set(v___f_3798_, 1, v___x_3795_);
lean_closure_set(v___f_3798_, 2, v_bufCount_3788_);
lean_closure_set(v___f_3798_, 3, v_producers_3784_);
lean_closure_set(v___f_3798_, 4, v_consumers_3785_);
lean_closure_set(v___f_3798_, 5, v_capacity_3786_);
lean_closure_set(v___f_3798_, 6, v_buf_3787_);
lean_closure_set(v___f_3798_, 7, v_sendIdx_3789_);
lean_closure_set(v___f_3798_, 8, v___x_3796_);
lean_closure_set(v___f_3798_, 9, v_a_3768_);
lean_closure_set(v___f_3798_, 10, v___x_3797_);
lean_closure_set(v___f_3798_, 11, v_recvIdx_3790_);
v___x_3799_ = lean_array_fget(v_buf_3787_, v_recvIdx_3790_);
lean_dec(v_recvIdx_3790_);
lean_dec_ref(v_buf_3787_);
v___x_3800_ = lean_box(0);
v___x_3801_ = lean_st_ref_swap(v___x_3799_, v___x_3800_);
lean_dec(v___x_3799_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v___x_3801_);
v___x_3803_ = v___x_3782_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3801_);
v___x_3803_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
v___x_3805_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3792_, v___x_3793_, v___x_3804_, v___f_3798_);
return v___x_3805_;
}
}
else
{
lean_object* v___x_3807_; 
lean_dec(v_recvIdx_3790_);
lean_dec(v_sendIdx_3789_);
lean_dec(v_bufCount_3788_);
lean_dec_ref(v_buf_3787_);
lean_dec(v_capacity_3786_);
lean_dec_ref(v_consumers_3785_);
lean_dec_ref(v_producers_3784_);
lean_del_object(v___x_3782_);
v___x_3807_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_3807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_3809_, lean_object* v_x_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3809_, v_x_3810_);
lean_dec(v_a_3809_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_3813_){
_start:
{
lean_object* v___f_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
lean_inc(v_a_3813_);
v___f_3815_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3815_, 0, v_a_3813_);
v___x_3816_ = lean_unsigned_to_nat(0u);
v___x_3817_ = 0;
v___x_3818_ = lean_st_ref_get(v_a_3813_);
v___x_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
v___x_3821_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3816_, v___x_3817_, v___x_3820_, v___f_3815_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3822_);
lean_dec(v_a_3822_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_3825_, lean_object* v_a_3826_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3826_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_3829_, lean_object* v_a_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_3829_, v_a_3830_);
lean_dec(v_a_3830_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_3833_, lean_object* v_x_3834_){
_start:
{
lean_object* v_val_3837_; lean_object* v___x_3839_; 
v___x_3839_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3833_, v_x_3834_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
lean_ctor_set_tag(v___x_3842_, 1);
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
v_val_3837_ = v___x_3845_;
goto v___jp_3836_;
}
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
v_a_3848_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3839_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3839_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
lean_ctor_set_tag(v___x_3850_, 0);
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
v_val_3837_ = v___x_3853_;
goto v___jp_3836_;
}
}
}
v___jp_3836_:
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v_val_3837_);
return v___x_3838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_3856_, lean_object* v_x_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_3856_, v_x_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v___y_3860_, lean_object* v___f_3861_, lean_object* v_x_3862_){
_start:
{
if (lean_obj_tag(v_x_3862_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3872_; 
lean_dec_ref(v___f_3861_);
v_a_3864_ = lean_ctor_get(v_x_3862_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_x_3862_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3866_ = v_x_3862_;
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v_x_3862_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; 
v___x_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
return v___x_3870_;
}
}
}
else
{
lean_object* v_a_3873_; uint8_t v___x_3874_; 
v_a_3873_ = lean_ctor_get(v_x_3862_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v_x_3862_, 1);
v___x_3874_ = lean_unbox(v_a_3873_);
lean_dec(v_a_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
lean_dec_ref(v___f_3861_);
v___x_3875_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_3875_;
}
else
{
lean_object* v___x_3876_; uint8_t v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3876_ = lean_unsigned_to_nat(0u);
v___x_3877_ = 0;
v___x_3878_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_3860_);
v___x_3879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3876_, v___x_3877_, v___x_3878_, v___f_3861_);
return v___x_3879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v___y_3880_, lean_object* v___f_3881_, lean_object* v_x_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v___y_3880_, v___f_3881_, v_x_3882_);
lean_dec(v___y_3880_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___x_3885_, lean_object* v_x_3886_){
_start:
{
uint8_t v___y_3889_; 
if (lean_obj_tag(v_x_3886_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3901_; 
v_a_3893_ = lean_ctor_get(v_x_3886_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_x_3886_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3895_ = v_x_3886_;
v_isShared_3896_ = v_isSharedCheck_3901_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v_x_3886_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3901_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v_bufCount_3903_; uint8_t v_closed_3904_; uint8_t v___x_3905_; 
v_a_3902_ = lean_ctor_get(v_x_3886_, 0);
lean_inc(v_a_3902_);
lean_dec_ref_known(v_x_3886_, 1);
v_bufCount_3903_ = lean_ctor_get(v_a_3902_, 4);
lean_inc(v_bufCount_3903_);
v_closed_3904_ = lean_ctor_get_uint8(v_a_3902_, sizeof(void*)*7);
lean_dec(v_a_3902_);
v___x_3905_ = lean_nat_dec_eq(v_bufCount_3903_, v___x_3885_);
lean_dec(v_bufCount_3903_);
if (v___x_3905_ == 0)
{
uint8_t v___x_3906_; 
v___x_3906_ = 1;
v___y_3889_ = v___x_3906_;
goto v___jp_3888_;
}
else
{
v___y_3889_ = v_closed_3904_;
goto v___jp_3888_;
}
}
v___jp_3888_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3890_ = lean_box(v___y_3889_);
v___x_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
v___x_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
return v___x_3892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_3907_, lean_object* v_x_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___x_3907_, v_x_3908_);
lean_dec(v___x_3907_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v___f_3916_; lean_object* v___x_3917_; lean_object* v___f_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
lean_inc(v___y_3914_);
v___f_3916_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3916_, 0, v___y_3914_);
lean_closure_set(v___f_3916_, 1, v___f_3913_);
v___x_3917_ = lean_unsigned_to_nat(0u);
v___f_3918_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___closed__0));
v___x_3919_ = 0;
v___x_3920_ = lean_st_ref_get(v___y_3914_);
v___x_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
v___x_3923_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3917_, v___x_3919_, v___x_3922_, v___f_3918_);
v___x_3924_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3917_, v___x_3919_, v___x_3923_, v___f_3916_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_3925_, v___y_3926_);
lean_dec(v___y_3926_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_3929_, lean_object* v_capacity_3930_, lean_object* v_buf_3931_, lean_object* v_bufCount_3932_, lean_object* v_sendIdx_3933_, lean_object* v_recvIdx_3934_, uint8_t v_closed_3935_, lean_object* v___y_3936_, lean_object* v_x_3937_){
_start:
{
if (lean_obj_tag(v_x_3937_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3947_; 
lean_dec(v_recvIdx_3934_);
lean_dec(v_sendIdx_3933_);
lean_dec(v_bufCount_3932_);
lean_dec_ref(v_buf_3931_);
lean_dec(v_capacity_3930_);
lean_dec_ref(v_producers_3929_);
v_a_3939_ = lean_ctor_get(v_x_3937_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_x_3937_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3941_ = v_x_3937_;
v_isShared_3942_ = v_isSharedCheck_3947_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v_x_3937_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3947_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
return v___x_3945_;
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_a_3948_ = lean_ctor_get(v_x_3937_, 0);
lean_inc(v_a_3948_);
lean_dec_ref_known(v_x_3937_, 1);
v___x_3949_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3949_, 0, v_producers_3929_);
lean_ctor_set(v___x_3949_, 1, v_a_3948_);
lean_ctor_set(v___x_3949_, 2, v_capacity_3930_);
lean_ctor_set(v___x_3949_, 3, v_buf_3931_);
lean_ctor_set(v___x_3949_, 4, v_bufCount_3932_);
lean_ctor_set(v___x_3949_, 5, v_sendIdx_3933_);
lean_ctor_set(v___x_3949_, 6, v_recvIdx_3934_);
lean_ctor_set_uint8(v___x_3949_, sizeof(void*)*7, v_closed_3935_);
v___x_3950_ = lean_st_ref_swap(v___y_3936_, v___x_3949_);
lean_dec(v___x_3950_);
v___x_3951_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_3951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_3952_, lean_object* v_capacity_3953_, lean_object* v_buf_3954_, lean_object* v_bufCount_3955_, lean_object* v_sendIdx_3956_, lean_object* v_recvIdx_3957_, lean_object* v_closed_3958_, lean_object* v___y_3959_, lean_object* v_x_3960_, lean_object* v___y_3961_){
_start:
{
uint8_t v_closed_boxed_3962_; lean_object* v_res_3963_; 
v_closed_boxed_3962_ = lean_unbox(v_closed_3958_);
v_res_3963_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_3952_, v_capacity_3953_, v_buf_3954_, v_bufCount_3955_, v_sendIdx_3956_, v_recvIdx_3957_, v_closed_boxed_3962_, v___y_3959_, v_x_3960_);
lean_dec(v___y_3959_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_3964_, lean_object* v_x_3965_, lean_object* v_head_3966_, lean_object* v_x_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_3964_, v_x_3965_, v_head_3966_, v_x_3967_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_3970_, lean_object* v_x_3971_){
_start:
{
if (lean_obj_tag(v_x_3970_) == 0)
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3973_, 0, v_x_3971_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
else
{
lean_object* v_head_3975_; lean_object* v_tail_3976_; lean_object* v_waiter_3977_; lean_object* v___f_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; 
v_head_3975_ = lean_ctor_get(v_x_3970_, 0);
lean_inc(v_head_3975_);
v_tail_3976_ = lean_ctor_get(v_x_3970_, 1);
lean_inc(v_tail_3976_);
lean_dec_ref_known(v_x_3970_, 2);
v_waiter_3977_ = lean_ctor_get(v_head_3975_, 1);
lean_inc(v_waiter_3977_);
v___f_3978_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3978_, 0, v_tail_3976_);
lean_closure_set(v___f_3978_, 1, v_x_3971_);
lean_closure_set(v___f_3978_, 2, v_head_3975_);
v___x_3979_ = lean_unsigned_to_nat(0u);
v___x_3980_ = 0;
if (lean_obj_tag(v_waiter_3977_) == 0)
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3981_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_3982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3979_, v___x_3980_, v___x_3981_, v___f_3978_);
return v___x_3982_;
}
else
{
lean_object* v_val_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3996_; 
v_val_3983_ = lean_ctor_get(v_waiter_3977_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_waiter_3977_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3985_ = v_waiter_3977_;
v_isShared_3986_ = v_isSharedCheck_3996_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_val_3983_);
lean_dec(v_waiter_3977_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3996_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v_finished_3987_; lean_object* v___f_3988_; lean_object* v___x_3989_; lean_object* v___x_3991_; 
v_finished_3987_ = lean_ctor_get(v_val_3983_, 0);
lean_inc(v_finished_3987_);
lean_dec(v_val_3983_);
v___f_3988_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_3989_ = lean_st_ref_get(v_finished_3987_);
lean_dec(v_finished_3987_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v___x_3989_);
v___x_3991_ = v___x_3985_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
v___x_3993_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3979_, v___x_3980_, v___x_3992_, v___f_3988_);
v___x_3994_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3979_, v___x_3980_, v___x_3993_, v___f_3978_);
return v___x_3994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_3997_, lean_object* v_x_3998_, lean_object* v_head_3999_, lean_object* v_x_4000_){
_start:
{
if (lean_obj_tag(v_x_4000_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v_head_3999_);
lean_dec(v_x_3998_);
lean_dec(v_tail_3997_);
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
lean_object* v_a_4011_; uint8_t v___x_4012_; 
v_a_4011_ = lean_ctor_get(v_x_4000_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v_x_4000_, 1);
v___x_4012_ = lean_unbox(v_a_4011_);
lean_dec(v_a_4011_);
if (v___x_4012_ == 0)
{
lean_object* v___x_4013_; 
lean_dec_ref(v_head_3999_);
v___x_4013_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_3997_, v_x_3998_);
return v___x_4013_;
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4014_, 0, v_head_3999_);
lean_ctor_set(v___x_4014_, 1, v_x_3998_);
v___x_4015_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_3997_, v___x_4014_);
return v___x_4015_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_4016_, lean_object* v_x_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4016_, v_x_4017_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_4020_){
_start:
{
if (lean_obj_tag(v_x_4020_) == 0)
{
lean_object* v___x_4022_; 
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v_x_4020_);
return v___x_4022_;
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4032_; 
v_a_4023_ = lean_ctor_get(v_x_4020_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v_x_4020_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4025_ = v_x_4020_;
v_isShared_4026_ = v_isSharedCheck_4032_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v_x_4020_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4032_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; lean_object* v___x_4029_; 
v___x_4027_ = l_List_reverse___redArg(v_a_4023_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4027_);
v___x_4029_ = v___x_4025_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4027_);
v___x_4029_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; 
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
return v___x_4030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4033_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4036_, lean_object* v___x_4037_, lean_object* v_x_4038_){
_start:
{
if (lean_obj_tag(v_x_4038_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4048_; 
lean_dec(v___x_4037_);
lean_dec(v_a_4036_);
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
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4065_; 
v_a_4049_ = lean_ctor_get(v_x_4038_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_x_4038_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4051_ = v_x_4038_;
v_isShared_4052_ = v_isSharedCheck_4065_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v_x_4038_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4065_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
uint8_t v___x_4053_; 
v___x_4053_ = l_List_isEmpty___redArg(v_a_4036_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; lean_object* v___x_4056_; 
lean_dec(v___x_4037_);
v___x_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4054_, 0, v_a_4049_);
lean_ctor_set(v___x_4054_, 1, v_a_4036_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v___x_4054_);
v___x_4056_ = v___x_4051_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4054_);
v___x_4056_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4057_; 
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
return v___x_4057_;
}
}
else
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4062_; 
lean_dec(v_a_4036_);
v___x_4059_ = l_List_reverse___redArg(v_a_4049_);
v___x_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4037_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v___x_4060_);
v___x_4062_ = v___x_4051_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4060_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4066_, lean_object* v___x_4067_, lean_object* v_x_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4066_, v___x_4067_, v_x_4068_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v___x_4071_, lean_object* v_eList_4072_, lean_object* v___f_4073_, lean_object* v_x_4074_){
_start:
{
if (lean_obj_tag(v_x_4074_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4084_; 
lean_dec_ref(v___f_4073_);
lean_dec(v_eList_4072_);
lean_dec(v___x_4071_);
v_a_4076_ = lean_ctor_get(v_x_4074_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v_x_4074_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4078_ = v_x_4074_;
v_isShared_4079_ = v_isSharedCheck_4084_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v_x_4074_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4084_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
lean_object* v___x_4082_; 
v___x_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
return v___x_4082_;
}
}
}
else
{
lean_object* v_a_4085_; lean_object* v___f_4086_; lean_object* v___x_4087_; uint8_t v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v_a_4085_ = lean_ctor_get(v_x_4074_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v_x_4074_, 1);
lean_inc(v___x_4071_);
v___f_4086_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4086_, 0, v_a_4085_);
lean_closure_set(v___f_4086_, 1, v___x_4071_);
v___x_4087_ = lean_unsigned_to_nat(0u);
v___x_4088_ = 0;
v___x_4089_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4072_, v___x_4071_);
v___x_4090_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4087_, v___x_4088_, v___x_4089_, v___f_4073_);
v___x_4091_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4087_, v___x_4088_, v___x_4090_, v___f_4086_);
return v___x_4091_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v___x_4092_, lean_object* v_eList_4093_, lean_object* v___f_4094_, lean_object* v_x_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v___x_4092_, v_eList_4093_, v___f_4094_, v_x_4095_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v_eList_4102_; lean_object* v_dList_4103_; lean_object* v___f_4104_; lean_object* v___x_4105_; lean_object* v___f_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v_eList_4102_ = lean_ctor_get(v_q_4099_, 0);
lean_inc(v_eList_4102_);
v_dList_4103_ = lean_ctor_get(v_q_4099_, 1);
lean_inc(v_dList_4103_);
lean_dec_ref(v_q_4099_);
v___f_4104_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4105_ = lean_box(0);
v___f_4106_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4106_, 0, v___x_4105_);
lean_closure_set(v___f_4106_, 1, v_eList_4102_);
lean_closure_set(v___f_4106_, 2, v___f_4104_);
v___x_4107_ = lean_unsigned_to_nat(0u);
v___x_4108_ = 0;
v___x_4109_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4103_, v___x_4105_);
v___x_4110_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4107_, v___x_4108_, v___x_4109_, v___f_4104_);
v___x_4111_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4107_, v___x_4108_, v___x_4110_, v___f_4106_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4112_, v___y_4113_);
lean_dec(v___y_4113_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4116_, lean_object* v_x_4117_){
_start:
{
if (lean_obj_tag(v_x_4117_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4127_; 
v_a_4119_ = lean_ctor_get(v_x_4117_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_x_4117_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4121_ = v_x_4117_;
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v_x_4117_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
return v___x_4125_;
}
}
}
else
{
lean_object* v_a_4128_; lean_object* v_producers_4129_; lean_object* v_consumers_4130_; lean_object* v_capacity_4131_; lean_object* v_buf_4132_; lean_object* v_bufCount_4133_; lean_object* v_sendIdx_4134_; lean_object* v_recvIdx_4135_; uint8_t v_closed_4136_; lean_object* v___x_4137_; lean_object* v___f_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v_a_4128_ = lean_ctor_get(v_x_4117_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v_x_4117_, 1);
v_producers_4129_ = lean_ctor_get(v_a_4128_, 0);
lean_inc_ref(v_producers_4129_);
v_consumers_4130_ = lean_ctor_get(v_a_4128_, 1);
lean_inc_ref(v_consumers_4130_);
v_capacity_4131_ = lean_ctor_get(v_a_4128_, 2);
lean_inc(v_capacity_4131_);
v_buf_4132_ = lean_ctor_get(v_a_4128_, 3);
lean_inc_ref(v_buf_4132_);
v_bufCount_4133_ = lean_ctor_get(v_a_4128_, 4);
lean_inc(v_bufCount_4133_);
v_sendIdx_4134_ = lean_ctor_get(v_a_4128_, 5);
lean_inc(v_sendIdx_4134_);
v_recvIdx_4135_ = lean_ctor_get(v_a_4128_, 6);
lean_inc(v_recvIdx_4135_);
v_closed_4136_ = lean_ctor_get_uint8(v_a_4128_, sizeof(void*)*7);
lean_dec(v_a_4128_);
v___x_4137_ = lean_box(v_closed_4136_);
lean_inc(v___y_4116_);
v___f_4138_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4138_, 0, v_producers_4129_);
lean_closure_set(v___f_4138_, 1, v_capacity_4131_);
lean_closure_set(v___f_4138_, 2, v_buf_4132_);
lean_closure_set(v___f_4138_, 3, v_bufCount_4133_);
lean_closure_set(v___f_4138_, 4, v_sendIdx_4134_);
lean_closure_set(v___f_4138_, 5, v_recvIdx_4135_);
lean_closure_set(v___f_4138_, 6, v___x_4137_);
lean_closure_set(v___f_4138_, 7, v___y_4116_);
v___x_4139_ = lean_unsigned_to_nat(0u);
v___x_4140_ = 0;
v___x_4141_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4130_, v___y_4116_);
v___x_4142_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4139_, v___x_4140_, v___x_4141_, v___f_4138_);
return v___x_4142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4143_, lean_object* v_x_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4143_, v_x_4144_);
lean_dec(v___y_4143_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4147_){
_start:
{
lean_object* v___f_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_inc(v___y_4147_);
v___f_4149_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4149_, 0, v___y_4147_);
v___x_4150_ = lean_unsigned_to_nat(0u);
v___x_4151_ = 0;
v___x_4152_ = lean_st_ref_get(v___y_4147_);
v___x_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
v___x_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
v___x_4155_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4150_, v___x_4151_, v___x_4154_, v___f_4149_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4156_);
lean_dec(v___y_4156_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4162_){
_start:
{
lean_object* v___f_4163_; lean_object* v___f_4164_; lean_object* v___f_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_inc_ref_n(v_ch_4162_, 2);
v___f_4163_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4163_, 0, v_ch_4162_);
v___f_4164_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0));
v___f_4165_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___x_4166_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4166_, 0, lean_box(0));
lean_closure_set(v___x_4166_, 1, lean_box(0));
lean_closure_set(v___x_4166_, 2, v_ch_4162_);
lean_closure_set(v___x_4166_, 3, v___f_4164_);
v___x_4167_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4167_, 0, lean_box(0));
lean_closure_set(v___x_4167_, 1, lean_box(0));
lean_closure_set(v___x_4167_, 2, v_ch_4162_);
lean_closure_set(v___x_4167_, 3, v___f_4165_);
v___x_4168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set(v___x_4168_, 1, v___f_4163_);
lean_ctor_set(v___x_4168_, 2, v___x_4167_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4169_, lean_object* v_ch_4170_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4172_, lean_object* v_q_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v___x_4176_; 
v___x_4176_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4173_, v___y_4174_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4177_, lean_object* v_q_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4177_, v_q_4178_, v___y_4179_);
lean_dec(v___y_4179_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4182_, lean_object* v_x_4183_, lean_object* v_x_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4183_, v_x_4184_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4188_, lean_object* v_x_4189_, lean_object* v_x_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4188_, v_x_4189_, v_x_4190_, v___y_4191_);
lean_dec(v___y_4191_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg(lean_object* v_x_4194_){
_start:
{
switch(lean_obj_tag(v_x_4194_))
{
case 0:
{
lean_object* v___x_4195_; 
v___x_4195_ = lean_unsigned_to_nat(0u);
return v___x_4195_;
}
case 1:
{
lean_object* v___x_4196_; 
v___x_4196_ = lean_unsigned_to_nat(1u);
return v___x_4196_;
}
default: 
{
lean_object* v___x_4197_; 
v___x_4197_ = lean_unsigned_to_nat(2u);
return v___x_4197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(lean_object* v_x_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4198_);
lean_dec_ref(v_x_4198_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx(lean_object* v_00_u03b1_4200_, lean_object* v_x_4201_){
_start:
{
lean_object* v___x_4202_; 
v___x_4202_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___boxed(lean_object* v_00_u03b1_4203_, lean_object* v_x_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Std_CloseableChannel_Flavors_ctorIdx(v_00_u03b1_4203_, v_x_4204_);
lean_dec_ref(v_x_4204_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4206_, lean_object* v_k_4207_){
_start:
{
lean_object* v_ch_4208_; lean_object* v___x_4209_; 
v_ch_4208_ = lean_ctor_get(v_t_4206_, 0);
lean_inc_ref(v_ch_4208_);
lean_dec_ref(v_t_4206_);
v___x_4209_ = lean_apply_1(v_k_4207_, v_ch_4208_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4210_, lean_object* v_motive_4211_, lean_object* v_ctorIdx_4212_, lean_object* v_t_4213_, lean_object* v_h_4214_, lean_object* v_k_4215_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4213_, v_k_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4217_, lean_object* v_motive_4218_, lean_object* v_ctorIdx_4219_, lean_object* v_t_4220_, lean_object* v_h_4221_, lean_object* v_k_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4217_, v_motive_4218_, v_ctorIdx_4219_, v_t_4220_, v_h_4221_, v_k_4222_);
lean_dec(v_ctorIdx_4219_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4224_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4225_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4224_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4227_, lean_object* v_motive_4228_, lean_object* v_t_4229_, lean_object* v_h_4230_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4231_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4229_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4233_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4234_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4233_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4236_, lean_object* v_motive_4237_, lean_object* v_t_4238_, lean_object* v_h_4239_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4240_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4238_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4240_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4242_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4243_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4242_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4245_, lean_object* v_motive_4246_, lean_object* v_t_4247_, lean_object* v_h_4248_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4249_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4247_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4249_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4251_){
_start:
{
if (lean_obj_tag(v_capacity_4251_) == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4253_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4253_);
return v___x_4254_;
}
else
{
lean_object* v_val_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4272_; 
v_val_4255_ = lean_ctor_get(v_capacity_4251_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v_capacity_4251_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4257_ = v_capacity_4251_;
v_isShared_4258_ = v_isSharedCheck_4272_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_val_4255_);
lean_dec(v_capacity_4251_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4272_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v_zero_4259_; uint8_t v_isZero_4260_; 
v_zero_4259_ = lean_unsigned_to_nat(0u);
v_isZero_4260_ = lean_nat_dec_eq(v_val_4255_, v_zero_4259_);
if (v_isZero_4260_ == 1)
{
lean_object* v___x_4261_; lean_object* v___x_4263_; 
lean_dec(v_val_4255_);
v___x_4261_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v___x_4261_);
v___x_4263_ = v___x_4257_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4261_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
else
{
lean_object* v_one_4265_; lean_object* v_n_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4270_; 
v_one_4265_ = lean_unsigned_to_nat(1u);
v_n_4266_ = lean_nat_sub(v_val_4255_, v_one_4265_);
lean_dec(v_val_4255_);
v___x_4267_ = lean_nat_add(v_n_4266_, v_one_4265_);
lean_dec(v_n_4266_);
v___x_4268_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4267_);
if (v_isShared_4258_ == 0)
{
lean_ctor_set_tag(v___x_4257_, 2);
lean_ctor_set(v___x_4257_, 0, v___x_4268_);
v___x_4270_ = v___x_4257_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Std_CloseableChannel_new___redArg(v_capacity_4273_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4276_, lean_object* v_capacity_4277_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Std_CloseableChannel_new___redArg(v_capacity_4277_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4280_, lean_object* v_capacity_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Std_CloseableChannel_new(v_00_u03b1_4280_, v_capacity_4281_);
return v_res_4283_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4284_, lean_object* v_v_4285_){
_start:
{
switch(lean_obj_tag(v_ch_4284_))
{
case 0:
{
lean_object* v_ch_4287_; uint8_t v___x_4288_; 
v_ch_4287_ = lean_ctor_get(v_ch_4284_, 0);
lean_inc_ref(v_ch_4287_);
lean_dec_ref_known(v_ch_4284_, 1);
v___x_4288_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4287_, v_v_4285_);
return v___x_4288_;
}
case 1:
{
lean_object* v_ch_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v_ch_4289_ = lean_ctor_get(v_ch_4284_, 0);
lean_inc_ref(v_ch_4289_);
lean_dec_ref_known(v_ch_4284_, 1);
v___x_4290_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4289_, v_v_4285_);
v___x_4291_ = lean_unbox(v___x_4290_);
lean_dec(v___x_4290_);
return v___x_4291_;
}
default: 
{
lean_object* v_ch_4292_; lean_object* v___x_4293_; uint8_t v___x_4294_; 
v_ch_4292_ = lean_ctor_get(v_ch_4284_, 0);
lean_inc_ref(v_ch_4292_);
lean_dec_ref_known(v_ch_4284_, 1);
v___x_4293_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4292_, v_v_4285_);
v___x_4294_ = lean_unbox(v___x_4293_);
lean_dec(v___x_4293_);
return v___x_4294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4295_, lean_object* v_v_4296_, lean_object* v_a_4297_){
_start:
{
uint8_t v_res_4298_; lean_object* v_r_4299_; 
v_res_4298_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4295_, v_v_4296_);
v_r_4299_ = lean_box(v_res_4298_);
return v_r_4299_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4300_, lean_object* v_ch_4301_, lean_object* v_v_4302_){
_start:
{
uint8_t v___x_4304_; 
v___x_4304_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4301_, v_v_4302_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4305_, lean_object* v_ch_4306_, lean_object* v_v_4307_, lean_object* v_a_4308_){
_start:
{
uint8_t v_res_4309_; lean_object* v_r_4310_; 
v_res_4309_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4305_, v_ch_4306_, v_v_4307_);
v_r_4310_ = lean_box(v_res_4309_);
return v_r_4310_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4311_, lean_object* v_v_4312_){
_start:
{
switch(lean_obj_tag(v_ch_4311_))
{
case 0:
{
lean_object* v_ch_4314_; lean_object* v___x_4315_; 
v_ch_4314_ = lean_ctor_get(v_ch_4311_, 0);
lean_inc_ref(v_ch_4314_);
lean_dec_ref_known(v_ch_4311_, 1);
v___x_4315_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4314_, v_v_4312_);
return v___x_4315_;
}
case 1:
{
lean_object* v_ch_4316_; lean_object* v___x_4317_; 
v_ch_4316_ = lean_ctor_get(v_ch_4311_, 0);
lean_inc_ref(v_ch_4316_);
lean_dec_ref_known(v_ch_4311_, 1);
v___x_4317_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4316_, v_v_4312_);
return v___x_4317_;
}
default: 
{
lean_object* v_ch_4318_; lean_object* v___x_4319_; 
v_ch_4318_ = lean_ctor_get(v_ch_4311_, 0);
lean_inc_ref(v_ch_4318_);
lean_dec_ref_known(v_ch_4311_, 1);
v___x_4319_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4318_, v_v_4312_);
return v___x_4319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4320_, lean_object* v_v_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_Std_CloseableChannel_send___redArg(v_ch_4320_, v_v_4321_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4324_, lean_object* v_ch_4325_, lean_object* v_v_4326_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Std_CloseableChannel_send___redArg(v_ch_4325_, v_v_4326_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4329_, lean_object* v_ch_4330_, lean_object* v_v_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l_Std_CloseableChannel_send(v_00_u03b1_4329_, v_ch_4330_, v_v_4331_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4334_){
_start:
{
switch(lean_obj_tag(v_ch_4334_))
{
case 0:
{
lean_object* v_ch_4336_; lean_object* v___x_4337_; 
v_ch_4336_ = lean_ctor_get(v_ch_4334_, 0);
lean_inc_ref(v_ch_4336_);
lean_dec_ref_known(v_ch_4334_, 1);
v___x_4337_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4336_);
return v___x_4337_;
}
case 1:
{
lean_object* v_ch_4338_; lean_object* v___x_4339_; 
v_ch_4338_ = lean_ctor_get(v_ch_4334_, 0);
lean_inc_ref(v_ch_4338_);
lean_dec_ref_known(v_ch_4334_, 1);
v___x_4339_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4338_);
return v___x_4339_;
}
default: 
{
lean_object* v_ch_4340_; lean_object* v___x_4341_; 
v_ch_4340_ = lean_ctor_get(v_ch_4334_, 0);
lean_inc_ref(v_ch_4340_);
lean_dec_ref_known(v_ch_4334_, 1);
v___x_4341_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4340_);
return v___x_4341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4342_, lean_object* v_a_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Std_CloseableChannel_close___redArg(v_ch_4342_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4345_, lean_object* v_ch_4346_){
_start:
{
lean_object* v___x_4348_; 
v___x_4348_ = l_Std_CloseableChannel_close___redArg(v_ch_4346_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4349_, lean_object* v_ch_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Std_CloseableChannel_close(v_00_u03b1_4349_, v_ch_4350_);
return v_res_4352_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4353_){
_start:
{
switch(lean_obj_tag(v_ch_4353_))
{
case 0:
{
lean_object* v_ch_4355_; lean_object* v___x_4356_; uint8_t v___x_4357_; 
v_ch_4355_ = lean_ctor_get(v_ch_4353_, 0);
lean_inc_ref(v_ch_4355_);
lean_dec_ref_known(v_ch_4353_, 1);
v___x_4356_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4355_);
v___x_4357_ = lean_unbox(v___x_4356_);
lean_dec(v___x_4356_);
return v___x_4357_;
}
case 1:
{
lean_object* v_ch_4358_; lean_object* v___x_4359_; uint8_t v___x_4360_; 
v_ch_4358_ = lean_ctor_get(v_ch_4353_, 0);
lean_inc_ref(v_ch_4358_);
lean_dec_ref_known(v_ch_4353_, 1);
v___x_4359_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4358_);
v___x_4360_ = lean_unbox(v___x_4359_);
lean_dec(v___x_4359_);
return v___x_4360_;
}
default: 
{
lean_object* v_ch_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; 
v_ch_4361_ = lean_ctor_get(v_ch_4353_, 0);
lean_inc_ref(v_ch_4361_);
lean_dec_ref_known(v_ch_4353_, 1);
v___x_4362_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4361_);
v___x_4363_ = lean_unbox(v___x_4362_);
lean_dec(v___x_4362_);
return v___x_4363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4364_, lean_object* v_a_4365_){
_start:
{
uint8_t v_res_4366_; lean_object* v_r_4367_; 
v_res_4366_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4364_);
v_r_4367_ = lean_box(v_res_4366_);
return v_r_4367_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4368_, lean_object* v_ch_4369_){
_start:
{
uint8_t v___x_4371_; 
v___x_4371_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4369_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4372_, lean_object* v_ch_4373_, lean_object* v_a_4374_){
_start:
{
uint8_t v_res_4375_; lean_object* v_r_4376_; 
v_res_4375_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4372_, v_ch_4373_);
v_r_4376_ = lean_box(v_res_4375_);
return v_r_4376_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4377_){
_start:
{
switch(lean_obj_tag(v_ch_4377_))
{
case 0:
{
lean_object* v_ch_4379_; lean_object* v___x_4380_; 
v_ch_4379_ = lean_ctor_get(v_ch_4377_, 0);
lean_inc_ref(v_ch_4379_);
lean_dec_ref_known(v_ch_4377_, 1);
v___x_4380_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4379_);
return v___x_4380_;
}
case 1:
{
lean_object* v_ch_4381_; lean_object* v___x_4382_; 
v_ch_4381_ = lean_ctor_get(v_ch_4377_, 0);
lean_inc_ref(v_ch_4381_);
lean_dec_ref_known(v_ch_4377_, 1);
v___x_4382_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4381_);
return v___x_4382_;
}
default: 
{
lean_object* v_ch_4383_; lean_object* v___x_4384_; 
v_ch_4383_ = lean_ctor_get(v_ch_4377_, 0);
lean_inc_ref(v_ch_4383_);
lean_dec_ref_known(v_ch_4377_, 1);
v___x_4384_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4383_);
return v___x_4384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4385_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4388_, lean_object* v_ch_4389_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4389_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4392_, lean_object* v_ch_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4392_, v_ch_4393_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4396_){
_start:
{
switch(lean_obj_tag(v_ch_4396_))
{
case 0:
{
lean_object* v_ch_4398_; lean_object* v___x_4399_; 
v_ch_4398_ = lean_ctor_get(v_ch_4396_, 0);
lean_inc_ref(v_ch_4398_);
lean_dec_ref_known(v_ch_4396_, 1);
v___x_4399_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4398_);
return v___x_4399_;
}
case 1:
{
lean_object* v_ch_4400_; lean_object* v___x_4401_; 
v_ch_4400_ = lean_ctor_get(v_ch_4396_, 0);
lean_inc_ref(v_ch_4400_);
lean_dec_ref_known(v_ch_4396_, 1);
v___x_4401_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4400_);
return v___x_4401_;
}
default: 
{
lean_object* v_ch_4402_; lean_object* v___x_4403_; 
v_ch_4402_ = lean_ctor_get(v_ch_4396_, 0);
lean_inc_ref(v_ch_4402_);
lean_dec_ref_known(v_ch_4396_, 1);
v___x_4403_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4402_);
return v___x_4403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4404_, lean_object* v_a_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l_Std_CloseableChannel_recv___redArg(v_ch_4404_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4407_, lean_object* v_ch_4408_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Std_CloseableChannel_recv___redArg(v_ch_4408_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4411_, lean_object* v_ch_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l_Std_CloseableChannel_recv(v_00_u03b1_4411_, v_ch_4412_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4415_){
_start:
{
switch(lean_obj_tag(v_ch_4415_))
{
case 0:
{
lean_object* v_ch_4416_; lean_object* v___x_4417_; 
v_ch_4416_ = lean_ctor_get(v_ch_4415_, 0);
lean_inc_ref(v_ch_4416_);
lean_dec_ref_known(v_ch_4415_, 1);
v___x_4417_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4416_);
return v___x_4417_;
}
case 1:
{
lean_object* v_ch_4418_; lean_object* v___x_4419_; 
v_ch_4418_ = lean_ctor_get(v_ch_4415_, 0);
lean_inc_ref(v_ch_4418_);
lean_dec_ref_known(v_ch_4415_, 1);
v___x_4419_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4418_);
return v___x_4419_;
}
default: 
{
lean_object* v_ch_4420_; lean_object* v___x_4421_; 
v_ch_4420_ = lean_ctor_get(v_ch_4415_, 0);
lean_inc_ref(v_ch_4420_);
lean_dec_ref_known(v_ch_4415_, 1);
v___x_4421_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4420_);
return v___x_4421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4422_, lean_object* v_ch_4423_){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4423_);
return v___x_4424_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = lean_box(0);
v___x_4426_ = lean_task_pure(v___x_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4427_, lean_object* v_ch_4428_, lean_object* v_prio_4429_, lean_object* v_x_4430_){
_start:
{
if (lean_obj_tag(v_x_4430_) == 0)
{
lean_object* v___x_4432_; 
lean_dec(v_prio_4429_);
lean_dec_ref(v_ch_4428_);
lean_dec_ref(v_f_4427_);
v___x_4432_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4432_;
}
else
{
lean_object* v_val_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_val_4433_ = lean_ctor_get(v_x_4430_, 0);
lean_inc(v_val_4433_);
lean_dec_ref_known(v_x_4430_, 1);
lean_inc_ref(v_f_4427_);
v___x_4434_ = lean_apply_2(v_f_4427_, v_val_4433_, lean_box(0));
v___x_4435_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4427_, v_ch_4428_, v_prio_4429_);
return v___x_4435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4436_, lean_object* v_ch_4437_, lean_object* v_prio_4438_, lean_object* v_x_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4436_, v_ch_4437_, v_prio_4438_, v_x_4439_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4442_, lean_object* v_ch_4443_, lean_object* v_prio_4444_){
_start:
{
lean_object* v___f_4446_; lean_object* v___x_4447_; uint8_t v___x_4448_; lean_object* v___x_4449_; 
lean_inc(v_prio_4444_);
lean_inc_ref(v_ch_4443_);
v___f_4446_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4446_, 0, v_f_4442_);
lean_closure_set(v___f_4446_, 1, v_ch_4443_);
lean_closure_set(v___f_4446_, 2, v_prio_4444_);
v___x_4447_ = l_Std_CloseableChannel_recv___redArg(v_ch_4443_);
v___x_4448_ = 0;
v___x_4449_ = lean_io_bind_task(v___x_4447_, v___f_4446_, v_prio_4444_, v___x_4448_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4450_, lean_object* v_ch_4451_, lean_object* v_prio_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4450_, v_ch_4451_, v_prio_4452_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4455_, lean_object* v_f_4456_, lean_object* v_ch_4457_, lean_object* v_prio_4458_){
_start:
{
lean_object* v___x_4460_; 
v___x_4460_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4456_, v_ch_4457_, v_prio_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4461_, lean_object* v_f_4462_, lean_object* v_ch_4463_, lean_object* v_prio_4464_, lean_object* v_a_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4461_, v_f_4462_, v_ch_4463_, v_prio_4464_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(lean_object* v_x_4467_){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = lean_box(0);
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0___boxed(lean_object* v_x_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(v_x_4471_);
lean_dec_ref(v_x_4471_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg(){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__2));
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object* v___dummy_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
return v_res_4482_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4484_, lean_object* v_inst_4485_){
_start:
{
lean_object* v___x_4486_; 
v___x_4486_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4487_, lean_object* v_inst_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4487_, v_inst_4488_);
lean_dec(v_inst_4488_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object* v_a_4490_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4491_, 0, v_a_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object* v___f_4492_, lean_object* v_x_4493_){
_start:
{
if (lean_obj_tag(v_x_4493_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4503_; 
lean_dec_ref(v___f_4492_);
v_a_4495_ = lean_ctor_get(v_x_4493_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v_x_4493_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4497_ = v_x_4493_;
v_isShared_4498_ = v_isSharedCheck_4503_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v_x_4493_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4503_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4501_; 
v___x_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
}
}
else
{
lean_object* v_a_4504_; 
v_a_4504_ = lean_ctor_get(v_x_4493_, 0);
lean_inc(v_a_4504_);
lean_dec_ref_known(v_x_4493_, 1);
if (lean_obj_tag(v_a_4504_) == 0)
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4513_; 
lean_dec_ref(v___f_4492_);
v_a_4505_ = lean_ctor_get(v_a_4504_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v_a_4504_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4507_ = v_a_4504_;
v_isShared_4508_ = v_isSharedCheck_4513_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v_a_4504_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4513_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; 
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
return v___x_4511_;
}
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4515_; uint8_t v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_a_4514_ = lean_ctor_get(v_a_4504_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v_a_4504_, 1);
v___x_4515_ = lean_unsigned_to_nat(0u);
v___x_4516_ = 0;
v___x_4517_ = lean_task_map(v___f_4492_, v_a_4514_, v___x_4515_, v___x_4516_);
v___x_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object* v___f_4519_, lean_object* v_x_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_4519_, v_x_4520_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object* v___f_4523_, lean_object* v_receiver_4524_){
_start:
{
lean_object* v___x_4526_; uint8_t v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4526_ = lean_unsigned_to_nat(0u);
v___x_4527_ = 0;
v___x_4528_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4524_);
v___x_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4528_);
v___x_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
v___x_4532_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4526_, v___x_4527_, v___x_4531_, v___f_4523_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object* v___f_4533_, lean_object* v_receiver_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_4533_, v_receiver_4534_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg(){
_start:
{
lean_object* v___f_4543_; 
v___f_4543_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__2));
return v___f_4543_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object* v___dummy_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
return v_res_4545_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4547_, lean_object* v_inst_4548_){
_start:
{
lean_object* v___x_4549_; 
v___x_4549_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4550_, lean_object* v_inst_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4550_, v_inst_4551_);
lean_dec(v_inst_4551_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v___f_4554_, lean_object* v_x_4555_){
_start:
{
if (lean_obj_tag(v_x_4555_) == 0)
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4565_; 
lean_dec_ref(v___f_4554_);
v_a_4557_ = lean_ctor_get(v_x_4555_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v_x_4555_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4559_ = v_x_4555_;
v_isShared_4560_ = v_isSharedCheck_4565_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v_x_4555_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4565_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
lean_object* v___x_4563_; 
v___x_4563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
return v___x_4563_;
}
}
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v_a_4566_ = lean_ctor_get(v_x_4555_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v_x_4555_, 1);
v___x_4567_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___closed__0));
v___x_4568_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4568_, 0, lean_box(0));
lean_closure_set(v___x_4568_, 1, lean_box(0));
lean_closure_set(v___x_4568_, 2, lean_box(0));
lean_closure_set(v___x_4568_, 3, v___x_4567_);
lean_closure_set(v___x_4568_, 4, v___f_4554_);
v___x_4569_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4569_, 0, lean_box(0));
lean_closure_set(v___x_4569_, 1, lean_box(0));
lean_closure_set(v___x_4569_, 2, lean_box(0));
lean_closure_set(v___x_4569_, 3, v___x_4568_);
v___x_4570_ = lean_unsigned_to_nat(0u);
v___x_4571_ = 0;
v___x_4572_ = lean_task_map(v___x_4569_, v_a_4566_, v___x_4570_, v___x_4571_);
v___x_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
return v___x_4573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v___f_4574_, lean_object* v_x_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_4574_, v_x_4575_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v___f_4578_, lean_object* v_receiver_4579_, lean_object* v_x_4580_){
_start:
{
lean_object* v___x_4582_; uint8_t v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4582_ = lean_unsigned_to_nat(0u);
v___x_4583_ = 0;
v___x_4584_ = l_Std_CloseableChannel_send___redArg(v_receiver_4579_, v_x_4580_);
v___x_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
v___x_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
v___x_4587_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4582_, v___x_4583_, v___x_4586_, v___f_4578_);
return v___x_4587_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0___boxed(lean_object* v___f_4588_, lean_object* v_receiver_4589_, lean_object* v_x_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(v___f_4588_, v_receiver_4589_, v_x_4590_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v_x_4593_){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v_x_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(v_x_4596_);
lean_dec_ref(v_x_4596_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(lean_object* v___f_4599_, lean_object* v_socket_4600_, lean_object* v_x_4601_, lean_object* v___y_4602_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = lean_apply_3(v___f_4599_, v_socket_4600_, v___y_4602_, lean_box(0));
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object* v___f_4605_, lean_object* v_socket_4606_, lean_object* v_x_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(v___f_4605_, v_socket_4606_, v_x_4607_, v___y_4608_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(lean_object* v___f_4611_, lean_object* v___x_4612_, lean_object* v_socket_4613_, lean_object* v_data_4614_){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; 
v___x_4616_ = lean_unsigned_to_nat(0u);
v___x_4617_ = lean_array_get_size(v_data_4614_);
v___x_4618_ = lean_box(0);
v___x_4619_ = lean_nat_dec_lt(v___x_4616_, v___x_4617_);
if (v___x_4619_ == 0)
{
lean_object* v___x_4620_; 
lean_dec_ref(v_data_4614_);
lean_dec_ref(v_socket_4613_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___f_4611_);
v___x_4620_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4620_;
}
else
{
lean_object* v___f_4621_; uint8_t v___x_4622_; 
v___f_4621_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4621_, 0, v___f_4611_);
lean_closure_set(v___f_4621_, 1, v_socket_4613_);
v___x_4622_ = lean_nat_dec_le(v___x_4617_, v___x_4617_);
if (v___x_4622_ == 0)
{
if (v___x_4619_ == 0)
{
lean_object* v___x_4623_; 
lean_dec_ref(v___f_4621_);
lean_dec_ref(v_data_4614_);
lean_dec_ref(v___x_4612_);
v___x_4623_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4623_;
}
else
{
size_t v___x_4624_; size_t v___x_4625_; lean_object* v___x_749__overap_4626_; lean_object* v___x_4627_; 
v___x_4624_ = ((size_t)0ULL);
v___x_4625_ = lean_usize_of_nat(v___x_4617_);
v___x_749__overap_4626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4612_, v___f_4621_, v_data_4614_, v___x_4624_, v___x_4625_, v___x_4618_);
v___x_4627_ = lean_apply_1(v___x_749__overap_4626_, lean_box(0));
return v___x_4627_;
}
}
else
{
size_t v___x_4628_; size_t v___x_4629_; lean_object* v___x_752__overap_4630_; lean_object* v___x_4631_; 
v___x_4628_ = ((size_t)0ULL);
v___x_4629_ = lean_usize_of_nat(v___x_4617_);
v___x_752__overap_4630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4612_, v___f_4621_, v_data_4614_, v___x_4628_, v___x_4629_, v___x_4618_);
v___x_4631_ = lean_apply_1(v___x_752__overap_4630_, lean_box(0));
return v___x_4631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object* v___f_4632_, lean_object* v___x_4633_, lean_object* v_socket_4634_, lean_object* v_data_4635_, lean_object* v___y_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(v___f_4632_, v___x_4633_, v_socket_4634_, v_data_4635_);
return v_res_4637_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_4643_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___f_4645_; lean_object* v___f_4646_; 
v___x_4644_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_4645_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1));
v___f_4646_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4646_, 0, v___f_4645_);
lean_closure_set(v___f_4646_, 1, v___x_4644_);
return v___f_4646_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5(void){
_start:
{
lean_object* v___f_4647_; lean_object* v___f_4648_; lean_object* v___f_4649_; lean_object* v___x_4650_; 
v___f_4647_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_4648_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4);
v___f_4649_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1));
v___x_4650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4650_, 0, v___f_4649_);
lean_ctor_set(v___x_4650_, 1, v___f_4648_);
lean_ctor_set(v___x_4650_, 2, v___f_4647_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_4652_; 
v___x_4652_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5);
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
return v_res_4654_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4656_, lean_object* v_inst_4657_){
_start:
{
lean_object* v___x_4658_; 
v___x_4658_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4659_, lean_object* v_inst_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4659_, v_inst_4660_);
lean_dec(v_inst_4660_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4662_){
_start:
{
lean_inc_ref(v_ch_4662_);
return v_ch_4662_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Std_CloseableChannel_sync___redArg(v_ch_4663_);
lean_dec_ref(v_ch_4663_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4665_, lean_object* v_ch_4666_){
_start:
{
lean_inc_ref(v_ch_4666_);
return v_ch_4666_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4667_, lean_object* v_ch_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_Std_CloseableChannel_sync(v_00_u03b1_4667_, v_ch_4668_);
lean_dec_ref(v_ch_4668_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4670_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l_Std_CloseableChannel_new___redArg(v_capacity_4670_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4673_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4676_, lean_object* v_capacity_4677_){
_start:
{
lean_object* v___x_4679_; 
v___x_4679_ = l_Std_CloseableChannel_new___redArg(v_capacity_4677_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4680_, lean_object* v_capacity_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4680_, v_capacity_4681_);
return v_res_4683_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4684_, lean_object* v_v_4685_){
_start:
{
uint8_t v___x_4687_; 
v___x_4687_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4684_, v_v_4685_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4688_, lean_object* v_v_4689_, lean_object* v_a_4690_){
_start:
{
uint8_t v_res_4691_; lean_object* v_r_4692_; 
v_res_4691_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4688_, v_v_4689_);
v_r_4692_ = lean_box(v_res_4691_);
return v_r_4692_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4693_, lean_object* v_ch_4694_, lean_object* v_v_4695_){
_start:
{
uint8_t v___x_4697_; 
v___x_4697_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4694_, v_v_4695_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4698_, lean_object* v_ch_4699_, lean_object* v_v_4700_, lean_object* v_a_4701_){
_start:
{
uint8_t v_res_4702_; lean_object* v_r_4703_; 
v_res_4702_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4698_, v_ch_4699_, v_v_4700_);
v_r_4703_ = lean_box(v_res_4702_);
return v_r_4703_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4704_, lean_object* v_v_4705_){
_start:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = l_Std_CloseableChannel_send___redArg(v_ch_4704_, v_v_4705_);
v___x_4708_ = lean_io_wait(v___x_4707_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4708_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4708_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
lean_ctor_set_tag(v___x_4711_, 1);
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
else
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
v_a_4717_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4719_ = v___x_4708_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4708_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
lean_ctor_set_tag(v___x_4719_, 0);
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_4725_, lean_object* v_v_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4725_, v_v_4726_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_4729_, lean_object* v_ch_4730_, lean_object* v_v_4731_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4730_, v_v_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_4734_, lean_object* v_ch_4735_, lean_object* v_v_4736_, lean_object* v_a_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_4734_, v_ch_4735_, v_v_4736_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_4739_){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = l_Std_CloseableChannel_close___redArg(v_ch_4739_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_4742_, lean_object* v_a_4743_){
_start:
{
lean_object* v_res_4744_; 
v_res_4744_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_4742_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_4745_, lean_object* v_ch_4746_){
_start:
{
lean_object* v___x_4748_; 
v___x_4748_ = l_Std_CloseableChannel_close___redArg(v_ch_4746_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_4749_, lean_object* v_ch_4750_, lean_object* v_a_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_4749_, v_ch_4750_);
return v_res_4752_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_4753_){
_start:
{
uint8_t v___x_4755_; 
v___x_4755_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4753_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_4756_, lean_object* v_a_4757_){
_start:
{
uint8_t v_res_4758_; lean_object* v_r_4759_; 
v_res_4758_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_4756_);
v_r_4759_ = lean_box(v_res_4758_);
return v_r_4759_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_4760_, lean_object* v_ch_4761_){
_start:
{
uint8_t v___x_4763_; 
v___x_4763_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4761_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_4764_, lean_object* v_ch_4765_, lean_object* v_a_4766_){
_start:
{
uint8_t v_res_4767_; lean_object* v_r_4768_; 
v_res_4767_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_4764_, v_ch_4765_);
v_r_4768_ = lean_box(v_res_4767_);
return v_r_4768_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_4769_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4769_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_4772_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_4775_, lean_object* v_ch_4776_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4776_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_4779_, lean_object* v_ch_4780_, lean_object* v_a_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_4779_, v_ch_4780_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_4783_){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4785_ = l_Std_CloseableChannel_recv___redArg(v_ch_4783_);
v___x_4786_ = lean_io_wait(v___x_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_4787_, lean_object* v_a_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4787_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_4790_, lean_object* v_ch_4791_){
_start:
{
lean_object* v___x_4793_; 
v___x_4793_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4791_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_4794_, lean_object* v_ch_4795_, lean_object* v_a_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_4794_, v_ch_4795_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_4798_, lean_object* v_b_4799_, lean_object* v_f_4800_, lean_object* v_toBind_4801_, lean_object* v___f_4802_, lean_object* v_____do__lift_4803_){
_start:
{
if (lean_obj_tag(v_____do__lift_4803_) == 0)
{
lean_object* v___x_4804_; 
lean_dec(v___f_4802_);
lean_dec(v_toBind_4801_);
lean_dec(v_f_4800_);
v___x_4804_ = lean_apply_2(v_toPure_4798_, lean_box(0), v_b_4799_);
return v___x_4804_;
}
else
{
lean_object* v_val_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
lean_dec(v_toPure_4798_);
v_val_4805_ = lean_ctor_get(v_____do__lift_4803_, 0);
lean_inc(v_val_4805_);
lean_dec_ref_known(v_____do__lift_4803_, 1);
v___x_4806_ = lean_apply_2(v_f_4800_, v_val_4805_, v_b_4799_);
v___x_4807_ = lean_apply_4(v_toBind_4801_, lean_box(0), lean_box(0), v___x_4806_, v___f_4802_);
return v___x_4807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_4808_, lean_object* v_inst_4809_, lean_object* v_ch_4810_, lean_object* v_f_4811_, lean_object* v_b_4812_){
_start:
{
lean_object* v_toApplicative_4813_; lean_object* v_toBind_4814_; lean_object* v_toPure_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___f_4818_; lean_object* v___f_4819_; lean_object* v___x_4820_; 
v_toApplicative_4813_ = lean_ctor_get(v_inst_4808_, 0);
v_toBind_4814_ = lean_ctor_get(v_inst_4808_, 1);
lean_inc_n(v_toBind_4814_, 2);
v_toPure_4815_ = lean_ctor_get(v_toApplicative_4813_, 1);
lean_inc_n(v_toPure_4815_, 2);
lean_inc_ref(v_ch_4810_);
v___x_4816_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_4816_, 0, lean_box(0));
lean_closure_set(v___x_4816_, 1, v_ch_4810_);
lean_inc(v_inst_4809_);
v___x_4817_ = lean_apply_2(v_inst_4809_, lean_box(0), v___x_4816_);
lean_inc(v_f_4811_);
v___f_4818_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4818_, 0, v_toPure_4815_);
lean_closure_set(v___f_4818_, 1, v_inst_4808_);
lean_closure_set(v___f_4818_, 2, v_inst_4809_);
lean_closure_set(v___f_4818_, 3, v_ch_4810_);
lean_closure_set(v___f_4818_, 4, v_f_4811_);
v___f_4819_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_4819_, 0, v_toPure_4815_);
lean_closure_set(v___f_4819_, 1, v_b_4812_);
lean_closure_set(v___f_4819_, 2, v_f_4811_);
lean_closure_set(v___f_4819_, 3, v_toBind_4814_);
lean_closure_set(v___f_4819_, 4, v___f_4818_);
v___x_4820_ = lean_apply_4(v_toBind_4814_, lean_box(0), lean_box(0), v___x_4817_, v___f_4819_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_4821_, lean_object* v_inst_4822_, lean_object* v_inst_4823_, lean_object* v_ch_4824_, lean_object* v_f_4825_, lean_object* v_____do__lift_4826_){
_start:
{
if (lean_obj_tag(v_____do__lift_4826_) == 0)
{
lean_object* v_a_4827_; lean_object* v___x_4828_; 
lean_dec(v_f_4825_);
lean_dec_ref(v_ch_4824_);
lean_dec(v_inst_4823_);
lean_dec_ref(v_inst_4822_);
v_a_4827_ = lean_ctor_get(v_____do__lift_4826_, 0);
lean_inc(v_a_4827_);
lean_dec_ref_known(v_____do__lift_4826_, 1);
v___x_4828_ = lean_apply_2(v_toPure_4821_, lean_box(0), v_a_4827_);
return v___x_4828_;
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4830_; 
lean_dec(v_toPure_4821_);
v_a_4829_ = lean_ctor_get(v_____do__lift_4826_, 0);
lean_inc(v_a_4829_);
lean_dec_ref_known(v_____do__lift_4826_, 1);
v___x_4830_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4822_, v_inst_4823_, v_ch_4824_, v_f_4825_, v_a_4829_);
return v___x_4830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_4831_, lean_object* v_00_u03b1_4832_, lean_object* v_00_u03b2_4833_, lean_object* v_inst_4834_, lean_object* v_inst_4835_, lean_object* v_ch_4836_, lean_object* v_f_4837_, lean_object* v_b_4838_){
_start:
{
lean_object* v___x_4839_; 
v___x_4839_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4834_, v_inst_4835_, v_ch_4836_, v_f_4837_, v_b_4838_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_4840_, lean_object* v_inst_4841_, lean_object* v_ch_4842_, lean_object* v_b_4843_, lean_object* v_f_4844_){
_start:
{
lean_object* v___x_4845_; 
v___x_4845_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4840_, v_inst_4841_, v_ch_4842_, v_f_4844_, v_b_4843_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_4846_, lean_object* v_00_u03b1_4847_, lean_object* v_inst_4848_, lean_object* v_inst_4849_, lean_object* v_00_u03b2_4850_, lean_object* v_ch_4851_, lean_object* v_b_4852_, lean_object* v_f_4853_){
_start:
{
lean_object* v___x_4854_; 
v___x_4854_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4848_, v_inst_4849_, v_ch_4851_, v_f_4853_, v_b_4852_);
return v___x_4854_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_4855_, lean_object* v_inst_4856_, lean_object* v_00_u03b2_4857_, lean_object* v_ch_4858_, lean_object* v_b_4859_, lean_object* v_f_4860_){
_start:
{
lean_object* v___x_4861_; 
v___x_4861_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4855_, v_inst_4856_, v_ch_4858_, v_f_4860_, v_b_4859_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_4862_, lean_object* v_inst_4863_){
_start:
{
lean_object* v___f_4864_; 
v___f_4864_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4864_, 0, v_inst_4862_);
lean_closure_set(v___f_4864_, 1, v_inst_4863_);
return v___f_4864_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_4865_, lean_object* v_00_u03b1_4866_, lean_object* v_inst_4867_, lean_object* v_inst_4868_){
_start:
{
lean_object* v___f_4869_; 
v___f_4869_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4869_, 0, v_inst_4867_);
lean_closure_set(v___f_4869_, 1, v_inst_4868_);
return v___f_4869_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_4870_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l_Std_CloseableChannel_new___redArg(v_capacity_4870_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_4873_, lean_object* v_a_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l_Std_Channel_new___redArg(v_capacity_4873_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_4876_, lean_object* v_capacity_4877_){
_start:
{
lean_object* v___x_4879_; 
v___x_4879_ = l_Std_CloseableChannel_new___redArg(v_capacity_4877_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_4880_, lean_object* v_capacity_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l_Std_Channel_new(v_00_u03b1_4880_, v_capacity_4881_);
return v_res_4883_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_4884_, lean_object* v_v_4885_){
_start:
{
uint8_t v___x_4887_; 
v___x_4887_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4884_, v_v_4885_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_4888_, lean_object* v_v_4889_, lean_object* v_a_4890_){
_start:
{
uint8_t v_res_4891_; lean_object* v_r_4892_; 
v_res_4891_ = l_Std_Channel_trySend___redArg(v_ch_4888_, v_v_4889_);
v_r_4892_ = lean_box(v_res_4891_);
return v_r_4892_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_4893_, lean_object* v_ch_4894_, lean_object* v_v_4895_){
_start:
{
uint8_t v___x_4897_; 
v___x_4897_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4894_, v_v_4895_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_4898_, lean_object* v_ch_4899_, lean_object* v_v_4900_, lean_object* v_a_4901_){
_start:
{
uint8_t v_res_4902_; lean_object* v_r_4903_; 
v_res_4902_ = l_Std_Channel_trySend(v_00_u03b1_4898_, v_ch_4899_, v_v_4900_);
v_r_4903_ = lean_box(v_res_4902_);
return v_r_4903_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4904_ = lean_box(0);
v___x_4905_ = lean_task_pure(v___x_4904_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_4906_){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_142__overap_4911_; lean_object* v___x_4912_; 
v___x_4908_ = l_instMonadBaseIO;
v___x_4909_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4910_ = l_instInhabitedOfMonad___redArg(v___x_4908_, v___x_4909_);
v___x_142__overap_4911_ = lean_panic_fn_borrowed(v___x_4910_, v_msg_4906_);
lean_dec(v___x_4910_);
v___x_4912_ = lean_apply_1(v___x_142__overap_4911_, lean_box(0));
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_4913_);
return v_res_4915_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
v___x_4919_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4920_ = lean_unsigned_to_nat(21u);
v___x_4921_ = lean_unsigned_to_nat(869u);
v___x_4922_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_4923_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4924_ = l_mkPanicMessageWithDecl(v___x_4923_, v___x_4922_, v___x_4921_, v___x_4920_, v___x_4919_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_4925_){
_start:
{
if (lean_obj_tag(v_x_4925_) == 0)
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_4928_ = l_panic___at___00Std_Channel_send_spec__0(v___x_4927_);
return v___x_4928_;
}
else
{
lean_object* v___x_4929_; 
v___x_4929_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4929_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Std_Channel_send___redArg___lam__0(v_x_4930_);
lean_dec_ref(v_x_4930_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_4934_, lean_object* v_v_4935_){
_start:
{
lean_object* v___f_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; uint8_t v___x_4940_; lean_object* v___x_4941_; 
v___f_4937_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_4938_ = l_Std_CloseableChannel_send___redArg(v_ch_4934_, v_v_4935_);
v___x_4939_ = lean_unsigned_to_nat(0u);
v___x_4940_ = 1;
v___x_4941_ = lean_io_bind_task(v___x_4938_, v___f_4937_, v___x_4939_, v___x_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_4942_, lean_object* v_v_4943_, lean_object* v_a_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Std_Channel_send___redArg(v_ch_4942_, v_v_4943_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_4946_, lean_object* v_ch_4947_, lean_object* v_v_4948_){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = l_Std_Channel_send___redArg(v_ch_4947_, v_v_4948_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_4951_, lean_object* v_ch_4952_, lean_object* v_v_4953_, lean_object* v_a_4954_){
_start:
{
lean_object* v_res_4955_; 
v_res_4955_ = l_Std_Channel_send(v_00_u03b1_4951_, v_ch_4952_, v_v_4953_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_4956_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4956_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_4959_, lean_object* v_a_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l_Std_Channel_tryRecv___redArg(v_ch_4959_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_4962_, lean_object* v_ch_4963_){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4963_);
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_4966_, lean_object* v_ch_4967_, lean_object* v_a_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Std_Channel_tryRecv(v_00_u03b1_4966_, v_ch_4967_);
return v_res_4969_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4971_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4972_ = lean_unsigned_to_nat(16u);
v___x_4973_ = lean_unsigned_to_nat(880u);
v___x_4974_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_4975_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4976_ = l_mkPanicMessageWithDecl(v___x_4975_, v___x_4974_, v___x_4973_, v___x_4972_, v___x_4971_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_4977_, lean_object* v_x_4978_){
_start:
{
if (lean_obj_tag(v_x_4978_) == 0)
{
lean_object* v___x_4980_; lean_object* v___x_144__overap_4981_; lean_object* v___x_4982_; 
v___x_4980_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_144__overap_4981_ = l_panic___redArg(v___x_4977_, v___x_4980_);
v___x_4982_ = lean_apply_1(v___x_144__overap_4981_, lean_box(0));
return v___x_4982_;
}
else
{
lean_object* v_val_4983_; lean_object* v___x_4984_; 
v_val_4983_ = lean_ctor_get(v_x_4978_, 0);
lean_inc(v_val_4983_);
lean_dec_ref_known(v_x_4978_, 1);
v___x_4984_ = lean_task_pure(v_val_4983_);
return v___x_4984_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_4985_, lean_object* v_x_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Std_Channel_recv___redArg___lam__0(v___x_4985_, v_x_4986_);
lean_dec(v___x_4985_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_4989_, lean_object* v_ch_4990_){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___f_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; uint8_t v___x_4998_; lean_object* v___x_4999_; 
v___x_4992_ = l_instMonadBaseIO;
v___x_4993_ = lean_task_pure(v_inst_4989_);
v___x_4994_ = l_instInhabitedOfMonad___redArg(v___x_4992_, v___x_4993_);
v___f_4995_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4995_, 0, v___x_4994_);
v___x_4996_ = l_Std_CloseableChannel_recv___redArg(v_ch_4990_);
v___x_4997_ = lean_unsigned_to_nat(0u);
v___x_4998_ = 1;
v___x_4999_ = lean_io_bind_task(v___x_4996_, v___f_4995_, v___x_4997_, v___x_4998_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_5000_, lean_object* v_ch_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Std_Channel_recv___redArg(v_inst_5000_, v_ch_5001_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_5004_, lean_object* v_inst_5005_, lean_object* v_ch_5006_){
_start:
{
lean_object* v___x_5008_; 
v___x_5008_ = l_Std_Channel_recv___redArg(v_inst_5005_, v_ch_5006_);
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_5009_, lean_object* v_inst_5010_, lean_object* v_ch_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Std_Channel_recv(v_00_u03b1_5009_, v_inst_5010_, v_ch_5011_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_5014_){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5016_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5014_);
v___x_5017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5016_);
v___x_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5017_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5019_);
return v_res_5021_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5025_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_5026_ = lean_unsigned_to_nat(14u);
v___x_5027_ = lean_unsigned_to_nat(22u);
v___x_5028_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_5029_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_5030_ = l_mkPanicMessageWithDecl(v___x_5029_, v___x_5028_, v___x_5027_, v___x_5026_, v___x_5025_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_5031_, lean_object* v_inst_5032_, lean_object* v_x_5033_){
_start:
{
lean_object* v___y_5036_; lean_object* v___y_5040_; 
if (lean_obj_tag(v_x_5033_) == 0)
{
lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5042_ = lean_box(0);
v___x_5043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5042_);
return v___x_5043_;
}
else
{
lean_object* v_val_5044_; 
v_val_5044_ = lean_ctor_get(v_x_5033_, 0);
lean_inc(v_val_5044_);
lean_dec_ref_known(v_x_5033_, 1);
if (lean_obj_tag(v_val_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
v_a_5045_ = lean_ctor_get(v_val_5044_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v_val_5044_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v_val_5044_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v_val_5044_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
v___y_5036_ = v___x_5050_;
goto v___jp_5035_;
}
}
}
else
{
lean_object* v_a_5053_; 
v_a_5053_ = lean_ctor_get(v_val_5044_, 0);
lean_inc(v_a_5053_);
lean_dec_ref_known(v_val_5044_, 1);
if (lean_obj_tag(v_a_5053_) == 0)
{
lean_object* v___x_5054_; lean_object* v___x_5055_; 
v___x_5054_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5055_ = l_panic___redArg(v_inst_5032_, v___x_5054_);
v___y_5040_ = v___x_5055_;
goto v___jp_5039_;
}
else
{
lean_object* v_val_5056_; 
v_val_5056_ = lean_ctor_get(v_a_5053_, 0);
lean_inc(v_val_5056_);
lean_dec_ref_known(v_a_5053_, 1);
v___y_5040_ = v_val_5056_;
goto v___jp_5039_;
}
}
}
v___jp_5035_:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5037_ = lean_io_promise_resolve(v___y_5036_, v_promise_5031_);
v___x_5038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5037_);
return v___x_5038_;
}
v___jp_5039_:
{
lean_object* v___x_5041_; 
v___x_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5041_, 0, v___y_5040_);
v___y_5036_ = v___x_5041_;
goto v___jp_5035_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5057_, lean_object* v_inst_5058_, lean_object* v_x_5059_, lean_object* v___y_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5057_, v_inst_5058_, v_x_5059_);
lean_dec(v_inst_5058_);
lean_dec(v_promise_5057_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5062_, lean_object* v___f_5063_, lean_object* v_x_5064_){
_start:
{
lean_object* v_val_5067_; 
if (lean_obj_tag(v_x_5064_) == 0)
{
lean_object* v___x_5069_; 
lean_dec_ref(v___f_5063_);
v___x_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5069_, 0, v_x_5064_);
return v___x_5069_;
}
else
{
lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5085_; 
v_isSharedCheck_5085_ = !lean_is_exclusive(v_x_5064_);
if (v_isSharedCheck_5085_ == 0)
{
lean_object* v_unused_5086_; 
v_unused_5086_ = lean_ctor_get(v_x_5064_, 0);
lean_dec(v_unused_5086_);
v___x_5071_ = v_x_5064_;
v_isShared_5072_ = v_isSharedCheck_5085_;
goto v_resetjp_5070_;
}
else
{
lean_dec(v_x_5064_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5085_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; uint8_t v___x_5075_; lean_object* v___x_5076_; 
v___x_5073_ = lean_io_promise_result_opt(v_a_5062_);
v___x_5074_ = lean_unsigned_to_nat(0u);
v___x_5075_ = 1;
v___x_5076_ = l_EIO_chainTask___redArg(v___x_5073_, v___f_5063_, v___x_5074_, v___x_5075_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; lean_object* v___x_5079_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_a_5077_);
lean_dec_ref_known(v___x_5076_, 1);
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 0, v_a_5077_);
v___x_5079_ = v___x_5071_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5077_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
v_val_5067_ = v___x_5079_;
goto v___jp_5066_;
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; 
v_a_5081_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_a_5081_);
lean_dec_ref_known(v___x_5076_, 1);
if (v_isShared_5072_ == 0)
{
lean_ctor_set_tag(v___x_5071_, 0);
lean_ctor_set(v___x_5071_, 0, v_a_5081_);
v___x_5083_ = v___x_5071_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5081_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
v_val_5067_ = v___x_5083_;
goto v___jp_5066_;
}
}
}
}
v___jp_5066_:
{
lean_object* v___x_5068_; 
v___x_5068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5068_, 0, v_val_5067_);
return v___x_5068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5087_, lean_object* v___f_5088_, lean_object* v_x_5089_, lean_object* v___y_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5087_, v___f_5088_, v_x_5089_);
lean_dec(v_a_5087_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5092_, lean_object* v___f_5093_, lean_object* v_finished_5094_, lean_object* v_x_5095_){
_start:
{
if (lean_obj_tag(v_x_5095_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5105_; 
lean_dec(v_finished_5094_);
lean_dec_ref(v___f_5093_);
lean_dec_ref(v_sel_5092_);
v_a_5097_ = lean_ctor_get(v_x_5095_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v_x_5095_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5099_ = v_x_5095_;
v_isShared_5100_ = v_isSharedCheck_5105_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v_x_5095_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5105_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5097_);
v___x_5102_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
lean_object* v___x_5103_; 
v___x_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5102_);
return v___x_5103_;
}
}
}
else
{
lean_object* v_a_5106_; lean_object* v_registerFn_5107_; lean_object* v___f_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; uint8_t v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v_a_5106_ = lean_ctor_get(v_x_5095_, 0);
lean_inc_n(v_a_5106_, 2);
lean_dec_ref_known(v_x_5095_, 1);
v_registerFn_5107_ = lean_ctor_get(v_sel_5092_, 1);
lean_inc_ref(v_registerFn_5107_);
lean_dec_ref(v_sel_5092_);
v___f_5108_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5108_, 0, v_a_5106_);
lean_closure_set(v___f_5108_, 1, v___f_5093_);
v___x_5109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5109_, 0, v_finished_5094_);
lean_ctor_set(v___x_5109_, 1, v_a_5106_);
v___x_5110_ = lean_unsigned_to_nat(0u);
v___x_5111_ = 0;
v___x_5112_ = lean_apply_2(v_registerFn_5107_, v___x_5109_, lean_box(0));
v___x_5113_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5110_, v___x_5111_, v___x_5112_, v___f_5108_);
return v___x_5113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5114_, lean_object* v___f_5115_, lean_object* v_finished_5116_, lean_object* v_x_5117_, lean_object* v___y_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5114_, v___f_5115_, v_finished_5116_, v_x_5117_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5120_, lean_object* v_sel_5121_, lean_object* v_waiter_5122_){
_start:
{
lean_object* v_finished_5124_; lean_object* v_promise_5125_; lean_object* v___f_5126_; lean_object* v___f_5127_; lean_object* v___x_5128_; uint8_t v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; 
v_finished_5124_ = lean_ctor_get(v_waiter_5122_, 0);
lean_inc(v_finished_5124_);
v_promise_5125_ = lean_ctor_get(v_waiter_5122_, 1);
lean_inc(v_promise_5125_);
lean_dec_ref(v_waiter_5122_);
v___f_5126_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5126_, 0, v_promise_5125_);
lean_closure_set(v___f_5126_, 1, v_inst_5120_);
v___f_5127_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5127_, 0, v_sel_5121_);
lean_closure_set(v___f_5127_, 1, v___f_5126_);
lean_closure_set(v___f_5127_, 2, v_finished_5124_);
v___x_5128_ = lean_unsigned_to_nat(0u);
v___x_5129_ = 0;
v___x_5130_ = lean_io_promise_new();
v___x_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5131_, 0, v___x_5130_);
v___x_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5132_, 0, v___x_5131_);
v___x_5133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5128_, v___x_5129_, v___x_5132_, v___f_5127_);
return v___x_5133_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5134_, lean_object* v_sel_5135_, lean_object* v_waiter_5136_, lean_object* v___y_5137_){
_start:
{
lean_object* v_res_5138_; 
v_res_5138_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5134_, v_sel_5135_, v_waiter_5136_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5139_, lean_object* v_ch_5140_){
_start:
{
lean_object* v_sel_5141_; lean_object* v_unregisterFn_5142_; lean_object* v___f_5143_; lean_object* v___f_5144_; lean_object* v___x_5145_; 
lean_inc_ref(v_ch_5140_);
v_sel_5141_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5140_);
v_unregisterFn_5142_ = lean_ctor_get(v_sel_5141_, 2);
lean_inc_ref(v_unregisterFn_5142_);
v___f_5143_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5143_, 0, v_ch_5140_);
v___f_5144_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5144_, 0, v_inst_5139_);
lean_closure_set(v___f_5144_, 1, v_sel_5141_);
v___x_5145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5145_, 0, v___f_5143_);
lean_ctor_set(v___x_5145_, 1, v___f_5144_);
lean_ctor_set(v___x_5145_, 2, v_unregisterFn_5142_);
return v___x_5145_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5146_, lean_object* v_inst_5147_, lean_object* v_ch_5148_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l_Std_Channel_recvSelector___redArg(v_inst_5147_, v_ch_5148_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5150_, lean_object* v_inst_5151_, lean_object* v_ch_5152_, lean_object* v_prio_5153_, lean_object* v_v_5154_, lean_object* v___y_5155_){
_start:
{
lean_object* v_res_5156_; 
v_res_5156_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5150_, v_inst_5151_, v_ch_5152_, v_prio_5153_, v_v_5154_);
return v_res_5156_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5157_, lean_object* v_f_5158_, lean_object* v_ch_5159_, lean_object* v_prio_5160_){
_start:
{
lean_object* v___f_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; lean_object* v___x_5165_; 
lean_inc(v_prio_5160_);
lean_inc_ref(v_ch_5159_);
lean_inc(v_inst_5157_);
v___f_5162_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5162_, 0, v_f_5158_);
lean_closure_set(v___f_5162_, 1, v_inst_5157_);
lean_closure_set(v___f_5162_, 2, v_ch_5159_);
lean_closure_set(v___f_5162_, 3, v_prio_5160_);
v___x_5163_ = l_Std_Channel_recv___redArg(v_inst_5157_, v_ch_5159_);
v___x_5164_ = 0;
v___x_5165_ = lean_io_bind_task(v___x_5163_, v___f_5162_, v_prio_5160_, v___x_5164_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5166_, lean_object* v_inst_5167_, lean_object* v_ch_5168_, lean_object* v_prio_5169_, lean_object* v_v_5170_){
_start:
{
lean_object* v___x_5172_; lean_object* v___x_5173_; 
lean_inc_ref(v_f_5166_);
v___x_5172_ = lean_apply_2(v_f_5166_, v_v_5170_, lean_box(0));
v___x_5173_ = l_Std_Channel_forAsync___redArg(v_inst_5167_, v_f_5166_, v_ch_5168_, v_prio_5169_);
return v___x_5173_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5174_, lean_object* v_f_5175_, lean_object* v_ch_5176_, lean_object* v_prio_5177_, lean_object* v_a_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_Std_Channel_forAsync___redArg(v_inst_5174_, v_f_5175_, v_ch_5176_, v_prio_5177_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5180_, lean_object* v_inst_5181_, lean_object* v_f_5182_, lean_object* v_ch_5183_, lean_object* v_prio_5184_){
_start:
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Std_Channel_forAsync___redArg(v_inst_5181_, v_f_5182_, v_ch_5183_, v_prio_5184_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5187_, lean_object* v_inst_5188_, lean_object* v_f_5189_, lean_object* v_ch_5190_, lean_object* v_prio_5191_, lean_object* v_a_5192_){
_start:
{
lean_object* v_res_5193_; 
v_res_5193_ = l_Std_Channel_forAsync(v_00_u03b1_5187_, v_inst_5188_, v_f_5189_, v_ch_5190_, v_prio_5191_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5194_, lean_object* v_channel_5195_){
_start:
{
lean_object* v___x_5196_; 
v___x_5196_ = l_Std_Channel_recvSelector___redArg(v_inst_5194_, v_channel_5195_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5197_){
_start:
{
lean_object* v___f_5198_; lean_object* v___f_5199_; lean_object* v___x_5200_; 
v___f_5198_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5198_, 0, v_inst_5197_);
v___f_5199_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__1));
v___x_5200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5200_, 0, v___f_5198_);
lean_ctor_set(v___x_5200_, 1, v___f_5199_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5201_, lean_object* v_inst_5202_){
_start:
{
lean_object* v___x_5203_; 
v___x_5203_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5202_);
return v___x_5203_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5204_){
_start:
{
lean_object* v___x_5205_; 
v___x_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5205_, 0, v_a_5204_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5206_, lean_object* v_x_5207_){
_start:
{
if (lean_obj_tag(v_x_5207_) == 0)
{
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5217_; 
lean_dec_ref(v___f_5206_);
v_a_5209_ = lean_ctor_get(v_x_5207_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v_x_5207_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5211_ = v_x_5207_;
v_isShared_5212_ = v_isSharedCheck_5217_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v_x_5207_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5217_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5214_; 
if (v_isShared_5212_ == 0)
{
v___x_5214_ = v___x_5211_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5209_);
v___x_5214_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
lean_object* v___x_5215_; 
v___x_5215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5215_, 0, v___x_5214_);
return v___x_5215_;
}
}
}
else
{
lean_object* v_a_5218_; 
v_a_5218_ = lean_ctor_get(v_x_5207_, 0);
lean_inc(v_a_5218_);
lean_dec_ref_known(v_x_5207_, 1);
if (lean_obj_tag(v_a_5218_) == 0)
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5227_; 
lean_dec_ref(v___f_5206_);
v_a_5219_ = lean_ctor_get(v_a_5218_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v_a_5218_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5221_ = v_a_5218_;
v_isShared_5222_ = v_isSharedCheck_5227_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v_a_5218_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5227_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v___x_5224_; 
if (v_isShared_5222_ == 0)
{
v___x_5224_ = v___x_5221_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5219_);
v___x_5224_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
lean_object* v___x_5225_; 
v___x_5225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5224_);
return v___x_5225_;
}
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5229_; uint8_t v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; 
v_a_5228_ = lean_ctor_get(v_a_5218_, 0);
lean_inc(v_a_5228_);
lean_dec_ref_known(v_a_5218_, 1);
v___x_5229_ = lean_unsigned_to_nat(0u);
v___x_5230_ = 0;
v___x_5231_ = lean_task_map(v___f_5206_, v_a_5228_, v___x_5229_, v___x_5230_);
v___x_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
return v___x_5232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5233_, lean_object* v_x_5234_, lean_object* v___y_5235_){
_start:
{
lean_object* v_res_5236_; 
v_res_5236_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5233_, v_x_5234_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5237_, lean_object* v___f_5238_, lean_object* v_receiver_5239_){
_start:
{
lean_object* v___x_5241_; uint8_t v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
v___x_5241_ = lean_unsigned_to_nat(0u);
v___x_5242_ = 0;
v___x_5243_ = l_Std_Channel_recv___redArg(v_inst_5237_, v_receiver_5239_);
v___x_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5244_, 0, v___x_5243_);
v___x_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5244_);
v___x_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5246_, 0, v___x_5245_);
v___x_5247_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5241_, v___x_5242_, v___x_5246_, v___f_5238_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5248_, lean_object* v___f_5249_, lean_object* v_receiver_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5248_, v___f_5249_, v_receiver_5250_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5256_){
_start:
{
lean_object* v___f_5257_; lean_object* v___f_5258_; 
v___f_5257_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5258_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5258_, 0, v_inst_5256_);
lean_closure_set(v___f_5258_, 1, v___f_5257_);
return v___f_5258_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5259_, lean_object* v_inst_5260_){
_start:
{
lean_object* v___x_5261_; 
v___x_5261_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5260_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v_a_5262_){
_start:
{
lean_object* v___x_5263_; 
v___x_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5263_, 0, v_a_5262_);
return v___x_5263_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v___f_5264_, lean_object* v_x_5265_){
_start:
{
if (lean_obj_tag(v_x_5265_) == 0)
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5275_; 
lean_dec_ref(v___f_5264_);
v_a_5267_ = lean_ctor_get(v_x_5265_, 0);
v_isSharedCheck_5275_ = !lean_is_exclusive(v_x_5265_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5269_ = v_x_5265_;
v_isShared_5270_ = v_isSharedCheck_5275_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v_x_5265_);
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
v_a_5276_ = lean_ctor_get(v_x_5265_, 0);
lean_inc(v_a_5276_);
lean_dec_ref_known(v_x_5265_, 1);
v___x_5277_ = lean_unsigned_to_nat(0u);
v___x_5278_ = 0;
v___x_5279_ = lean_task_map(v___f_5264_, v_a_5276_, v___x_5277_, v___x_5278_);
v___x_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5279_);
return v___x_5280_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5281_, lean_object* v_x_5282_, lean_object* v___y_5283_){
_start:
{
lean_object* v_res_5284_; 
v_res_5284_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_5281_, v_x_5282_);
return v_res_5284_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v___f_5285_, lean_object* v_receiver_5286_, lean_object* v_x_5287_){
_start:
{
lean_object* v___x_5289_; uint8_t v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5289_ = lean_unsigned_to_nat(0u);
v___x_5290_ = 0;
v___x_5291_ = l_Std_Channel_send___redArg(v_receiver_5286_, v_x_5287_);
v___x_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5291_);
v___x_5293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
v___x_5294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5289_, v___x_5290_, v___x_5293_, v___f_5285_);
return v___x_5294_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5295_, lean_object* v_receiver_5296_, lean_object* v_x_5297_, lean_object* v___y_5298_){
_start:
{
lean_object* v_res_5299_; 
v_res_5299_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(v___f_5295_, v_receiver_5296_, v_x_5297_);
return v_res_5299_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_5305_; lean_object* v___f_5306_; lean_object* v___f_5307_; 
v___x_5305_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5306_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5307_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5307_, 0, v___f_5306_);
lean_closure_set(v___f_5307_, 1, v___x_5305_);
return v___f_5307_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___f_5308_; lean_object* v___f_5309_; lean_object* v___f_5310_; lean_object* v___x_5311_; 
v___f_5308_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5309_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5310_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2));
v___x_5311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5311_, 0, v___f_5310_);
lean_ctor_set(v___x_5311_, 1, v___f_5309_);
lean_ctor_set(v___x_5311_, 2, v___f_5308_);
return v___x_5311_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_5313_; 
v___x_5313_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg();
return v_res_5315_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5316_; 
v___x_5316_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg();
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5317_, lean_object* v_inst_5318_){
_start:
{
lean_object* v___x_5319_; 
v___x_5319_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__0, &l_Std_Channel_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__0);
return v___x_5319_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5320_, lean_object* v_inst_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_5320_, v_inst_5321_);
lean_dec(v_inst_5321_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object* v_ch_5323_){
_start:
{
lean_inc_ref(v_ch_5323_);
return v_ch_5323_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object* v_ch_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l_Std_Channel_sync___redArg(v_ch_5324_);
lean_dec_ref(v_ch_5324_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object* v_00_u03b1_5326_, lean_object* v_ch_5327_){
_start:
{
lean_inc_ref(v_ch_5327_);
return v_ch_5327_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object* v_00_u03b1_5328_, lean_object* v_ch_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l_Std_Channel_sync(v_00_u03b1_5328_, v_ch_5329_);
lean_dec_ref(v_ch_5329_);
return v_res_5330_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg(lean_object* v_capacity_5331_){
_start:
{
lean_object* v___x_5333_; 
v___x_5333_ = l_Std_CloseableChannel_new___redArg(v_capacity_5331_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object* v_capacity_5334_, lean_object* v_a_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_Std_Channel_Sync_new___redArg(v_capacity_5334_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new(lean_object* v_00_u03b1_5337_, lean_object* v_capacity_5338_){
_start:
{
lean_object* v___x_5340_; 
v___x_5340_ = l_Std_CloseableChannel_new___redArg(v_capacity_5338_);
return v___x_5340_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object* v_00_u03b1_5341_, lean_object* v_capacity_5342_, lean_object* v_a_5343_){
_start:
{
lean_object* v_res_5344_; 
v_res_5344_ = l_Std_Channel_Sync_new(v_00_u03b1_5341_, v_capacity_5342_);
return v_res_5344_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object* v_ch_5345_, lean_object* v_v_5346_){
_start:
{
uint8_t v___x_5348_; 
v___x_5348_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5345_, v_v_5346_);
return v___x_5348_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object* v_ch_5349_, lean_object* v_v_5350_, lean_object* v_a_5351_){
_start:
{
uint8_t v_res_5352_; lean_object* v_r_5353_; 
v_res_5352_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5349_, v_v_5350_);
v_r_5353_ = lean_box(v_res_5352_);
return v_r_5353_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend(lean_object* v_00_u03b1_5354_, lean_object* v_ch_5355_, lean_object* v_v_5356_){
_start:
{
uint8_t v___x_5358_; 
v___x_5358_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5355_, v_v_5356_);
return v___x_5358_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object* v_00_u03b1_5359_, lean_object* v_ch_5360_, lean_object* v_v_5361_, lean_object* v_a_5362_){
_start:
{
uint8_t v_res_5363_; lean_object* v_r_5364_; 
v_res_5363_ = l_Std_Channel_Sync_trySend(v_00_u03b1_5359_, v_ch_5360_, v_v_5361_);
v_r_5364_ = lean_box(v_res_5363_);
return v_r_5364_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg(lean_object* v_ch_5365_, lean_object* v_v_5366_){
_start:
{
lean_object* v___x_5368_; lean_object* v___x_5369_; 
v___x_5368_ = l_Std_Channel_send___redArg(v_ch_5365_, v_v_5366_);
v___x_5369_ = lean_io_wait(v___x_5368_);
return v___x_5369_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object* v_ch_5370_, lean_object* v_v_5371_, lean_object* v_a_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_Std_Channel_Sync_send___redArg(v_ch_5370_, v_v_5371_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send(lean_object* v_00_u03b1_5374_, lean_object* v_ch_5375_, lean_object* v_v_5376_){
_start:
{
lean_object* v___x_5378_; 
v___x_5378_ = l_Std_Channel_Sync_send___redArg(v_ch_5375_, v_v_5376_);
return v___x_5378_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object* v_00_u03b1_5379_, lean_object* v_ch_5380_, lean_object* v_v_5381_, lean_object* v_a_5382_){
_start:
{
lean_object* v_res_5383_; 
v_res_5383_ = l_Std_Channel_Sync_send(v_00_u03b1_5379_, v_ch_5380_, v_v_5381_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object* v_ch_5384_){
_start:
{
lean_object* v___x_5386_; 
v___x_5386_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5384_);
return v___x_5386_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5387_, lean_object* v_a_5388_){
_start:
{
lean_object* v_res_5389_; 
v_res_5389_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5387_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv(lean_object* v_00_u03b1_5390_, lean_object* v_ch_5391_){
_start:
{
lean_object* v___x_5393_; 
v___x_5393_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5391_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5394_, lean_object* v_ch_5395_, lean_object* v_a_5396_){
_start:
{
lean_object* v_res_5397_; 
v_res_5397_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_5394_, v_ch_5395_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg(lean_object* v_inst_5398_, lean_object* v_ch_5399_){
_start:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5401_ = l_Std_Channel_recv___redArg(v_inst_5398_, v_ch_5399_);
v___x_5402_ = lean_io_wait(v___x_5401_);
return v___x_5402_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object* v_inst_5403_, lean_object* v_ch_5404_, lean_object* v_a_5405_){
_start:
{
lean_object* v_res_5406_; 
v_res_5406_ = l_Std_Channel_Sync_recv___redArg(v_inst_5403_, v_ch_5404_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv(lean_object* v_00_u03b1_5407_, lean_object* v_inst_5408_, lean_object* v_ch_5409_){
_start:
{
lean_object* v___x_5411_; 
v___x_5411_ = l_Std_Channel_Sync_recv___redArg(v_inst_5408_, v_ch_5409_);
return v___x_5411_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object* v_00_u03b1_5412_, lean_object* v_inst_5413_, lean_object* v_ch_5414_, lean_object* v_a_5415_){
_start:
{
lean_object* v_res_5416_; 
v_res_5416_ = l_Std_Channel_Sync_recv(v_00_u03b1_5412_, v_inst_5413_, v_ch_5414_);
return v_res_5416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object* v_f_5417_, lean_object* v_b_5418_, lean_object* v_toBind_5419_, lean_object* v___f_5420_, lean_object* v_a_5421_){
_start:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; 
v___x_5422_ = lean_apply_2(v_f_5417_, v_a_5421_, v_b_5418_);
v___x_5423_ = lean_apply_4(v_toBind_5419_, lean_box(0), lean_box(0), v___x_5422_, v___f_5420_);
return v___x_5423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object* v_inst_5424_, lean_object* v_inst_5425_, lean_object* v_inst_5426_, lean_object* v_ch_5427_, lean_object* v_f_5428_, lean_object* v_b_5429_){
_start:
{
lean_object* v_toApplicative_5430_; lean_object* v_toBind_5431_; lean_object* v_toPure_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___f_5435_; lean_object* v___f_5436_; lean_object* v___x_5437_; 
v_toApplicative_5430_ = lean_ctor_get(v_inst_5425_, 0);
v_toBind_5431_ = lean_ctor_get(v_inst_5425_, 1);
lean_inc_n(v_toBind_5431_, 2);
v_toPure_5432_ = lean_ctor_get(v_toApplicative_5430_, 1);
lean_inc(v_toPure_5432_);
lean_inc_ref(v_ch_5427_);
lean_inc(v_inst_5424_);
v___x_5433_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_recv___boxed), 4, 3);
lean_closure_set(v___x_5433_, 0, lean_box(0));
lean_closure_set(v___x_5433_, 1, v_inst_5424_);
lean_closure_set(v___x_5433_, 2, v_ch_5427_);
lean_inc(v_inst_5426_);
v___x_5434_ = lean_apply_2(v_inst_5426_, lean_box(0), v___x_5433_);
lean_inc(v_f_5428_);
v___f_5435_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5435_, 0, v_toPure_5432_);
lean_closure_set(v___f_5435_, 1, v_inst_5424_);
lean_closure_set(v___f_5435_, 2, v_inst_5425_);
lean_closure_set(v___f_5435_, 3, v_inst_5426_);
lean_closure_set(v___f_5435_, 4, v_ch_5427_);
lean_closure_set(v___f_5435_, 5, v_f_5428_);
v___f_5436_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1), 5, 4);
lean_closure_set(v___f_5436_, 0, v_f_5428_);
lean_closure_set(v___f_5436_, 1, v_b_5429_);
lean_closure_set(v___f_5436_, 2, v_toBind_5431_);
lean_closure_set(v___f_5436_, 3, v___f_5435_);
v___x_5437_ = lean_apply_4(v_toBind_5431_, lean_box(0), lean_box(0), v___x_5434_, v___f_5436_);
return v___x_5437_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5438_, lean_object* v_inst_5439_, lean_object* v_inst_5440_, lean_object* v_inst_5441_, lean_object* v_ch_5442_, lean_object* v_f_5443_, lean_object* v_____do__lift_5444_){
_start:
{
if (lean_obj_tag(v_____do__lift_5444_) == 0)
{
lean_object* v_a_5445_; lean_object* v___x_5446_; 
lean_dec(v_f_5443_);
lean_dec_ref(v_ch_5442_);
lean_dec(v_inst_5441_);
lean_dec_ref(v_inst_5440_);
lean_dec(v_inst_5439_);
v_a_5445_ = lean_ctor_get(v_____do__lift_5444_, 0);
lean_inc(v_a_5445_);
lean_dec_ref_known(v_____do__lift_5444_, 1);
v___x_5446_ = lean_apply_2(v_toPure_5438_, lean_box(0), v_a_5445_);
return v___x_5446_;
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5448_; 
lean_dec(v_toPure_5438_);
v_a_5447_ = lean_ctor_get(v_____do__lift_5444_, 0);
lean_inc(v_a_5447_);
lean_dec_ref_known(v_____do__lift_5444_, 1);
v___x_5448_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5439_, v_inst_5440_, v_inst_5441_, v_ch_5442_, v_f_5443_, v_a_5447_);
return v___x_5448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object* v_00_u03b1_5449_, lean_object* v_m_5450_, lean_object* v_00_u03b2_5451_, lean_object* v_inst_5452_, lean_object* v_inst_5453_, lean_object* v_inst_5454_, lean_object* v_ch_5455_, lean_object* v_f_5456_, lean_object* v_b_5457_){
_start:
{
lean_object* v___x_5458_; 
v___x_5458_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5452_, v_inst_5453_, v_inst_5454_, v_ch_5455_, v_f_5456_, v_b_5457_);
return v___x_5458_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5459_, lean_object* v_inst_5460_, lean_object* v_inst_5461_, lean_object* v_ch_5462_, lean_object* v_b_5463_, lean_object* v_f_5464_){
_start:
{
lean_object* v___x_5465_; 
v___x_5465_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5459_, v_inst_5460_, v_inst_5461_, v_ch_5462_, v_f_5464_, v_b_5463_);
return v___x_5465_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_00_u03b1_5466_, lean_object* v_m_5467_, lean_object* v_inst_5468_, lean_object* v_inst_5469_, lean_object* v_inst_5470_, lean_object* v_00_u03b2_5471_, lean_object* v_ch_5472_, lean_object* v_b_5473_, lean_object* v_f_5474_){
_start:
{
lean_object* v___x_5475_; 
v___x_5475_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5468_, v_inst_5469_, v_inst_5470_, v_ch_5472_, v_f_5474_, v_b_5473_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5476_, lean_object* v_inst_5477_, lean_object* v_inst_5478_, lean_object* v_00_u03b2_5479_, lean_object* v_ch_5480_, lean_object* v_b_5481_, lean_object* v_f_5482_){
_start:
{
lean_object* v___x_5483_; 
v___x_5483_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5476_, v_inst_5477_, v_inst_5478_, v_ch_5480_, v_f_5482_, v_b_5481_);
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5484_, lean_object* v_inst_5485_, lean_object* v_inst_5486_){
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
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5488_, lean_object* v_m_5489_, lean_object* v_inst_5490_, lean_object* v_inst_5491_, lean_object* v_inst_5492_){
_start:
{
lean_object* v___f_5493_; 
v___f_5493_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5493_, 0, v_inst_5490_);
lean_closure_set(v___f_5493_, 1, v_inst_5491_);
lean_closure_set(v___f_5493_, 2, v_inst_5492_);
return v___f_5493_;
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

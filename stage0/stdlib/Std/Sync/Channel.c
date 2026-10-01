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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(uint8_t v___x_2842_, lean_object* v_as_2843_, size_t v_sz_2844_, size_t v_i_2845_, lean_object* v_b_2846_){
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
lean_object* v___x_2850_; lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; size_t v___x_2854_; size_t v___x_2855_; 
v___x_2850_ = lean_box(0);
v_a_2851_ = lean_array_uget_borrowed(v_as_2843_, v_i_2845_);
v___x_2852_ = lean_box(v___x_2842_);
v___x_2853_ = lean_io_promise_resolve(v___x_2852_, v_a_2851_);
v___x_2854_ = ((size_t)1ULL);
v___x_2855_ = lean_usize_add(v_i_2845_, v___x_2854_);
v_i_2845_ = v___x_2855_;
v_b_2846_ = v___x_2850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg___boxed(lean_object* v___x_2857_, lean_object* v_as_2858_, lean_object* v_sz_2859_, lean_object* v_i_2860_, lean_object* v_b_2861_, lean_object* v___y_2862_){
_start:
{
uint8_t v___x_1818__boxed_2863_; size_t v_sz_boxed_2864_; size_t v_i_boxed_2865_; lean_object* v_res_2866_; 
v___x_1818__boxed_2863_ = lean_unbox(v___x_2857_);
v_sz_boxed_2864_ = lean_unbox_usize(v_sz_2859_);
lean_dec(v_sz_2859_);
v_i_boxed_2865_ = lean_unbox_usize(v_i_2860_);
lean_dec(v_i_2860_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v___x_1818__boxed_2863_, v_as_2858_, v_sz_boxed_2864_, v_i_boxed_2865_, v_b_2861_);
lean_dec_ref(v_as_2858_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t v___x_2867_, lean_object* v_as_2868_, size_t v_sz_2869_, size_t v_i_2870_, lean_object* v_b_2871_){
_start:
{
uint8_t v___x_2873_; 
v___x_2873_ = lean_usize_dec_lt(v_i_2870_, v_sz_2869_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v_b_2871_);
return v___x_2874_;
}
else
{
lean_object* v___x_2875_; lean_object* v_a_2876_; lean_object* v___x_2877_; size_t v___x_2878_; size_t v___x_2879_; 
v___x_2875_ = lean_box(0);
v_a_2876_ = lean_array_uget_borrowed(v_as_2868_, v_i_2870_);
v___x_2877_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_2876_, v___x_2867_);
v___x_2878_ = ((size_t)1ULL);
v___x_2879_ = lean_usize_add(v_i_2870_, v___x_2878_);
v_i_2870_ = v___x_2879_;
v_b_2871_ = v___x_2875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_2881_, lean_object* v_as_2882_, lean_object* v_sz_2883_, lean_object* v_i_2884_, lean_object* v_b_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v___x_1840__boxed_2887_; size_t v_sz_boxed_2888_; size_t v_i_boxed_2889_; lean_object* v_res_2890_; 
v___x_1840__boxed_2887_ = lean_unbox(v___x_2881_);
v_sz_boxed_2888_ = lean_unbox_usize(v_sz_2883_);
lean_dec(v_sz_2883_);
v_i_boxed_2889_ = lean_unbox_usize(v_i_2884_);
lean_dec(v_i_2884_);
v_res_2890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1840__boxed_2887_, v_as_2882_, v_sz_boxed_2888_, v_i_boxed_2889_, v_b_2885_);
lean_dec_ref(v_as_2882_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_2891_){
_start:
{
lean_object* v___x_2893_; uint8_t v_closed_2894_; 
v___x_2893_ = lean_st_ref_get(v___y_2891_);
v_closed_2894_ = lean_ctor_get_uint8(v___x_2893_, sizeof(void*)*7);
if (v_closed_2894_ == 0)
{
lean_object* v_producers_2895_; lean_object* v_consumers_2896_; lean_object* v_capacity_2897_; lean_object* v_buf_2898_; lean_object* v_bufCount_2899_; lean_object* v_sendIdx_2900_; lean_object* v_recvIdx_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2927_; 
v_producers_2895_ = lean_ctor_get(v___x_2893_, 0);
v_consumers_2896_ = lean_ctor_get(v___x_2893_, 1);
v_capacity_2897_ = lean_ctor_get(v___x_2893_, 2);
v_buf_2898_ = lean_ctor_get(v___x_2893_, 3);
v_bufCount_2899_ = lean_ctor_get(v___x_2893_, 4);
v_sendIdx_2900_ = lean_ctor_get(v___x_2893_, 5);
v_recvIdx_2901_ = lean_ctor_get(v___x_2893_, 6);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2903_ = v___x_2893_;
v_isShared_2904_ = v_isSharedCheck_2927_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_recvIdx_2901_);
lean_inc(v_sendIdx_2900_);
lean_inc(v_bufCount_2899_);
lean_inc(v_buf_2898_);
lean_inc(v_capacity_2897_);
lean_inc(v_consumers_2896_);
lean_inc(v_producers_2895_);
lean_dec(v___x_2893_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2927_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; size_t v_sz_2907_; size_t v___x_2908_; lean_object* v___x_2909_; 
v___x_2905_ = l_Std_Queue_toArray___redArg(v_consumers_2896_);
v___x_2906_ = lean_box(0);
v_sz_2907_ = lean_array_size(v___x_2905_);
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_2894_, v___x_2905_, v_sz_2907_, v___x_2908_, v___x_2906_);
lean_dec_ref(v___x_2905_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v___x_2910_; size_t v_sz_2911_; lean_object* v___x_2912_; 
lean_dec_ref_known(v___x_2909_, 1);
v___x_2910_ = l_Std_Queue_toArray___redArg(v_producers_2895_);
v_sz_2911_ = lean_array_size(v___x_2910_);
v___x_2912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v_closed_2894_, v___x_2910_, v_sz_2911_, v___x_2908_, v___x_2906_);
lean_dec_ref(v___x_2910_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2925_; 
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; 
v_unused_2926_ = lean_ctor_get(v___x_2912_, 0);
lean_dec(v_unused_2926_);
v___x_2914_ = v___x_2912_;
v_isShared_2915_ = v_isSharedCheck_2925_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v___x_2912_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2925_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; uint8_t v___x_2917_; lean_object* v___x_2919_; 
v___x_2916_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2917_ = 1;
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 1, v___x_2916_);
lean_ctor_set(v___x_2903_, 0, v___x_2916_);
v___x_2919_ = v___x_2903_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2924_, 2, v_capacity_2897_);
lean_ctor_set(v_reuseFailAlloc_2924_, 3, v_buf_2898_);
lean_ctor_set(v_reuseFailAlloc_2924_, 4, v_bufCount_2899_);
lean_ctor_set(v_reuseFailAlloc_2924_, 5, v_sendIdx_2900_);
lean_ctor_set(v_reuseFailAlloc_2924_, 6, v_recvIdx_2901_);
v___x_2919_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2922_; 
lean_ctor_set_uint8(v___x_2919_, sizeof(void*)*7, v___x_2917_);
v___x_2920_ = lean_st_ref_swap(v___y_2891_, v___x_2919_);
lean_dec(v___x_2920_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2906_);
v___x_2922_ = v___x_2914_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2906_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_del_object(v___x_2903_);
lean_dec(v_recvIdx_2901_);
lean_dec(v_sendIdx_2900_);
lean_dec(v_bufCount_2899_);
lean_dec_ref(v_buf_2898_);
lean_dec(v_capacity_2897_);
return v___x_2912_;
}
}
else
{
lean_del_object(v___x_2903_);
lean_dec(v_recvIdx_2901_);
lean_dec(v_sendIdx_2900_);
lean_dec(v_bufCount_2899_);
lean_dec_ref(v_buf_2898_);
lean_dec(v_capacity_2897_);
lean_dec_ref(v_producers_2895_);
return v___x_2909_;
}
}
}
else
{
uint8_t v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec(v___x_2893_);
v___x_2928_ = 1;
v___x_2929_ = lean_box(v___x_2928_);
v___x_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_2931_);
lean_dec(v___y_2931_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_2935_){
_start:
{
lean_object* v___f_2937_; lean_object* v___x_2938_; 
v___f_2937_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_2938_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_2935_, v___f_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2939_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_2942_, lean_object* v_ch_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2943_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_2946_, lean_object* v_ch_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_2946_, v_ch_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_2950_, uint8_t v___x_2951_, lean_object* v_as_2952_, size_t v_sz_2953_, size_t v_i_2954_, lean_object* v_b_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_2951_, v_as_2952_, v_sz_2953_, v_i_2954_, v_b_2955_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_2959_, lean_object* v___x_2960_, lean_object* v_as_2961_, lean_object* v_sz_2962_, lean_object* v_i_2963_, lean_object* v_b_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
uint8_t v___x_1942__boxed_2967_; size_t v_sz_boxed_2968_; size_t v_i_boxed_2969_; lean_object* v_res_2970_; 
v___x_1942__boxed_2967_ = lean_unbox(v___x_2960_);
v_sz_boxed_2968_ = lean_unbox_usize(v_sz_2962_);
lean_dec(v_sz_2962_);
v_i_boxed_2969_ = lean_unbox_usize(v_i_2963_);
lean_dec(v_i_2963_);
v_res_2970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_2959_, v___x_1942__boxed_2967_, v_as_2961_, v_sz_boxed_2968_, v_i_boxed_2969_, v_b_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v_as_2961_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1(lean_object* v_00_u03b1_2971_, uint8_t v___x_2972_, lean_object* v_as_2973_, size_t v_sz_2974_, size_t v_i_2975_, lean_object* v_b_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v___x_2972_, v_as_2973_, v_sz_2974_, v_i_2975_, v_b_2976_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_2980_, lean_object* v___x_2981_, lean_object* v_as_2982_, lean_object* v_sz_2983_, lean_object* v_i_2984_, lean_object* v_b_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
uint8_t v___x_1953__boxed_2988_; size_t v_sz_boxed_2989_; size_t v_i_boxed_2990_; lean_object* v_res_2991_; 
v___x_1953__boxed_2988_ = lean_unbox(v___x_2981_);
v_sz_boxed_2989_ = lean_unbox_usize(v_sz_2983_);
lean_dec(v_sz_2983_);
v_i_boxed_2990_ = lean_unbox_usize(v_i_2984_);
lean_dec(v_i_2984_);
v_res_2991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1(v_00_u03b1_2980_, v___x_1953__boxed_2988_, v_as_2982_, v_sz_boxed_2989_, v_i_boxed_2990_, v_b_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v_as_2982_);
return v_res_2991_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_2992_){
_start:
{
lean_object* v___x_2994_; uint8_t v_closed_2995_; 
v___x_2994_ = lean_st_ref_get(v___y_2992_);
v_closed_2995_ = lean_ctor_get_uint8(v___x_2994_, sizeof(void*)*7);
lean_dec(v___x_2994_);
return v_closed_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v_res_2998_; lean_object* v_r_2999_; 
v_res_2998_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_2996_);
lean_dec(v___y_2996_);
v_r_2999_ = lean_box(v_res_2998_);
return v_r_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_3001_){
_start:
{
lean_object* v___f_3003_; lean_object* v___x_3004_; 
v___f_3003_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_3004_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3001_, v___f_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_3008_, lean_object* v_ch_3009_){
_start:
{
lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3009_);
v___x_3012_ = lean_unbox(v___x_3011_);
lean_dec(v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_3013_, lean_object* v_ch_3014_, lean_object* v_a_3015_){
_start:
{
uint8_t v_res_3016_; lean_object* v_r_3017_; 
v_res_3016_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_3013_, v_ch_3014_);
v_r_3017_ = lean_box(v_res_3016_);
return v_r_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v_toPure_3021_; lean_object* v___x_3022_; 
v_toPure_3021_ = lean_ctor_get(v_toApplicative_3018_, 1);
lean_inc(v_toPure_3021_);
lean_dec_ref(v_toApplicative_3018_);
v___x_3022_ = lean_apply_2(v_toPure_3021_, lean_box(0), v_a_3019_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_3023_, lean_object* v_toBind_3024_, lean_object* v___f_3025_, lean_object* v_____r_3026_, lean_object* v_st_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_inc(v___y_3028_);
v___x_3029_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_3029_, 0, lean_box(0));
lean_closure_set(v___x_3029_, 1, lean_box(0));
lean_closure_set(v___x_3029_, 2, v___y_3028_);
lean_closure_set(v___x_3029_, 3, v_st_3027_);
v___x_3030_ = lean_apply_2(v_inst_3023_, lean_box(0), v___x_3029_);
v___x_3031_ = lean_apply_4(v_toBind_3024_, lean_box(0), lean_box(0), v___x_3030_, v___f_3025_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_inst_3032_, lean_object* v_toBind_3033_, lean_object* v___f_3034_, lean_object* v_____r_3035_, lean_object* v_st_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3032_, v_toBind_3033_, v___f_3034_, v_____r_3035_, v_st_3036_, v___y_3037_);
lean_dec(v___y_3037_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_3039_, lean_object* v_consumers_3040_, lean_object* v_capacity_3041_, lean_object* v_buf_3042_, lean_object* v___x_3043_, lean_object* v_sendIdx_3044_, lean_object* v___y_3045_, uint8_t v_closed_3046_, lean_object* v___f_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3050_, 0, v_snd_3039_);
lean_ctor_set(v___x_3050_, 1, v_consumers_3040_);
lean_ctor_set(v___x_3050_, 2, v_capacity_3041_);
lean_ctor_set(v___x_3050_, 3, v_buf_3042_);
lean_ctor_set(v___x_3050_, 4, v___x_3043_);
lean_ctor_set(v___x_3050_, 5, v_sendIdx_3044_);
lean_ctor_set(v___x_3050_, 6, v___y_3045_);
lean_ctor_set_uint8(v___x_3050_, sizeof(void*)*7, v_closed_3046_);
v___x_3051_ = lean_box(0);
lean_inc(v_a_3048_);
v___x_3052_ = lean_apply_3(v___f_3047_, v___x_3051_, v___x_3050_, v_a_3048_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_3053_, lean_object* v_consumers_3054_, lean_object* v_capacity_3055_, lean_object* v_buf_3056_, lean_object* v___x_3057_, lean_object* v_sendIdx_3058_, lean_object* v___y_3059_, lean_object* v_closed_3060_, lean_object* v___f_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
uint8_t v_closed_boxed_3064_; lean_object* v_res_3065_; 
v_closed_boxed_3064_ = lean_unbox(v_closed_3060_);
v_res_3065_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3053_, v_consumers_3054_, v_capacity_3055_, v_buf_3056_, v___x_3057_, v_sendIdx_3058_, v___y_3059_, v_closed_boxed_3064_, v___f_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3062_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3066_, lean_object* v_inst_3067_, lean_object* v_toBind_3068_, lean_object* v_bufCount_3069_, lean_object* v_producers_3070_, lean_object* v_consumers_3071_, lean_object* v_capacity_3072_, lean_object* v_buf_3073_, lean_object* v_sendIdx_3074_, uint8_t v_closed_3075_, lean_object* v_a_3076_, uint8_t v___x_3077_, lean_object* v_inst_3078_, lean_object* v_recvIdx_3079_, lean_object* v___x_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___f_3082_; lean_object* v___f_3083_; lean_object* v___y_3085_; lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___f_3082_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3082_, 0, v_toApplicative_3066_);
lean_closure_set(v___f_3082_, 1, v_a_3081_);
lean_inc_ref(v___f_3082_);
lean_inc(v_toBind_3068_);
lean_inc(v_inst_3067_);
v___f_3083_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3083_, 0, v_inst_3067_);
lean_closure_set(v___f_3083_, 1, v_toBind_3068_);
lean_closure_set(v___f_3083_, 2, v___f_3082_);
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_add(v_recvIdx_3079_, v___x_3101_);
v___x_3103_ = lean_nat_dec_eq(v___x_3102_, v_capacity_3072_);
if (v___x_3103_ == 0)
{
lean_dec(v___x_3080_);
v___y_3085_ = v___x_3102_;
goto v___jp_3084_;
}
else
{
lean_dec(v___x_3102_);
v___y_3085_ = v___x_3080_;
goto v___jp_3084_;
}
v___jp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3086_ = lean_unsigned_to_nat(1u);
v___x_3087_ = lean_nat_sub(v_bufCount_3069_, v___x_3086_);
lean_inc(v___y_3085_);
lean_inc(v_sendIdx_3074_);
lean_inc(v___x_3087_);
lean_inc_ref(v_buf_3073_);
lean_inc(v_capacity_3072_);
lean_inc_ref(v_consumers_3071_);
lean_inc_ref(v_producers_3070_);
v___x_3088_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3088_, 0, v_producers_3070_);
lean_ctor_set(v___x_3088_, 1, v_consumers_3071_);
lean_ctor_set(v___x_3088_, 2, v_capacity_3072_);
lean_ctor_set(v___x_3088_, 3, v_buf_3073_);
lean_ctor_set(v___x_3088_, 4, v___x_3087_);
lean_ctor_set(v___x_3088_, 5, v_sendIdx_3074_);
lean_ctor_set(v___x_3088_, 6, v___y_3085_);
lean_ctor_set_uint8(v___x_3088_, sizeof(void*)*7, v_closed_3075_);
v___x_3089_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3070_);
if (lean_obj_tag(v___x_3089_) == 1)
{
lean_object* v_val_3090_; lean_object* v_fst_3091_; lean_object* v_snd_3092_; lean_object* v___x_3093_; lean_object* v___f_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
lean_dec_ref_known(v___x_3088_, 7);
lean_dec_ref(v___f_3082_);
lean_dec(v_inst_3067_);
v_val_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_val_3090_);
lean_dec_ref_known(v___x_3089_, 1);
v_fst_3091_ = lean_ctor_get(v_val_3090_, 0);
lean_inc(v_fst_3091_);
v_snd_3092_ = lean_ctor_get(v_val_3090_, 1);
lean_inc(v_snd_3092_);
lean_dec(v_val_3090_);
v___x_3093_ = lean_box(v_closed_3075_);
lean_inc(v_a_3076_);
v___f_3094_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3094_, 0, v_snd_3092_);
lean_closure_set(v___f_3094_, 1, v_consumers_3071_);
lean_closure_set(v___f_3094_, 2, v_capacity_3072_);
lean_closure_set(v___f_3094_, 3, v_buf_3073_);
lean_closure_set(v___f_3094_, 4, v___x_3087_);
lean_closure_set(v___f_3094_, 5, v_sendIdx_3074_);
lean_closure_set(v___f_3094_, 6, v___y_3085_);
lean_closure_set(v___f_3094_, 7, v___x_3093_);
lean_closure_set(v___f_3094_, 8, v___f_3083_);
lean_closure_set(v___f_3094_, 9, v_a_3076_);
v___x_3095_ = lean_box(v___x_3077_);
v___x_3096_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3096_, 0, lean_box(0));
lean_closure_set(v___x_3096_, 1, v___x_3095_);
lean_closure_set(v___x_3096_, 2, v_fst_3091_);
v___x_3097_ = lean_apply_2(v_inst_3078_, lean_box(0), v___x_3096_);
v___x_3098_ = lean_apply_4(v_toBind_3068_, lean_box(0), lean_box(0), v___x_3097_, v___f_3094_);
return v___x_3098_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_dec(v___x_3089_);
lean_dec(v___x_3087_);
lean_dec(v___y_3085_);
lean_dec_ref(v___f_3083_);
lean_dec(v_inst_3078_);
lean_dec(v_sendIdx_3074_);
lean_dec_ref(v_buf_3073_);
lean_dec(v_capacity_3072_);
lean_dec_ref(v_consumers_3071_);
v___x_3099_ = lean_box(0);
v___x_3100_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3067_, v_toBind_3068_, v___f_3082_, v___x_3099_, v___x_3088_, v_a_3076_);
return v___x_3100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3104_, lean_object* v_inst_3105_, lean_object* v_toBind_3106_, lean_object* v_bufCount_3107_, lean_object* v_producers_3108_, lean_object* v_consumers_3109_, lean_object* v_capacity_3110_, lean_object* v_buf_3111_, lean_object* v_sendIdx_3112_, lean_object* v_closed_3113_, lean_object* v_a_3114_, lean_object* v___x_3115_, lean_object* v_inst_3116_, lean_object* v_recvIdx_3117_, lean_object* v___x_3118_, lean_object* v_a_3119_){
_start:
{
uint8_t v_closed_boxed_3120_; uint8_t v___x_543__boxed_3121_; lean_object* v_res_3122_; 
v_closed_boxed_3120_ = lean_unbox(v_closed_3113_);
v___x_543__boxed_3121_ = lean_unbox(v___x_3115_);
v_res_3122_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3104_, v_inst_3105_, v_toBind_3106_, v_bufCount_3107_, v_producers_3108_, v_consumers_3109_, v_capacity_3110_, v_buf_3111_, v_sendIdx_3112_, v_closed_boxed_3120_, v_a_3114_, v___x_543__boxed_3121_, v_inst_3116_, v_recvIdx_3117_, v___x_3118_, v_a_3119_);
lean_dec(v_recvIdx_3117_);
lean_dec(v_a_3114_);
lean_dec(v_bufCount_3107_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3123_, lean_object* v_inst_3124_, lean_object* v_toBind_3125_, lean_object* v_a_3126_, lean_object* v_inst_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_producers_3129_; lean_object* v_consumers_3130_; lean_object* v_capacity_3131_; lean_object* v_buf_3132_; lean_object* v_bufCount_3133_; lean_object* v_sendIdx_3134_; lean_object* v_recvIdx_3135_; uint8_t v_closed_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
v_producers_3129_ = lean_ctor_get(v_a_3128_, 0);
lean_inc_ref(v_producers_3129_);
v_consumers_3130_ = lean_ctor_get(v_a_3128_, 1);
lean_inc_ref(v_consumers_3130_);
v_capacity_3131_ = lean_ctor_get(v_a_3128_, 2);
lean_inc(v_capacity_3131_);
v_buf_3132_ = lean_ctor_get(v_a_3128_, 3);
lean_inc_ref(v_buf_3132_);
v_bufCount_3133_ = lean_ctor_get(v_a_3128_, 4);
lean_inc(v_bufCount_3133_);
v_sendIdx_3134_ = lean_ctor_get(v_a_3128_, 5);
lean_inc(v_sendIdx_3134_);
v_recvIdx_3135_ = lean_ctor_get(v_a_3128_, 6);
lean_inc(v_recvIdx_3135_);
v_closed_3136_ = lean_ctor_get_uint8(v_a_3128_, sizeof(void*)*7);
lean_dec_ref(v_a_3128_);
v___x_3137_ = lean_unsigned_to_nat(0u);
v___x_3138_ = lean_nat_dec_eq(v_bufCount_3133_, v___x_3137_);
if (v___x_3138_ == 0)
{
uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___f_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3139_ = 1;
v___x_3140_ = lean_box(v_closed_3136_);
v___x_3141_ = lean_box(v___x_3139_);
lean_inc(v_recvIdx_3135_);
lean_inc(v_a_3126_);
lean_inc_ref(v_buf_3132_);
lean_inc(v_toBind_3125_);
lean_inc(v_inst_3124_);
v___f_3142_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3142_, 0, v_toApplicative_3123_);
lean_closure_set(v___f_3142_, 1, v_inst_3124_);
lean_closure_set(v___f_3142_, 2, v_toBind_3125_);
lean_closure_set(v___f_3142_, 3, v_bufCount_3133_);
lean_closure_set(v___f_3142_, 4, v_producers_3129_);
lean_closure_set(v___f_3142_, 5, v_consumers_3130_);
lean_closure_set(v___f_3142_, 6, v_capacity_3131_);
lean_closure_set(v___f_3142_, 7, v_buf_3132_);
lean_closure_set(v___f_3142_, 8, v_sendIdx_3134_);
lean_closure_set(v___f_3142_, 9, v___x_3140_);
lean_closure_set(v___f_3142_, 10, v_a_3126_);
lean_closure_set(v___f_3142_, 11, v___x_3141_);
lean_closure_set(v___f_3142_, 12, v_inst_3127_);
lean_closure_set(v___f_3142_, 13, v_recvIdx_3135_);
lean_closure_set(v___f_3142_, 14, v___x_3137_);
v___x_3143_ = lean_array_fget(v_buf_3132_, v_recvIdx_3135_);
lean_dec(v_recvIdx_3135_);
lean_dec_ref(v_buf_3132_);
v___x_3144_ = lean_box(0);
v___x_3145_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3145_, 0, lean_box(0));
lean_closure_set(v___x_3145_, 1, lean_box(0));
lean_closure_set(v___x_3145_, 2, v___x_3143_);
lean_closure_set(v___x_3145_, 3, v___x_3144_);
v___x_3146_ = lean_apply_2(v_inst_3124_, lean_box(0), v___x_3145_);
v___x_3147_ = lean_apply_4(v_toBind_3125_, lean_box(0), lean_box(0), v___x_3146_, v___f_3142_);
return v___x_3147_;
}
else
{
lean_object* v_toPure_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec(v_recvIdx_3135_);
lean_dec(v_sendIdx_3134_);
lean_dec(v_bufCount_3133_);
lean_dec_ref(v_buf_3132_);
lean_dec(v_capacity_3131_);
lean_dec_ref(v_consumers_3130_);
lean_dec_ref(v_producers_3129_);
lean_dec(v_inst_3127_);
lean_dec(v_toBind_3125_);
lean_dec(v_inst_3124_);
v_toPure_3148_ = lean_ctor_get(v_toApplicative_3123_, 1);
lean_inc(v_toPure_3148_);
lean_dec_ref(v_toApplicative_3123_);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_apply_2(v_toPure_3148_, lean_box(0), v___x_3149_);
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_3151_, lean_object* v_inst_3152_, lean_object* v_toBind_3153_, lean_object* v_a_3154_, lean_object* v_inst_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(v_toApplicative_3151_, v_inst_3152_, v_toBind_3153_, v_a_3154_, v_inst_3155_, v_a_3156_);
lean_dec(v_a_3154_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_inst_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_toApplicative_3162_; lean_object* v_toBind_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_toApplicative_3162_ = lean_ctor_get(v_inst_3158_, 0);
lean_inc_ref(v_toApplicative_3162_);
v_toBind_3163_ = lean_ctor_get(v_inst_3158_, 1);
lean_inc_n(v_toBind_3163_, 2);
lean_dec_ref(v_inst_3158_);
lean_inc_n(v_a_3161_, 2);
lean_inc(v_inst_3159_);
v___f_3164_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_3164_, 0, v_toApplicative_3162_);
lean_closure_set(v___f_3164_, 1, v_inst_3159_);
lean_closure_set(v___f_3164_, 2, v_toBind_3163_);
lean_closure_set(v___f_3164_, 3, v_a_3161_);
lean_closure_set(v___f_3164_, 4, v_inst_3160_);
v___x_3165_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3165_, 0, lean_box(0));
lean_closure_set(v___x_3165_, 1, lean_box(0));
lean_closure_set(v___x_3165_, 2, v_a_3161_);
v___x_3166_ = lean_apply_2(v_inst_3159_, lean_box(0), v___x_3165_);
v___x_3167_ = lean_apply_4(v_toBind_3163_, lean_box(0), lean_box(0), v___x_3166_, v___f_3164_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3168_, v_inst_3169_, v_inst_3170_, v_a_3171_);
lean_dec(v_a_3171_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3173_, lean_object* v_00_u03b1_3174_, lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3175_, v_inst_3176_, v_inst_3177_, v_a_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object* v_m_3180_, lean_object* v_00_u03b1_3181_, lean_object* v_inst_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(v_m_3180_, v_00_u03b1_3181_, v_inst_3182_, v_inst_3183_, v_inst_3184_, v_a_3185_);
lean_dec(v_a_3185_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3189_; lean_object* v_producers_3190_; lean_object* v_consumers_3191_; lean_object* v_capacity_3192_; lean_object* v_buf_3193_; lean_object* v_bufCount_3194_; lean_object* v_sendIdx_3195_; lean_object* v_recvIdx_3196_; uint8_t v_closed_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3229_; 
v___x_3189_ = lean_st_ref_get(v_a_3187_);
v_producers_3190_ = lean_ctor_get(v___x_3189_, 0);
v_consumers_3191_ = lean_ctor_get(v___x_3189_, 1);
v_capacity_3192_ = lean_ctor_get(v___x_3189_, 2);
v_buf_3193_ = lean_ctor_get(v___x_3189_, 3);
v_bufCount_3194_ = lean_ctor_get(v___x_3189_, 4);
v_sendIdx_3195_ = lean_ctor_get(v___x_3189_, 5);
v_recvIdx_3196_ = lean_ctor_get(v___x_3189_, 6);
v_closed_3197_ = lean_ctor_get_uint8(v___x_3189_, sizeof(void*)*7);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3199_ = v___x_3189_;
v_isShared_3200_ = v_isSharedCheck_3229_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_recvIdx_3196_);
lean_inc(v_sendIdx_3195_);
lean_inc(v_bufCount_3194_);
lean_inc(v_buf_3193_);
lean_inc(v_capacity_3192_);
lean_inc(v_consumers_3191_);
lean_inc(v_producers_3190_);
lean_dec(v___x_3189_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3229_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; uint8_t v___x_3202_; 
v___x_3201_ = lean_unsigned_to_nat(0u);
v___x_3202_ = lean_nat_dec_eq(v_bufCount_3194_, v___x_3201_);
if (v___x_3202_ == 0)
{
uint8_t v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v_st_3208_; lean_object* v___y_3209_; lean_object* v___y_3212_; lean_object* v___x_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___x_3203_ = 1;
v___x_3204_ = lean_array_fget_borrowed(v_buf_3193_, v_recvIdx_3196_);
v___x_3205_ = lean_box(0);
v___x_3206_ = lean_st_ref_swap(v___x_3204_, v___x_3205_);
v___x_3225_ = lean_unsigned_to_nat(1u);
v___x_3226_ = lean_nat_add(v_recvIdx_3196_, v___x_3225_);
lean_dec(v_recvIdx_3196_);
v___x_3227_ = lean_nat_dec_eq(v___x_3226_, v_capacity_3192_);
if (v___x_3227_ == 0)
{
v___y_3212_ = v___x_3226_;
goto v___jp_3211_;
}
else
{
lean_dec(v___x_3226_);
v___y_3212_ = v___x_3201_;
goto v___jp_3211_;
}
v___jp_3207_:
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_st_ref_swap(v___y_3209_, v_st_3208_);
lean_dec(v___x_3210_);
return v___x_3206_;
}
v___jp_3211_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_nat_sub(v_bufCount_3194_, v___x_3213_);
lean_dec(v_bufCount_3194_);
lean_inc(v___y_3212_);
lean_inc(v_sendIdx_3195_);
lean_inc(v___x_3214_);
lean_inc_ref(v_buf_3193_);
lean_inc(v_capacity_3192_);
lean_inc_ref(v_consumers_3191_);
lean_inc_ref(v_producers_3190_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 6, v___y_3212_);
lean_ctor_set(v___x_3199_, 4, v___x_3214_);
v___x_3216_ = v___x_3199_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_producers_3190_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_consumers_3191_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_capacity_3192_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_buf_3193_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3224_, 5, v_sendIdx_3195_);
lean_ctor_set(v_reuseFailAlloc_3224_, 6, v___y_3212_);
lean_ctor_set_uint8(v_reuseFailAlloc_3224_, sizeof(void*)*7, v_closed_3197_);
v___x_3216_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3190_);
if (lean_obj_tag(v___x_3217_) == 1)
{
lean_object* v_val_3218_; lean_object* v_fst_3219_; lean_object* v_snd_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec_ref(v___x_3216_);
v_val_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_val_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v_fst_3219_ = lean_ctor_get(v_val_3218_, 0);
lean_inc(v_fst_3219_);
v_snd_3220_ = lean_ctor_get(v_val_3218_, 1);
lean_inc(v_snd_3220_);
lean_dec(v_val_3218_);
v___x_3221_ = lean_box(v___x_3203_);
v___x_3222_ = lean_io_promise_resolve(v___x_3221_, v_fst_3219_);
lean_dec(v_fst_3219_);
v___x_3223_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3223_, 0, v_snd_3220_);
lean_ctor_set(v___x_3223_, 1, v_consumers_3191_);
lean_ctor_set(v___x_3223_, 2, v_capacity_3192_);
lean_ctor_set(v___x_3223_, 3, v_buf_3193_);
lean_ctor_set(v___x_3223_, 4, v___x_3214_);
lean_ctor_set(v___x_3223_, 5, v_sendIdx_3195_);
lean_ctor_set(v___x_3223_, 6, v___y_3212_);
lean_ctor_set_uint8(v___x_3223_, sizeof(void*)*7, v_closed_3197_);
v_st_3208_ = v___x_3223_;
v___y_3209_ = v_a_3187_;
goto v___jp_3207_;
}
else
{
lean_dec(v___x_3217_);
lean_dec(v___x_3214_);
lean_dec(v___y_3212_);
lean_dec(v_sendIdx_3195_);
lean_dec_ref(v_buf_3193_);
lean_dec(v_capacity_3192_);
lean_dec_ref(v_consumers_3191_);
v_st_3208_ = v___x_3216_;
v___y_3209_ = v_a_3187_;
goto v___jp_3207_;
}
}
}
}
else
{
lean_object* v___x_3228_; 
lean_del_object(v___x_3199_);
lean_dec(v_recvIdx_3196_);
lean_dec(v_sendIdx_3195_);
lean_dec(v_bufCount_3194_);
lean_dec_ref(v_buf_3193_);
lean_dec(v_capacity_3192_);
lean_dec_ref(v_consumers_3191_);
lean_dec_ref(v_producers_3190_);
v___x_3228_ = lean_box(0);
return v___x_3228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3230_);
lean_dec(v_a_3230_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3237_, lean_object* v_a_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3237_, v_a_3238_);
lean_dec(v_a_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3242_){
_start:
{
lean_object* v___f_3244_; lean_object* v___x_3245_; 
v___f_3244_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3245_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3242_, v___f_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3246_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3249_, lean_object* v_ch_3250_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3250_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3253_, lean_object* v_ch_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3253_, v_ch_3254_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3258_);
if (lean_obj_tag(v___x_3260_) == 1)
{
lean_object* v___x_3261_; 
lean_dec_ref(v___f_3257_);
v___x_3261_ = lean_task_pure(v___x_3260_);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; uint8_t v_closed_3263_; 
lean_dec(v___x_3260_);
v___x_3262_ = lean_st_ref_get(v___y_3258_);
v_closed_3263_ = lean_ctor_get_uint8(v___x_3262_, sizeof(void*)*7);
lean_dec(v___x_3262_);
if (v_closed_3263_ == 0)
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v_producers_3266_; lean_object* v_consumers_3267_; lean_object* v_capacity_3268_; lean_object* v_buf_3269_; lean_object* v_bufCount_3270_; lean_object* v_sendIdx_3271_; lean_object* v_recvIdx_3272_; uint8_t v_closed_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3287_; 
v___x_3264_ = lean_io_promise_new();
v___x_3265_ = lean_st_ref_take(v___y_3258_);
v_producers_3266_ = lean_ctor_get(v___x_3265_, 0);
v_consumers_3267_ = lean_ctor_get(v___x_3265_, 1);
v_capacity_3268_ = lean_ctor_get(v___x_3265_, 2);
v_buf_3269_ = lean_ctor_get(v___x_3265_, 3);
v_bufCount_3270_ = lean_ctor_get(v___x_3265_, 4);
v_sendIdx_3271_ = lean_ctor_get(v___x_3265_, 5);
v_recvIdx_3272_ = lean_ctor_get(v___x_3265_, 6);
v_closed_3273_ = lean_ctor_get_uint8(v___x_3265_, sizeof(void*)*7);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3275_ = v___x_3265_;
v_isShared_3276_ = v_isSharedCheck_3287_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_recvIdx_3272_);
lean_inc(v_sendIdx_3271_);
lean_inc(v_bufCount_3270_);
lean_inc(v_buf_3269_);
lean_inc(v_capacity_3268_);
lean_inc(v_consumers_3267_);
lean_inc(v_producers_3266_);
lean_dec(v___x_3265_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3287_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3277_ = lean_box(0);
lean_inc(v___x_3264_);
v___x_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3264_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = l_Std_Queue_enqueue___redArg(v___x_3278_, v_consumers_3267_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 1, v___x_3279_);
v___x_3281_ = v___x_3275_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_producers_3266_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_capacity_3268_);
lean_ctor_set(v_reuseFailAlloc_3286_, 3, v_buf_3269_);
lean_ctor_set(v_reuseFailAlloc_3286_, 4, v_bufCount_3270_);
lean_ctor_set(v_reuseFailAlloc_3286_, 5, v_sendIdx_3271_);
lean_ctor_set(v_reuseFailAlloc_3286_, 6, v_recvIdx_3272_);
lean_ctor_set_uint8(v_reuseFailAlloc_3286_, sizeof(void*)*7, v_closed_3273_);
v___x_3281_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3282_ = lean_st_ref_put(v___y_3258_, v___x_3281_);
v___x_3283_ = lean_io_promise_result_opt(v___x_3264_);
lean_dec(v___x_3264_);
v___x_3284_ = lean_unsigned_to_nat(0u);
v___x_3285_ = lean_io_bind_task(v___x_3283_, v___f_3257_, v___x_3284_, v_closed_3263_);
return v___x_3285_;
}
}
}
else
{
lean_object* v___x_3288_; 
lean_dec_ref(v___f_3257_);
v___x_3288_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3288_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3289_, v___y_3290_);
lean_dec(v___y_3290_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3293_, lean_object* v_res_3294_){
_start:
{
if (lean_obj_tag(v_res_3294_) == 0)
{
lean_dec_ref(v_ch_3293_);
goto v___jp_3296_;
}
else
{
lean_object* v_val_3298_; uint8_t v___x_3299_; 
v_val_3298_ = lean_ctor_get(v_res_3294_, 0);
v___x_3299_ = lean_unbox(v_val_3298_);
if (v___x_3299_ == 0)
{
lean_dec_ref(v_ch_3293_);
goto v___jp_3296_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3293_);
return v___x_3300_;
}
}
v___jp_3296_:
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3301_, lean_object* v_res_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3301_, v_res_3302_);
lean_dec(v_res_3302_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3305_){
_start:
{
lean_object* v___f_3307_; lean_object* v___f_3308_; lean_object* v___x_3309_; 
lean_inc_ref(v_ch_3305_);
v___f_3307_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3307_, 0, v_ch_3305_);
v___f_3308_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3308_, 0, v___f_3307_);
v___x_3309_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3305_, v___f_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3310_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3313_, lean_object* v_ch_3314_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3314_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3317_, lean_object* v_ch_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3317_, v_ch_3318_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3321_, lean_object* v_a_3322_){
_start:
{
uint8_t v___y_3324_; lean_object* v_bufCount_3328_; uint8_t v_closed_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v_bufCount_3328_ = lean_ctor_get(v_a_3322_, 4);
v_closed_3329_ = lean_ctor_get_uint8(v_a_3322_, sizeof(void*)*7);
v___x_3330_ = lean_unsigned_to_nat(0u);
v___x_3331_ = lean_nat_dec_eq(v_bufCount_3328_, v___x_3330_);
if (v___x_3331_ == 0)
{
uint8_t v___x_3332_; 
v___x_3332_ = 1;
v___y_3324_ = v___x_3332_;
goto v___jp_3323_;
}
else
{
v___y_3324_ = v_closed_3329_;
goto v___jp_3323_;
}
v___jp_3323_:
{
lean_object* v_toPure_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_toPure_3325_ = lean_ctor_get(v_toApplicative_3321_, 1);
lean_inc(v_toPure_3325_);
lean_dec_ref(v_toApplicative_3321_);
v___x_3326_ = lean_box(v___y_3324_);
v___x_3327_ = lean_apply_2(v_toPure_3325_, lean_box(0), v___x_3326_);
return v___x_3327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3333_, v_a_3334_);
lean_dec_ref(v_a_3334_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v_toApplicative_3339_; lean_object* v_toBind_3340_; lean_object* v___f_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_toApplicative_3339_ = lean_ctor_get(v_inst_3336_, 0);
lean_inc_ref(v_toApplicative_3339_);
v_toBind_3340_ = lean_ctor_get(v_inst_3336_, 1);
lean_inc(v_toBind_3340_);
lean_dec_ref(v_inst_3336_);
v___f_3341_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3341_, 0, v_toApplicative_3339_);
lean_inc(v_a_3338_);
v___x_3342_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3342_, 0, lean_box(0));
lean_closure_set(v___x_3342_, 1, lean_box(0));
lean_closure_set(v___x_3342_, 2, v_a_3338_);
v___x_3343_ = lean_apply_2(v_inst_3337_, lean_box(0), v___x_3342_);
v___x_3344_ = lean_apply_4(v_toBind_3340_, lean_box(0), lean_box(0), v___x_3343_, v___f_3341_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object* v_inst_3345_, lean_object* v_inst_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(v_inst_3345_, v_inst_3346_, v_a_3347_);
lean_dec(v_a_3347_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3349_, lean_object* v_00_u03b1_3350_, lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v_toApplicative_3354_; lean_object* v_toBind_3355_; lean_object* v___f_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_toApplicative_3354_ = lean_ctor_get(v_inst_3351_, 0);
lean_inc_ref(v_toApplicative_3354_);
v_toBind_3355_ = lean_ctor_get(v_inst_3351_, 1);
lean_inc(v_toBind_3355_);
lean_dec_ref(v_inst_3351_);
v___f_3356_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3356_, 0, v_toApplicative_3354_);
lean_inc(v_a_3353_);
v___x_3357_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3357_, 0, lean_box(0));
lean_closure_set(v___x_3357_, 1, lean_box(0));
lean_closure_set(v___x_3357_, 2, v_a_3353_);
v___x_3358_ = lean_apply_2(v_inst_3352_, lean_box(0), v___x_3357_);
v___x_3359_ = lean_apply_4(v_toBind_3355_, lean_box(0), lean_box(0), v___x_3358_, v___f_3356_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object* v_m_3360_, lean_object* v_00_u03b1_3361_, lean_object* v_inst_3362_, lean_object* v_inst_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(v_m_3360_, v_00_u03b1_3361_, v_inst_3362_, v_inst_3363_, v_a_3364_);
lean_dec(v_a_3364_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3366_){
_start:
{
lean_object* v___x_3368_; lean_object* v_producers_3369_; lean_object* v_consumers_3370_; lean_object* v_capacity_3371_; lean_object* v_buf_3372_; lean_object* v_bufCount_3373_; lean_object* v_sendIdx_3374_; lean_object* v_recvIdx_3375_; uint8_t v_closed_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3410_; 
v___x_3368_ = lean_st_ref_get(v_a_3366_);
v_producers_3369_ = lean_ctor_get(v___x_3368_, 0);
v_consumers_3370_ = lean_ctor_get(v___x_3368_, 1);
v_capacity_3371_ = lean_ctor_get(v___x_3368_, 2);
v_buf_3372_ = lean_ctor_get(v___x_3368_, 3);
v_bufCount_3373_ = lean_ctor_get(v___x_3368_, 4);
v_sendIdx_3374_ = lean_ctor_get(v___x_3368_, 5);
v_recvIdx_3375_ = lean_ctor_get(v___x_3368_, 6);
v_closed_3376_ = lean_ctor_get_uint8(v___x_3368_, sizeof(void*)*7);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3378_ = v___x_3368_;
v_isShared_3379_ = v_isSharedCheck_3410_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_recvIdx_3375_);
lean_inc(v_sendIdx_3374_);
lean_inc(v_bufCount_3373_);
lean_inc(v_buf_3372_);
lean_inc(v_capacity_3371_);
lean_inc(v_consumers_3370_);
lean_inc(v_producers_3369_);
lean_dec(v___x_3368_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3410_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3380_ = lean_unsigned_to_nat(0u);
v___x_3381_ = lean_nat_dec_eq(v_bufCount_3373_, v___x_3380_);
if (v___x_3381_ == 0)
{
uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v_st_3387_; lean_object* v___y_3388_; lean_object* v___y_3392_; lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3382_ = 1;
v___x_3383_ = lean_array_fget_borrowed(v_buf_3372_, v_recvIdx_3375_);
v___x_3384_ = lean_box(0);
v___x_3385_ = lean_st_ref_swap(v___x_3383_, v___x_3384_);
v___x_3405_ = lean_unsigned_to_nat(1u);
v___x_3406_ = lean_nat_add(v_recvIdx_3375_, v___x_3405_);
lean_dec(v_recvIdx_3375_);
v___x_3407_ = lean_nat_dec_eq(v___x_3406_, v_capacity_3371_);
if (v___x_3407_ == 0)
{
v___y_3392_ = v___x_3406_;
goto v___jp_3391_;
}
else
{
lean_dec(v___x_3406_);
v___y_3392_ = v___x_3380_;
goto v___jp_3391_;
}
v___jp_3386_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = lean_st_ref_swap(v___y_3388_, v_st_3387_);
lean_dec(v___x_3389_);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3385_);
return v___x_3390_;
}
v___jp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3393_ = lean_unsigned_to_nat(1u);
v___x_3394_ = lean_nat_sub(v_bufCount_3373_, v___x_3393_);
lean_dec(v_bufCount_3373_);
lean_inc(v___y_3392_);
lean_inc(v_sendIdx_3374_);
lean_inc(v___x_3394_);
lean_inc_ref(v_buf_3372_);
lean_inc(v_capacity_3371_);
lean_inc_ref(v_consumers_3370_);
lean_inc_ref(v_producers_3369_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 6, v___y_3392_);
lean_ctor_set(v___x_3378_, 4, v___x_3394_);
v___x_3396_ = v___x_3378_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_producers_3369_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_consumers_3370_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_capacity_3371_);
lean_ctor_set(v_reuseFailAlloc_3404_, 3, v_buf_3372_);
lean_ctor_set(v_reuseFailAlloc_3404_, 4, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3404_, 5, v_sendIdx_3374_);
lean_ctor_set(v_reuseFailAlloc_3404_, 6, v___y_3392_);
lean_ctor_set_uint8(v_reuseFailAlloc_3404_, sizeof(void*)*7, v_closed_3376_);
v___x_3396_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3397_; 
v___x_3397_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3369_);
if (lean_obj_tag(v___x_3397_) == 1)
{
lean_object* v_val_3398_; lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v___x_3396_);
v_val_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v___x_3397_, 1);
v_fst_3399_ = lean_ctor_get(v_val_3398_, 0);
lean_inc(v_fst_3399_);
v_snd_3400_ = lean_ctor_get(v_val_3398_, 1);
lean_inc(v_snd_3400_);
lean_dec(v_val_3398_);
v___x_3401_ = lean_box(v___x_3382_);
v___x_3402_ = lean_io_promise_resolve(v___x_3401_, v_fst_3399_);
lean_dec(v_fst_3399_);
v___x_3403_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3403_, 0, v_snd_3400_);
lean_ctor_set(v___x_3403_, 1, v_consumers_3370_);
lean_ctor_set(v___x_3403_, 2, v_capacity_3371_);
lean_ctor_set(v___x_3403_, 3, v_buf_3372_);
lean_ctor_set(v___x_3403_, 4, v___x_3394_);
lean_ctor_set(v___x_3403_, 5, v_sendIdx_3374_);
lean_ctor_set(v___x_3403_, 6, v___y_3392_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*7, v_closed_3376_);
v_st_3387_ = v___x_3403_;
v___y_3388_ = v_a_3366_;
goto v___jp_3386_;
}
else
{
lean_dec(v___x_3397_);
lean_dec(v___x_3394_);
lean_dec(v___y_3392_);
lean_dec(v_sendIdx_3374_);
lean_dec_ref(v_buf_3372_);
lean_dec(v_capacity_3371_);
lean_dec_ref(v_consumers_3370_);
v_st_3387_ = v___x_3396_;
v___y_3388_ = v_a_3366_;
goto v___jp_3386_;
}
}
}
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_del_object(v___x_3378_);
lean_dec(v_recvIdx_3375_);
lean_dec(v_sendIdx_3374_);
lean_dec(v_bufCount_3373_);
lean_dec_ref(v_buf_3372_);
lean_dec(v_capacity_3371_);
lean_dec_ref(v_consumers_3370_);
lean_dec_ref(v_producers_3369_);
v___x_3408_ = lean_box(0);
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
return v___x_3409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3411_);
lean_dec(v_a_3411_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3415_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3418_, lean_object* v_a_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3418_, v_a_3419_);
lean_dec(v_a_3419_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3422_, lean_object* v_lose_3423_){
_start:
{
lean_object* v_finished_3425_; lean_object* v_promise_3426_; lean_object* v___x_3427_; uint8_t v___y_3429_; uint8_t v___x_3437_; 
v_finished_3425_ = lean_ctor_get(v_w_3422_, 0);
v_promise_3426_ = lean_ctor_get(v_w_3422_, 1);
v___x_3427_ = lean_st_ref_take(v_finished_3425_);
v___x_3437_ = lean_unbox(v___x_3427_);
lean_dec(v___x_3427_);
if (v___x_3437_ == 0)
{
uint8_t v___x_3438_; 
v___x_3438_ = 1;
v___y_3429_ = v___x_3438_;
goto v___jp_3428_;
}
else
{
uint8_t v___x_3439_; 
v___x_3439_ = 0;
v___y_3429_ = v___x_3439_;
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
v___x_3433_ = lean_apply_1(v_lose_3423_, lean_box(0));
return v___x_3433_;
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
lean_dec_ref(v_lose_3423_);
v___x_3434_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__2));
v___x_3435_ = lean_io_promise_resolve(v___x_3434_, v_promise_3426_);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3440_, lean_object* v_lose_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3440_, v_lose_3441_);
lean_dec_ref(v_w_3440_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3444_, lean_object* v_w_3445_, lean_object* v_lose_3446_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3445_, v_lose_3446_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3449_, lean_object* v_w_3450_, lean_object* v_lose_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3449_, v_w_3450_, v_lose_3451_);
lean_dec_ref(v_w_3450_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3454_, lean_object* v_lose_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v_finished_3458_; lean_object* v_promise_3459_; lean_object* v___x_3460_; uint8_t v___y_3462_; uint8_t v___x_3478_; 
v_finished_3458_ = lean_ctor_get(v_w_3454_, 0);
v_promise_3459_ = lean_ctor_get(v_w_3454_, 1);
v___x_3460_ = lean_st_ref_take(v_finished_3458_);
v___x_3478_ = lean_unbox(v___x_3460_);
lean_dec(v___x_3460_);
if (v___x_3478_ == 0)
{
uint8_t v___x_3479_; 
v___x_3479_ = 1;
v___y_3462_ = v___x_3479_;
goto v___jp_3461_;
}
else
{
uint8_t v___x_3480_; 
v___x_3480_ = 0;
v___y_3462_ = v___x_3480_;
goto v___jp_3461_;
}
v___jp_3461_:
{
uint8_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = 1;
v___x_3464_ = lean_box(v___x_3463_);
v___x_3465_ = lean_st_ref_put(v_finished_3458_, v___x_3464_);
if (v___y_3462_ == 0)
{
lean_object* v___x_3466_; 
lean_inc(v___y_3456_);
v___x_3466_ = lean_apply_2(v_lose_3455_, v___y_3456_, lean_box(0));
return v___x_3466_;
}
else
{
lean_object* v___x_3467_; lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref(v_lose_3455_);
v___x_3467_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3456_);
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3477_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3477_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v_a_3468_);
v___x_3473_ = lean_io_promise_resolve(v___x_3472_, v_promise_3459_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3473_);
v___x_3475_ = v___x_3470_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3481_, lean_object* v_lose_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3481_, v_lose_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v_w_3481_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3486_, lean_object* v_w_3487_, lean_object* v_lose_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3487_, v_lose_3488_, v___y_3489_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3492_, lean_object* v_w_3493_, lean_object* v_lose_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3492_, v_w_3493_, v_lose_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v_w_3493_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3498_, lean_object* v_k_3499_){
_start:
{
lean_object* v_ref_3501_; lean_object* v_mutex_3502_; lean_object* v___x_3503_; lean_object* v_r_3504_; 
v_ref_3501_ = lean_ctor_get(v_mutex_3498_, 0);
lean_inc(v_ref_3501_);
v_mutex_3502_ = lean_ctor_get(v_mutex_3498_, 1);
lean_inc(v_mutex_3502_);
lean_dec_ref(v_mutex_3498_);
v___x_3503_ = lean_io_basemutex_lock(v_mutex_3502_);
v_r_3504_ = lean_apply_2(v_k_3499_, v_ref_3501_, lean_box(0));
if (lean_obj_tag(v_r_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3513_; 
v_a_3505_ = lean_ctor_get(v_r_3504_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v_r_3504_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3507_ = v_r_3504_;
v_isShared_3508_ = v_isSharedCheck_3513_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v_r_3504_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3513_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3509_ = lean_io_basemutex_unlock(v_mutex_3502_);
lean_dec(v_mutex_3502_);
if (v_isShared_3508_ == 0)
{
v___x_3511_ = v___x_3507_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3505_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3522_; 
v_a_3514_ = lean_ctor_get(v_r_3504_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_r_3504_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3516_ = v_r_3504_;
v_isShared_3517_ = v_isSharedCheck_3522_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v_r_3504_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3522_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3518_ = lean_io_basemutex_unlock(v_mutex_3502_);
lean_dec(v_mutex_3502_);
if (v_isShared_3517_ == 0)
{
v___x_3520_ = v___x_3516_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3514_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3523_, lean_object* v_k_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3523_, v_k_3524_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3527_, lean_object* v_00_u03b2_3528_, lean_object* v_mutex_3529_, lean_object* v_k_3530_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3529_, v_k_3530_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3533_, lean_object* v_00_u03b2_3534_, lean_object* v_mutex_3535_, lean_object* v_k_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3533_, v_00_u03b2_3534_, v_mutex_3535_, v_k_3536_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3539_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; lean_object* v_producers_3549_; lean_object* v_consumers_3550_; lean_object* v_capacity_3551_; lean_object* v_buf_3552_; lean_object* v_bufCount_3553_; lean_object* v_sendIdx_3554_; lean_object* v_recvIdx_3555_; uint8_t v_closed_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3579_; 
v___x_3548_ = lean_st_ref_get(v___y_3546_);
v_producers_3549_ = lean_ctor_get(v___x_3548_, 0);
v_consumers_3550_ = lean_ctor_get(v___x_3548_, 1);
v_capacity_3551_ = lean_ctor_get(v___x_3548_, 2);
v_buf_3552_ = lean_ctor_get(v___x_3548_, 3);
v_bufCount_3553_ = lean_ctor_get(v___x_3548_, 4);
v_sendIdx_3554_ = lean_ctor_get(v___x_3548_, 5);
v_recvIdx_3555_ = lean_ctor_get(v___x_3548_, 6);
v_closed_3556_ = lean_ctor_get_uint8(v___x_3548_, sizeof(void*)*7);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3558_ = v___x_3548_;
v_isShared_3559_ = v_isSharedCheck_3579_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_recvIdx_3555_);
lean_inc(v_sendIdx_3554_);
lean_inc(v_bufCount_3553_);
lean_inc(v_buf_3552_);
lean_inc(v_capacity_3551_);
lean_inc(v_consumers_3550_);
lean_inc(v_producers_3549_);
lean_dec(v___x_3548_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3579_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3550_);
if (lean_obj_tag(v___x_3560_) == 1)
{
lean_object* v_val_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3576_; 
v_val_3561_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3563_ = v___x_3560_;
v_isShared_3564_ = v_isSharedCheck_3576_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_val_3561_);
lean_dec(v___x_3560_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3576_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v_fst_3565_; lean_object* v_snd_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
v_fst_3565_ = lean_ctor_get(v_val_3561_, 0);
lean_inc(v_fst_3565_);
v_snd_3566_ = lean_ctor_get(v_val_3561_, 1);
lean_inc(v_snd_3566_);
lean_dec(v_val_3561_);
v___x_3567_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3565_, v_____do__lift_3545_);
lean_dec(v_fst_3565_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 1, v_snd_3566_);
v___x_3569_ = v___x_3558_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_producers_3549_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_snd_3566_);
lean_ctor_set(v_reuseFailAlloc_3575_, 2, v_capacity_3551_);
lean_ctor_set(v_reuseFailAlloc_3575_, 3, v_buf_3552_);
lean_ctor_set(v_reuseFailAlloc_3575_, 4, v_bufCount_3553_);
lean_ctor_set(v_reuseFailAlloc_3575_, 5, v_sendIdx_3554_);
lean_ctor_set(v_reuseFailAlloc_3575_, 6, v_recvIdx_3555_);
lean_ctor_set_uint8(v_reuseFailAlloc_3575_, sizeof(void*)*7, v_closed_3556_);
v___x_3569_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3570_ = lean_box(0);
v___x_3571_ = lean_st_ref_swap(v___y_3546_, v___x_3569_);
lean_dec(v___x_3571_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set_tag(v___x_3563_, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3570_);
v___x_3573_ = v___x_3563_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3570_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_dec(v___x_3560_);
lean_del_object(v___x_3558_);
lean_dec(v_recvIdx_3555_);
lean_dec(v_sendIdx_3554_);
lean_dec(v_bufCount_3553_);
lean_dec_ref(v_buf_3552_);
lean_dec(v_capacity_3551_);
lean_dec_ref(v_producers_3549_);
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
uint8_t v_____do__lift_3555__boxed_3583_; lean_object* v_res_3584_; 
v_____do__lift_3555__boxed_3583_ = lean_unbox(v_____do__lift_3580_);
v_res_3584_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3555__boxed_3583_, v___y_3581_);
lean_dec(v___y_3581_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3585_, lean_object* v___f_3586_, uint8_t v_____do__lift_3587_, lean_object* v___y_3588_){
_start:
{
if (v_____do__lift_3587_ == 0)
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v_producers_3592_; lean_object* v_consumers_3593_; lean_object* v_capacity_3594_; lean_object* v_buf_3595_; lean_object* v_bufCount_3596_; lean_object* v_sendIdx_3597_; lean_object* v_recvIdx_3598_; uint8_t v_closed_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3613_; 
v___x_3590_ = lean_io_promise_new();
v___x_3591_ = lean_st_ref_take(v___y_3588_);
v_producers_3592_ = lean_ctor_get(v___x_3591_, 0);
v_consumers_3593_ = lean_ctor_get(v___x_3591_, 1);
v_capacity_3594_ = lean_ctor_get(v___x_3591_, 2);
v_buf_3595_ = lean_ctor_get(v___x_3591_, 3);
v_bufCount_3596_ = lean_ctor_get(v___x_3591_, 4);
v_sendIdx_3597_ = lean_ctor_get(v___x_3591_, 5);
v_recvIdx_3598_ = lean_ctor_get(v___x_3591_, 6);
v_closed_3599_ = lean_ctor_get_uint8(v___x_3591_, sizeof(void*)*7);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3601_ = v___x_3591_;
v_isShared_3602_ = v_isSharedCheck_3613_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_recvIdx_3598_);
lean_inc(v_sendIdx_3597_);
lean_inc(v_bufCount_3596_);
lean_inc(v_buf_3595_);
lean_inc(v_capacity_3594_);
lean_inc(v_consumers_3593_);
lean_inc(v_producers_3592_);
lean_dec(v___x_3591_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3613_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v_waiter_3585_);
lean_inc(v___x_3590_);
v___x_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3590_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = l_Std_Queue_enqueue___redArg(v___x_3604_, v_consumers_3593_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 1, v___x_3605_);
v___x_3607_ = v___x_3601_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_producers_3592_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_capacity_3594_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_buf_3595_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v_bufCount_3596_);
lean_ctor_set(v_reuseFailAlloc_3612_, 5, v_sendIdx_3597_);
lean_ctor_set(v_reuseFailAlloc_3612_, 6, v_recvIdx_3598_);
lean_ctor_set_uint8(v_reuseFailAlloc_3612_, sizeof(void*)*7, v_closed_3599_);
v___x_3607_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3608_ = lean_st_ref_put(v___y_3588_, v___x_3607_);
v___x_3609_ = lean_io_promise_result_opt(v___x_3590_);
lean_dec(v___x_3590_);
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = l_EIO_chainTask___redArg(v___x_3609_, v___f_3586_, v___x_3610_, v_____do__lift_3587_);
return v___x_3611_;
}
}
}
else
{
lean_object* v___x_3614_; lean_object* v_lose_3615_; lean_object* v___x_3616_; 
lean_dec_ref(v___f_3586_);
v___x_3614_ = lean_box(v_____do__lift_3587_);
v_lose_3615_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3615_, 0, v___x_3614_);
v___x_3616_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3585_, v_lose_3615_, v___y_3588_);
lean_dec_ref(v_waiter_3585_);
return v___x_3616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3617_, lean_object* v___f_3618_, lean_object* v_____do__lift_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
uint8_t v_____do__lift_3613__boxed_3622_; lean_object* v_res_3623_; 
v_____do__lift_3613__boxed_3622_ = lean_unbox(v_____do__lift_3619_);
v_res_3623_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3617_, v___f_3618_, v_____do__lift_3613__boxed_3622_, v___y_3620_);
lean_dec(v___y_3620_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___x_3627_; lean_object* v_bufCount_3628_; uint8_t v_closed_3629_; lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3627_ = lean_st_ref_get(v___y_3625_);
v_bufCount_3628_ = lean_ctor_get(v___x_3627_, 4);
lean_inc(v_bufCount_3628_);
v_closed_3629_ = lean_ctor_get_uint8(v___x_3627_, sizeof(void*)*7);
lean_dec(v___x_3627_);
v___x_3630_ = lean_unsigned_to_nat(0u);
v___x_3631_ = lean_nat_dec_eq(v_bufCount_3628_, v___x_3630_);
lean_dec(v_bufCount_3628_);
if (v___x_3631_ == 0)
{
uint8_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3632_ = 1;
v___x_3633_ = lean_box(v___x_3632_);
lean_inc(v___y_3625_);
v___x_3634_ = lean_apply_3(v___f_3624_, v___x_3633_, v___y_3625_, lean_box(0));
return v___x_3634_;
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_box(v_closed_3629_);
lean_inc(v___y_3625_);
v___x_3636_ = lean_apply_3(v___f_3624_, v___x_3635_, v___y_3625_, lean_box(0));
return v___x_3636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3637_, v___y_3638_);
lean_dec(v___y_3638_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3643_, lean_object* v_ch_3644_, lean_object* v_x_3645_){
_start:
{
if (lean_obj_tag(v_x_3645_) == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_dec_ref(v_ch_3644_);
lean_dec_ref(v_waiter_3643_);
v___x_3647_ = lean_box(0);
v___x_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
return v___x_3648_;
}
else
{
lean_object* v_val_3649_; uint8_t v___x_3650_; 
v_val_3649_ = lean_ctor_get(v_x_3645_, 0);
v___x_3650_ = lean_unbox(v_val_3649_);
if (v___x_3650_ == 0)
{
lean_object* v___f_3651_; lean_object* v___x_3652_; 
lean_dec_ref(v_ch_3644_);
v___f_3651_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3652_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3643_, v___f_3651_);
lean_dec_ref(v_waiter_3643_);
return v___x_3652_;
}
else
{
lean_object* v___x_3653_; 
v___x_3653_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3644_, v_waiter_3643_);
return v___x_3653_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3654_, lean_object* v_ch_3655_, lean_object* v_x_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3654_, v_ch_3655_, v_x_3656_);
lean_dec(v_x_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3659_, lean_object* v_waiter_3660_){
_start:
{
lean_object* v___f_3662_; lean_object* v___f_3663_; lean_object* v___f_3664_; lean_object* v___x_3665_; 
lean_inc_ref(v_ch_3659_);
lean_inc_ref(v_waiter_3660_);
v___f_3662_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3662_, 0, v_waiter_3660_);
lean_closure_set(v___f_3662_, 1, v_ch_3659_);
v___f_3663_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3663_, 0, v_waiter_3660_);
lean_closure_set(v___f_3663_, 1, v___f_3662_);
v___f_3664_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3664_, 0, v___f_3663_);
v___x_3665_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3659_, v___f_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3666_, lean_object* v_waiter_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3666_, v_waiter_3667_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3670_, lean_object* v_ch_3671_, lean_object* v_waiter_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3671_, v_waiter_3672_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3675_, lean_object* v_ch_3676_, lean_object* v_waiter_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3675_, v_ch_3676_, v_waiter_3677_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3680_, lean_object* v_x_3681_){
_start:
{
if (lean_obj_tag(v_x_3681_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3691_; 
lean_dec_ref(v_x_3680_);
v_a_3683_ = lean_ctor_get(v_x_3681_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_x_3681_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3685_ = v_x_3681_;
v_isShared_3686_ = v_isSharedCheck_3691_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v_x_3681_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3691_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
}
}
else
{
lean_object* v___x_3692_; 
lean_dec_ref_known(v_x_3681_, 1);
v___x_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3692_, 0, v_x_3680_);
return v___x_3692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3693_, lean_object* v_x_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3693_, v_x_3694_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3697_, uint8_t v___x_3698_, lean_object* v___f_3699_, lean_object* v_____r_3700_, lean_object* v_st_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3704_ = lean_st_ref_swap(v___y_3702_, v_st_3701_);
lean_dec(v___x_3704_);
v___x_3705_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_3706_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3697_, v___x_3698_, v___x_3705_, v___f_3699_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3707_, lean_object* v___x_3708_, lean_object* v___f_3709_, lean_object* v_____r_3710_, lean_object* v_st_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
uint8_t v___x_6366__boxed_3714_; lean_object* v_res_3715_; 
v___x_6366__boxed_3714_ = lean_unbox(v___x_3708_);
v_res_3715_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3707_, v___x_6366__boxed_3714_, v___f_3709_, v_____r_3710_, v_st_3711_, v___y_3712_);
lean_dec(v___y_3712_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3716_, lean_object* v_consumers_3717_, lean_object* v_capacity_3718_, lean_object* v_buf_3719_, lean_object* v___x_3720_, lean_object* v_sendIdx_3721_, lean_object* v___y_3722_, uint8_t v_closed_3723_, lean_object* v___f_3724_, lean_object* v_a_3725_, lean_object* v_x_3726_){
_start:
{
if (lean_obj_tag(v_x_3726_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3736_; 
lean_dec_ref(v___f_3724_);
lean_dec(v___y_3722_);
lean_dec(v_sendIdx_3721_);
lean_dec(v___x_3720_);
lean_dec_ref(v_buf_3719_);
lean_dec(v_capacity_3718_);
lean_dec_ref(v_consumers_3717_);
lean_dec_ref(v_snd_3716_);
v_a_3728_ = lean_ctor_get(v_x_3726_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_x_3726_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3730_ = v_x_3726_;
v_isShared_3731_ = v_isSharedCheck_3736_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v_x_3726_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3736_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
return v___x_3734_;
}
}
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_dec_ref_known(v_x_3726_, 1);
v___x_3737_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3737_, 0, v_snd_3716_);
lean_ctor_set(v___x_3737_, 1, v_consumers_3717_);
lean_ctor_set(v___x_3737_, 2, v_capacity_3718_);
lean_ctor_set(v___x_3737_, 3, v_buf_3719_);
lean_ctor_set(v___x_3737_, 4, v___x_3720_);
lean_ctor_set(v___x_3737_, 5, v_sendIdx_3721_);
lean_ctor_set(v___x_3737_, 6, v___y_3722_);
lean_ctor_set_uint8(v___x_3737_, sizeof(void*)*7, v_closed_3723_);
v___x_3738_ = lean_box(0);
lean_inc(v_a_3725_);
v___x_3739_ = lean_apply_4(v___f_3724_, v___x_3738_, v___x_3737_, v_a_3725_, lean_box(0));
return v___x_3739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3740_, lean_object* v_consumers_3741_, lean_object* v_capacity_3742_, lean_object* v_buf_3743_, lean_object* v___x_3744_, lean_object* v_sendIdx_3745_, lean_object* v___y_3746_, lean_object* v_closed_3747_, lean_object* v___f_3748_, lean_object* v_a_3749_, lean_object* v_x_3750_, lean_object* v___y_3751_){
_start:
{
uint8_t v_closed_boxed_3752_; lean_object* v_res_3753_; 
v_closed_boxed_3752_ = lean_unbox(v_closed_3747_);
v_res_3753_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3740_, v_consumers_3741_, v_capacity_3742_, v_buf_3743_, v___x_3744_, v_sendIdx_3745_, v___y_3746_, v_closed_boxed_3752_, v___f_3748_, v_a_3749_, v_x_3750_);
lean_dec(v_a_3749_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3754_, uint8_t v___x_3755_, lean_object* v_bufCount_3756_, lean_object* v_producers_3757_, lean_object* v_consumers_3758_, lean_object* v_capacity_3759_, lean_object* v_buf_3760_, lean_object* v_sendIdx_3761_, uint8_t v_closed_3762_, lean_object* v_a_3763_, uint8_t v___x_3764_, lean_object* v_recvIdx_3765_, lean_object* v_x_3766_){
_start:
{
if (lean_obj_tag(v_x_3766_) == 0)
{
lean_object* v___x_3768_; 
lean_dec(v_sendIdx_3761_);
lean_dec_ref(v_buf_3760_);
lean_dec(v_capacity_3759_);
lean_dec_ref(v_consumers_3758_);
lean_dec_ref(v_producers_3757_);
lean_dec(v___x_3754_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_x_3766_);
return v___x_3768_;
}
else
{
lean_object* v___f_3769_; lean_object* v___x_3770_; lean_object* v___f_3771_; lean_object* v___y_3773_; lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___f_3769_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3769_, 0, v_x_3766_);
v___x_3770_ = lean_box(v___x_3755_);
lean_inc_ref(v___f_3769_);
lean_inc(v___x_3754_);
v___f_3771_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3771_, 0, v___x_3754_);
lean_closure_set(v___f_3771_, 1, v___x_3770_);
lean_closure_set(v___f_3771_, 2, v___f_3769_);
v___x_3796_ = lean_unsigned_to_nat(1u);
v___x_3797_ = lean_nat_add(v_recvIdx_3765_, v___x_3796_);
v___x_3798_ = lean_nat_dec_eq(v___x_3797_, v_capacity_3759_);
if (v___x_3798_ == 0)
{
v___y_3773_ = v___x_3797_;
goto v___jp_3772_;
}
else
{
lean_dec(v___x_3797_);
lean_inc(v___x_3754_);
v___y_3773_ = v___x_3754_;
goto v___jp_3772_;
}
v___jp_3772_:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3774_ = lean_unsigned_to_nat(1u);
v___x_3775_ = lean_nat_sub(v_bufCount_3756_, v___x_3774_);
lean_inc(v___y_3773_);
lean_inc(v_sendIdx_3761_);
lean_inc(v___x_3775_);
lean_inc_ref(v_buf_3760_);
lean_inc(v_capacity_3759_);
lean_inc_ref(v_consumers_3758_);
lean_inc_ref(v_producers_3757_);
v___x_3776_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3776_, 0, v_producers_3757_);
lean_ctor_set(v___x_3776_, 1, v_consumers_3758_);
lean_ctor_set(v___x_3776_, 2, v_capacity_3759_);
lean_ctor_set(v___x_3776_, 3, v_buf_3760_);
lean_ctor_set(v___x_3776_, 4, v___x_3775_);
lean_ctor_set(v___x_3776_, 5, v_sendIdx_3761_);
lean_ctor_set(v___x_3776_, 6, v___y_3773_);
lean_ctor_set_uint8(v___x_3776_, sizeof(void*)*7, v_closed_3762_);
v___x_3777_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3757_);
if (lean_obj_tag(v___x_3777_) == 1)
{
lean_object* v_val_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref_known(v___x_3776_, 7);
lean_dec_ref(v___f_3769_);
v_val_3778_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3780_ = v___x_3777_;
v_isShared_3781_ = v_isSharedCheck_3793_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_val_3778_);
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3793_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v_fst_3782_; lean_object* v_snd_3783_; lean_object* v___x_3784_; lean_object* v___f_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
v_fst_3782_ = lean_ctor_get(v_val_3778_, 0);
lean_inc(v_fst_3782_);
v_snd_3783_ = lean_ctor_get(v_val_3778_, 1);
lean_inc(v_snd_3783_);
lean_dec(v_val_3778_);
v___x_3784_ = lean_box(v_closed_3762_);
lean_inc(v_a_3763_);
v___f_3785_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3785_, 0, v_snd_3783_);
lean_closure_set(v___f_3785_, 1, v_consumers_3758_);
lean_closure_set(v___f_3785_, 2, v_capacity_3759_);
lean_closure_set(v___f_3785_, 3, v_buf_3760_);
lean_closure_set(v___f_3785_, 4, v___x_3775_);
lean_closure_set(v___f_3785_, 5, v_sendIdx_3761_);
lean_closure_set(v___f_3785_, 6, v___y_3773_);
lean_closure_set(v___f_3785_, 7, v___x_3784_);
lean_closure_set(v___f_3785_, 8, v___f_3771_);
lean_closure_set(v___f_3785_, 9, v_a_3763_);
v___x_3786_ = lean_box(v___x_3764_);
v___x_3787_ = lean_io_promise_resolve(v___x_3786_, v_fst_3782_);
lean_dec(v_fst_3782_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v___x_3787_);
v___x_3789_ = v___x_3780_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
v___x_3791_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3754_, v___x_3755_, v___x_3790_, v___f_3785_);
return v___x_3791_;
}
}
}
else
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
lean_dec(v___x_3777_);
lean_dec(v___x_3775_);
lean_dec(v___y_3773_);
lean_dec_ref(v___f_3771_);
lean_dec(v_sendIdx_3761_);
lean_dec_ref(v_buf_3760_);
lean_dec(v_capacity_3759_);
lean_dec_ref(v_consumers_3758_);
v___x_3794_ = lean_box(0);
v___x_3795_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3754_, v___x_3755_, v___f_3769_, v___x_3794_, v___x_3776_, v_a_3763_);
return v___x_3795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3799_, lean_object* v___x_3800_, lean_object* v_bufCount_3801_, lean_object* v_producers_3802_, lean_object* v_consumers_3803_, lean_object* v_capacity_3804_, lean_object* v_buf_3805_, lean_object* v_sendIdx_3806_, lean_object* v_closed_3807_, lean_object* v_a_3808_, lean_object* v___x_3809_, lean_object* v_recvIdx_3810_, lean_object* v_x_3811_, lean_object* v___y_3812_){
_start:
{
uint8_t v___x_6435__boxed_3813_; uint8_t v_closed_boxed_3814_; uint8_t v___x_6436__boxed_3815_; lean_object* v_res_3816_; 
v___x_6435__boxed_3813_ = lean_unbox(v___x_3800_);
v_closed_boxed_3814_ = lean_unbox(v_closed_3807_);
v___x_6436__boxed_3815_ = lean_unbox(v___x_3809_);
v_res_3816_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3799_, v___x_6435__boxed_3813_, v_bufCount_3801_, v_producers_3802_, v_consumers_3803_, v_capacity_3804_, v_buf_3805_, v_sendIdx_3806_, v_closed_boxed_3814_, v_a_3808_, v___x_6436__boxed_3815_, v_recvIdx_3810_, v_x_3811_);
lean_dec(v_recvIdx_3810_);
lean_dec(v_a_3808_);
lean_dec(v_bufCount_3801_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3817_, lean_object* v_x_3818_){
_start:
{
if (lean_obj_tag(v_x_3818_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3828_; 
v_a_3820_ = lean_ctor_get(v_x_3818_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_x_3818_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3822_ = v_x_3818_;
v_isShared_3823_ = v_isSharedCheck_3828_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v_x_3818_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3828_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
return v___x_3826_;
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3857_; 
v_a_3829_ = lean_ctor_get(v_x_3818_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_x_3818_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3831_ = v_x_3818_;
v_isShared_3832_ = v_isSharedCheck_3857_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v_x_3818_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3857_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v_producers_3833_; lean_object* v_consumers_3834_; lean_object* v_capacity_3835_; lean_object* v_buf_3836_; lean_object* v_bufCount_3837_; lean_object* v_sendIdx_3838_; lean_object* v_recvIdx_3839_; uint8_t v_closed_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v_producers_3833_ = lean_ctor_get(v_a_3829_, 0);
lean_inc_ref(v_producers_3833_);
v_consumers_3834_ = lean_ctor_get(v_a_3829_, 1);
lean_inc_ref(v_consumers_3834_);
v_capacity_3835_ = lean_ctor_get(v_a_3829_, 2);
lean_inc(v_capacity_3835_);
v_buf_3836_ = lean_ctor_get(v_a_3829_, 3);
lean_inc_ref(v_buf_3836_);
v_bufCount_3837_ = lean_ctor_get(v_a_3829_, 4);
lean_inc(v_bufCount_3837_);
v_sendIdx_3838_ = lean_ctor_get(v_a_3829_, 5);
lean_inc(v_sendIdx_3838_);
v_recvIdx_3839_ = lean_ctor_get(v_a_3829_, 6);
lean_inc(v_recvIdx_3839_);
v_closed_3840_ = lean_ctor_get_uint8(v_a_3829_, sizeof(void*)*7);
lean_dec(v_a_3829_);
v___x_3841_ = lean_unsigned_to_nat(0u);
v___x_3842_ = lean_nat_dec_eq(v_bufCount_3837_, v___x_3841_);
if (v___x_3842_ == 0)
{
uint8_t v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___f_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3843_ = 1;
v___x_3844_ = lean_box(v___x_3842_);
v___x_3845_ = lean_box(v_closed_3840_);
v___x_3846_ = lean_box(v___x_3843_);
lean_inc(v_recvIdx_3839_);
lean_inc(v_a_3817_);
lean_inc_ref(v_buf_3836_);
v___f_3847_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_3847_, 0, v___x_3841_);
lean_closure_set(v___f_3847_, 1, v___x_3844_);
lean_closure_set(v___f_3847_, 2, v_bufCount_3837_);
lean_closure_set(v___f_3847_, 3, v_producers_3833_);
lean_closure_set(v___f_3847_, 4, v_consumers_3834_);
lean_closure_set(v___f_3847_, 5, v_capacity_3835_);
lean_closure_set(v___f_3847_, 6, v_buf_3836_);
lean_closure_set(v___f_3847_, 7, v_sendIdx_3838_);
lean_closure_set(v___f_3847_, 8, v___x_3845_);
lean_closure_set(v___f_3847_, 9, v_a_3817_);
lean_closure_set(v___f_3847_, 10, v___x_3846_);
lean_closure_set(v___f_3847_, 11, v_recvIdx_3839_);
v___x_3848_ = lean_array_fget(v_buf_3836_, v_recvIdx_3839_);
lean_dec(v_recvIdx_3839_);
lean_dec_ref(v_buf_3836_);
v___x_3849_ = lean_box(0);
v___x_3850_ = lean_st_ref_swap(v___x_3848_, v___x_3849_);
lean_dec(v___x_3848_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v___x_3850_);
v___x_3852_ = v___x_3831_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3850_);
v___x_3852_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
v___x_3854_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3841_, v___x_3842_, v___x_3853_, v___f_3847_);
return v___x_3854_;
}
}
else
{
lean_object* v___x_3856_; 
lean_dec(v_recvIdx_3839_);
lean_dec(v_sendIdx_3838_);
lean_dec(v_bufCount_3837_);
lean_dec_ref(v_buf_3836_);
lean_dec(v_capacity_3835_);
lean_dec_ref(v_consumers_3834_);
lean_dec_ref(v_producers_3833_);
lean_del_object(v___x_3831_);
v___x_3856_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_3856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_3858_, lean_object* v_x_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3858_, v_x_3859_);
lean_dec(v_a_3858_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_3862_){
_start:
{
lean_object* v___f_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_inc(v_a_3862_);
v___f_3864_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3864_, 0, v_a_3862_);
v___x_3865_ = lean_unsigned_to_nat(0u);
v___x_3866_ = 0;
v___x_3867_ = lean_st_ref_get(v_a_3862_);
v___x_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
v___x_3870_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3865_, v___x_3866_, v___x_3869_, v___f_3864_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3871_);
lean_dec(v_a_3871_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3875_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_3878_, lean_object* v_a_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_3878_, v_a_3879_);
lean_dec(v_a_3879_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_3882_, lean_object* v_x_3883_){
_start:
{
lean_object* v_val_3886_; lean_object* v___x_3888_; 
v___x_3888_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3882_, v_x_3883_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3888_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3888_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
lean_ctor_set_tag(v___x_3891_, 1);
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
v_val_3886_ = v___x_3894_;
goto v___jp_3885_;
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
v_a_3897_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3888_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3888_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set_tag(v___x_3899_, 0);
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
v_val_3886_ = v___x_3902_;
goto v___jp_3885_;
}
}
}
v___jp_3885_:
{
lean_object* v___x_3887_; 
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v_val_3886_);
return v___x_3887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_3905_, lean_object* v_x_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_3905_, v_x_3906_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v___y_3909_, lean_object* v___f_3910_, lean_object* v_x_3911_){
_start:
{
if (lean_obj_tag(v_x_3911_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3921_; 
lean_dec_ref(v___f_3910_);
v_a_3913_ = lean_ctor_get(v_x_3911_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_x_3911_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3915_ = v_x_3911_;
v_isShared_3916_ = v_isSharedCheck_3921_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v_x_3911_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3921_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
return v___x_3919_;
}
}
}
else
{
lean_object* v_a_3922_; uint8_t v___x_3923_; 
v_a_3922_ = lean_ctor_get(v_x_3911_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v_x_3911_, 1);
v___x_3923_ = lean_unbox(v_a_3922_);
lean_dec(v_a_3922_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; 
lean_dec_ref(v___f_3910_);
v___x_3924_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_3924_;
}
else
{
lean_object* v___x_3925_; uint8_t v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3925_ = lean_unsigned_to_nat(0u);
v___x_3926_ = 0;
v___x_3927_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_3909_);
v___x_3928_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3925_, v___x_3926_, v___x_3927_, v___f_3910_);
return v___x_3928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v___y_3929_, lean_object* v___f_3930_, lean_object* v_x_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v___y_3929_, v___f_3930_, v_x_3931_);
lean_dec(v___y_3929_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___x_3934_, lean_object* v_x_3935_){
_start:
{
uint8_t v___y_3938_; 
if (lean_obj_tag(v_x_3935_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3950_; 
v_a_3942_ = lean_ctor_get(v_x_3935_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_x_3935_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3944_ = v_x_3935_;
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v_x_3935_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
return v___x_3948_;
}
}
}
else
{
lean_object* v_a_3951_; lean_object* v_bufCount_3952_; uint8_t v_closed_3953_; uint8_t v___x_3954_; 
v_a_3951_ = lean_ctor_get(v_x_3935_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v_x_3935_, 1);
v_bufCount_3952_ = lean_ctor_get(v_a_3951_, 4);
lean_inc(v_bufCount_3952_);
v_closed_3953_ = lean_ctor_get_uint8(v_a_3951_, sizeof(void*)*7);
lean_dec(v_a_3951_);
v___x_3954_ = lean_nat_dec_eq(v_bufCount_3952_, v___x_3934_);
lean_dec(v_bufCount_3952_);
if (v___x_3954_ == 0)
{
uint8_t v___x_3955_; 
v___x_3955_ = 1;
v___y_3938_ = v___x_3955_;
goto v___jp_3937_;
}
else
{
v___y_3938_ = v_closed_3953_;
goto v___jp_3937_;
}
}
v___jp_3937_:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3939_ = lean_box(v___y_3938_);
v___x_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
return v___x_3941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_3956_, lean_object* v_x_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___x_3956_, v_x_3957_);
lean_dec(v___x_3956_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___f_3965_; lean_object* v___x_3966_; lean_object* v___f_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
lean_inc(v___y_3963_);
v___f_3965_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3965_, 0, v___y_3963_);
lean_closure_set(v___f_3965_, 1, v___f_3962_);
v___x_3966_ = lean_unsigned_to_nat(0u);
v___f_3967_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___closed__0));
v___x_3968_ = 0;
v___x_3969_ = lean_st_ref_get(v___y_3963_);
v___x_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
v___x_3972_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3966_, v___x_3968_, v___x_3971_, v___f_3967_);
v___x_3973_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3966_, v___x_3968_, v___x_3972_, v___f_3965_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_3974_, v___y_3975_);
lean_dec(v___y_3975_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_3978_, lean_object* v_capacity_3979_, lean_object* v_buf_3980_, lean_object* v_bufCount_3981_, lean_object* v_sendIdx_3982_, lean_object* v_recvIdx_3983_, uint8_t v_closed_3984_, lean_object* v___y_3985_, lean_object* v_x_3986_){
_start:
{
if (lean_obj_tag(v_x_3986_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3996_; 
lean_dec(v_recvIdx_3983_);
lean_dec(v_sendIdx_3982_);
lean_dec(v_bufCount_3981_);
lean_dec_ref(v_buf_3980_);
lean_dec(v_capacity_3979_);
lean_dec_ref(v_producers_3978_);
v_a_3988_ = lean_ctor_get(v_x_3986_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_x_3986_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3990_ = v_x_3986_;
v_isShared_3991_ = v_isSharedCheck_3996_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v_x_3986_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3996_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3988_);
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
else
{
lean_object* v_a_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v_a_3997_ = lean_ctor_get(v_x_3986_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v_x_3986_, 1);
v___x_3998_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3998_, 0, v_producers_3978_);
lean_ctor_set(v___x_3998_, 1, v_a_3997_);
lean_ctor_set(v___x_3998_, 2, v_capacity_3979_);
lean_ctor_set(v___x_3998_, 3, v_buf_3980_);
lean_ctor_set(v___x_3998_, 4, v_bufCount_3981_);
lean_ctor_set(v___x_3998_, 5, v_sendIdx_3982_);
lean_ctor_set(v___x_3998_, 6, v_recvIdx_3983_);
lean_ctor_set_uint8(v___x_3998_, sizeof(void*)*7, v_closed_3984_);
v___x_3999_ = lean_st_ref_swap(v___y_3985_, v___x_3998_);
lean_dec(v___x_3999_);
v___x_4000_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_4001_, lean_object* v_capacity_4002_, lean_object* v_buf_4003_, lean_object* v_bufCount_4004_, lean_object* v_sendIdx_4005_, lean_object* v_recvIdx_4006_, lean_object* v_closed_4007_, lean_object* v___y_4008_, lean_object* v_x_4009_, lean_object* v___y_4010_){
_start:
{
uint8_t v_closed_boxed_4011_; lean_object* v_res_4012_; 
v_closed_boxed_4011_ = lean_unbox(v_closed_4007_);
v_res_4012_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_4001_, v_capacity_4002_, v_buf_4003_, v_bufCount_4004_, v_sendIdx_4005_, v_recvIdx_4006_, v_closed_boxed_4011_, v___y_4008_, v_x_4009_);
lean_dec(v___y_4008_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_4013_, lean_object* v_x_4014_, lean_object* v_head_4015_, lean_object* v_x_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_4013_, v_x_4014_, v_head_4015_, v_x_4016_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_4019_, lean_object* v_x_4020_){
_start:
{
if (lean_obj_tag(v_x_4019_) == 0)
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4022_, 0, v_x_4020_);
v___x_4023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4022_);
return v___x_4023_;
}
else
{
lean_object* v_head_4024_; lean_object* v_tail_4025_; lean_object* v_waiter_4026_; lean_object* v___f_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
v_head_4024_ = lean_ctor_get(v_x_4019_, 0);
lean_inc(v_head_4024_);
v_tail_4025_ = lean_ctor_get(v_x_4019_, 1);
lean_inc(v_tail_4025_);
lean_dec_ref_known(v_x_4019_, 2);
v_waiter_4026_ = lean_ctor_get(v_head_4024_, 1);
lean_inc(v_waiter_4026_);
v___f_4027_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4027_, 0, v_tail_4025_);
lean_closure_set(v___f_4027_, 1, v_x_4020_);
lean_closure_set(v___f_4027_, 2, v_head_4024_);
v___x_4028_ = lean_unsigned_to_nat(0u);
v___x_4029_ = 0;
if (lean_obj_tag(v_waiter_4026_) == 0)
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_4031_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4028_, v___x_4029_, v___x_4030_, v___f_4027_);
return v___x_4031_;
}
else
{
lean_object* v_val_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4045_; 
v_val_4032_ = lean_ctor_get(v_waiter_4026_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v_waiter_4026_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4034_ = v_waiter_4026_;
v_isShared_4035_ = v_isSharedCheck_4045_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_val_4032_);
lean_dec(v_waiter_4026_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4045_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v_finished_4036_; lean_object* v___f_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v_finished_4036_ = lean_ctor_get(v_val_4032_, 0);
lean_inc(v_finished_4036_);
lean_dec(v_val_4032_);
v___f_4037_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_4038_ = lean_st_ref_get(v_finished_4036_);
lean_dec(v_finished_4036_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v___x_4038_);
v___x_4040_ = v___x_4034_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4040_);
v___x_4042_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4028_, v___x_4029_, v___x_4041_, v___f_4037_);
v___x_4043_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4028_, v___x_4029_, v___x_4042_, v___f_4027_);
return v___x_4043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_4046_, lean_object* v_x_4047_, lean_object* v_head_4048_, lean_object* v_x_4049_){
_start:
{
if (lean_obj_tag(v_x_4049_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4059_; 
lean_dec_ref(v_head_4048_);
lean_dec(v_x_4047_);
lean_dec(v_tail_4046_);
v_a_4051_ = lean_ctor_get(v_x_4049_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v_x_4049_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4053_ = v_x_4049_;
v_isShared_4054_ = v_isSharedCheck_4059_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v_x_4049_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4059_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4051_);
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
}
else
{
lean_object* v_a_4060_; uint8_t v___x_4061_; 
v_a_4060_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v_x_4049_, 1);
v___x_4061_ = lean_unbox(v_a_4060_);
lean_dec(v_a_4060_);
if (v___x_4061_ == 0)
{
lean_object* v___x_4062_; 
lean_dec_ref(v_head_4048_);
v___x_4062_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4046_, v_x_4047_);
return v___x_4062_;
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4063_, 0, v_head_4048_);
lean_ctor_set(v___x_4063_, 1, v_x_4047_);
v___x_4064_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4046_, v___x_4063_);
return v___x_4064_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_4065_, lean_object* v_x_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4065_, v_x_4066_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_4069_){
_start:
{
if (lean_obj_tag(v_x_4069_) == 0)
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v_x_4069_);
return v___x_4071_;
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4081_; 
v_a_4072_ = lean_ctor_get(v_x_4069_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_x_4069_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4074_ = v_x_4069_;
v_isShared_4075_ = v_isSharedCheck_4081_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v_x_4069_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4081_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v___x_4078_; 
v___x_4076_ = l_List_reverse___redArg(v_a_4072_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4076_);
v___x_4078_ = v___x_4074_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4082_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4085_, lean_object* v___x_4086_, lean_object* v_x_4087_){
_start:
{
if (lean_obj_tag(v_x_4087_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v___x_4086_);
lean_dec(v_a_4085_);
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
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4114_; 
v_a_4098_ = lean_ctor_get(v_x_4087_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4100_ = v_x_4087_;
v_isShared_4101_ = v_isSharedCheck_4114_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v_x_4087_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4114_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
uint8_t v___x_4102_; 
v___x_4102_ = l_List_isEmpty___redArg(v_a_4085_);
if (v___x_4102_ == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4105_; 
lean_dec(v___x_4086_);
v___x_4103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4103_, 0, v_a_4098_);
lean_ctor_set(v___x_4103_, 1, v_a_4085_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4103_);
v___x_4105_ = v___x_4100_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4103_);
v___x_4105_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
return v___x_4106_;
}
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
lean_dec(v_a_4085_);
v___x_4108_ = l_List_reverse___redArg(v_a_4098_);
v___x_4109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4086_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4109_);
v___x_4111_ = v___x_4100_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4109_);
v___x_4111_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4112_; 
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
return v___x_4112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4115_, lean_object* v___x_4116_, lean_object* v_x_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4115_, v___x_4116_, v_x_4117_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v___x_4120_, lean_object* v_eList_4121_, lean_object* v___f_4122_, lean_object* v_x_4123_){
_start:
{
if (lean_obj_tag(v_x_4123_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4133_; 
lean_dec_ref(v___f_4122_);
lean_dec(v_eList_4121_);
lean_dec(v___x_4120_);
v_a_4125_ = lean_ctor_get(v_x_4123_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_x_4123_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4127_ = v_x_4123_;
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v_x_4123_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
return v___x_4131_;
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___f_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v_a_4134_ = lean_ctor_get(v_x_4123_, 0);
lean_inc(v_a_4134_);
lean_dec_ref_known(v_x_4123_, 1);
lean_inc(v___x_4120_);
v___f_4135_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4135_, 0, v_a_4134_);
lean_closure_set(v___f_4135_, 1, v___x_4120_);
v___x_4136_ = lean_unsigned_to_nat(0u);
v___x_4137_ = 0;
v___x_4138_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4121_, v___x_4120_);
v___x_4139_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4136_, v___x_4137_, v___x_4138_, v___f_4122_);
v___x_4140_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4136_, v___x_4137_, v___x_4139_, v___f_4135_);
return v___x_4140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v___x_4141_, lean_object* v_eList_4142_, lean_object* v___f_4143_, lean_object* v_x_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v___x_4141_, v_eList_4142_, v___f_4143_, v_x_4144_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_eList_4151_; lean_object* v_dList_4152_; lean_object* v___f_4153_; lean_object* v___x_4154_; lean_object* v___f_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v_eList_4151_ = lean_ctor_get(v_q_4148_, 0);
lean_inc(v_eList_4151_);
v_dList_4152_ = lean_ctor_get(v_q_4148_, 1);
lean_inc(v_dList_4152_);
lean_dec_ref(v_q_4148_);
v___f_4153_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4154_ = lean_box(0);
v___f_4155_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4155_, 0, v___x_4154_);
lean_closure_set(v___f_4155_, 1, v_eList_4151_);
lean_closure_set(v___f_4155_, 2, v___f_4153_);
v___x_4156_ = lean_unsigned_to_nat(0u);
v___x_4157_ = 0;
v___x_4158_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4152_, v___x_4154_);
v___x_4159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4156_, v___x_4157_, v___x_4158_, v___f_4153_);
v___x_4160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4156_, v___x_4157_, v___x_4159_, v___f_4155_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4161_, v___y_4162_);
lean_dec(v___y_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4165_, lean_object* v_x_4166_){
_start:
{
if (lean_obj_tag(v_x_4166_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4176_; 
v_a_4168_ = lean_ctor_get(v_x_4166_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_x_4166_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4170_ = v_x_4166_;
v_isShared_4171_ = v_isSharedCheck_4176_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v_x_4166_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4176_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4174_; 
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
return v___x_4174_;
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v_producers_4178_; lean_object* v_consumers_4179_; lean_object* v_capacity_4180_; lean_object* v_buf_4181_; lean_object* v_bufCount_4182_; lean_object* v_sendIdx_4183_; lean_object* v_recvIdx_4184_; uint8_t v_closed_4185_; lean_object* v___x_4186_; lean_object* v___f_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v_a_4177_ = lean_ctor_get(v_x_4166_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v_x_4166_, 1);
v_producers_4178_ = lean_ctor_get(v_a_4177_, 0);
lean_inc_ref(v_producers_4178_);
v_consumers_4179_ = lean_ctor_get(v_a_4177_, 1);
lean_inc_ref(v_consumers_4179_);
v_capacity_4180_ = lean_ctor_get(v_a_4177_, 2);
lean_inc(v_capacity_4180_);
v_buf_4181_ = lean_ctor_get(v_a_4177_, 3);
lean_inc_ref(v_buf_4181_);
v_bufCount_4182_ = lean_ctor_get(v_a_4177_, 4);
lean_inc(v_bufCount_4182_);
v_sendIdx_4183_ = lean_ctor_get(v_a_4177_, 5);
lean_inc(v_sendIdx_4183_);
v_recvIdx_4184_ = lean_ctor_get(v_a_4177_, 6);
lean_inc(v_recvIdx_4184_);
v_closed_4185_ = lean_ctor_get_uint8(v_a_4177_, sizeof(void*)*7);
lean_dec(v_a_4177_);
v___x_4186_ = lean_box(v_closed_4185_);
lean_inc(v___y_4165_);
v___f_4187_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4187_, 0, v_producers_4178_);
lean_closure_set(v___f_4187_, 1, v_capacity_4180_);
lean_closure_set(v___f_4187_, 2, v_buf_4181_);
lean_closure_set(v___f_4187_, 3, v_bufCount_4182_);
lean_closure_set(v___f_4187_, 4, v_sendIdx_4183_);
lean_closure_set(v___f_4187_, 5, v_recvIdx_4184_);
lean_closure_set(v___f_4187_, 6, v___x_4186_);
lean_closure_set(v___f_4187_, 7, v___y_4165_);
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = 0;
v___x_4190_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4179_, v___y_4165_);
v___x_4191_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4188_, v___x_4189_, v___x_4190_, v___f_4187_);
return v___x_4191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4192_, lean_object* v_x_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4192_, v_x_4193_);
lean_dec(v___y_4192_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4196_){
_start:
{
lean_object* v___f_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_inc(v___y_4196_);
v___f_4198_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4198_, 0, v___y_4196_);
v___x_4199_ = lean_unsigned_to_nat(0u);
v___x_4200_ = 0;
v___x_4201_ = lean_st_ref_get(v___y_4196_);
v___x_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
v___x_4204_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4199_, v___x_4200_, v___x_4203_, v___f_4198_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4205_);
lean_dec(v___y_4205_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4211_){
_start:
{
lean_object* v___f_4212_; lean_object* v___f_4213_; lean_object* v___f_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
lean_inc_ref_n(v_ch_4211_, 2);
v___f_4212_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4212_, 0, v_ch_4211_);
v___f_4213_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0));
v___f_4214_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___x_4215_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4215_, 0, lean_box(0));
lean_closure_set(v___x_4215_, 1, lean_box(0));
lean_closure_set(v___x_4215_, 2, v_ch_4211_);
lean_closure_set(v___x_4215_, 3, v___f_4213_);
v___x_4216_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4216_, 0, lean_box(0));
lean_closure_set(v___x_4216_, 1, lean_box(0));
lean_closure_set(v___x_4216_, 2, v_ch_4211_);
lean_closure_set(v___x_4216_, 3, v___f_4214_);
v___x_4217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4215_);
lean_ctor_set(v___x_4217_, 1, v___f_4212_);
lean_ctor_set(v___x_4217_, 2, v___x_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4218_, lean_object* v_ch_4219_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4221_, lean_object* v_q_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4222_, v___y_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4226_, lean_object* v_q_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4226_, v_q_4227_, v___y_4228_);
lean_dec(v___y_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4231_, lean_object* v_x_4232_, lean_object* v_x_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4232_, v_x_4233_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4237_, lean_object* v_x_4238_, lean_object* v_x_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4237_, v_x_4238_, v_x_4239_, v___y_4240_);
lean_dec(v___y_4240_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg(lean_object* v_x_4243_){
_start:
{
switch(lean_obj_tag(v_x_4243_))
{
case 0:
{
lean_object* v___x_4244_; 
v___x_4244_ = lean_unsigned_to_nat(0u);
return v___x_4244_;
}
case 1:
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_unsigned_to_nat(1u);
return v___x_4245_;
}
default: 
{
lean_object* v___x_4246_; 
v___x_4246_ = lean_unsigned_to_nat(2u);
return v___x_4246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(lean_object* v_x_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4247_);
lean_dec_ref(v_x_4247_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx(lean_object* v_00_u03b1_4249_, lean_object* v_x_4250_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___boxed(lean_object* v_00_u03b1_4252_, lean_object* v_x_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Std_CloseableChannel_Flavors_ctorIdx(v_00_u03b1_4252_, v_x_4253_);
lean_dec_ref(v_x_4253_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4255_, lean_object* v_k_4256_){
_start:
{
lean_object* v_ch_4257_; lean_object* v___x_4258_; 
v_ch_4257_ = lean_ctor_get(v_t_4255_, 0);
lean_inc_ref(v_ch_4257_);
lean_dec_ref(v_t_4255_);
v___x_4258_ = lean_apply_1(v_k_4256_, v_ch_4257_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4259_, lean_object* v_motive_4260_, lean_object* v_ctorIdx_4261_, lean_object* v_t_4262_, lean_object* v_h_4263_, lean_object* v_k_4264_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4262_, v_k_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4266_, lean_object* v_motive_4267_, lean_object* v_ctorIdx_4268_, lean_object* v_t_4269_, lean_object* v_h_4270_, lean_object* v_k_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4266_, v_motive_4267_, v_ctorIdx_4268_, v_t_4269_, v_h_4270_, v_k_4271_);
lean_dec(v_ctorIdx_4268_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4273_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4274_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4273_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4276_, lean_object* v_motive_4277_, lean_object* v_t_4278_, lean_object* v_h_4279_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4278_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4282_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4282_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4285_, lean_object* v_motive_4286_, lean_object* v_t_4287_, lean_object* v_h_4288_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4289_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4287_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4291_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4292_){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4291_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4294_, lean_object* v_motive_4295_, lean_object* v_t_4296_, lean_object* v_h_4297_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4298_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4296_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4300_){
_start:
{
if (lean_obj_tag(v_capacity_4300_) == 0)
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4302_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4302_);
return v___x_4303_;
}
else
{
lean_object* v_val_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4321_; 
v_val_4304_ = lean_ctor_get(v_capacity_4300_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v_capacity_4300_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4306_ = v_capacity_4300_;
v_isShared_4307_ = v_isSharedCheck_4321_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_val_4304_);
lean_dec(v_capacity_4300_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4321_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v_zero_4308_; uint8_t v_isZero_4309_; 
v_zero_4308_ = lean_unsigned_to_nat(0u);
v_isZero_4309_ = lean_nat_dec_eq(v_val_4304_, v_zero_4308_);
if (v_isZero_4309_ == 1)
{
lean_object* v___x_4310_; lean_object* v___x_4312_; 
lean_dec(v_val_4304_);
v___x_4310_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 0, v___x_4310_);
v___x_4312_ = v___x_4306_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4310_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
else
{
lean_object* v_one_4314_; lean_object* v_n_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
v_one_4314_ = lean_unsigned_to_nat(1u);
v_n_4315_ = lean_nat_sub(v_val_4304_, v_one_4314_);
lean_dec(v_val_4304_);
v___x_4316_ = lean_nat_add(v_n_4315_, v_one_4314_);
lean_dec(v_n_4315_);
v___x_4317_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4316_);
if (v_isShared_4307_ == 0)
{
lean_ctor_set_tag(v___x_4306_, 2);
lean_ctor_set(v___x_4306_, 0, v___x_4317_);
v___x_4319_ = v___x_4306_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Std_CloseableChannel_new___redArg(v_capacity_4322_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4325_, lean_object* v_capacity_4326_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Std_CloseableChannel_new___redArg(v_capacity_4326_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4329_, lean_object* v_capacity_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Std_CloseableChannel_new(v_00_u03b1_4329_, v_capacity_4330_);
return v_res_4332_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4333_, lean_object* v_v_4334_){
_start:
{
switch(lean_obj_tag(v_ch_4333_))
{
case 0:
{
lean_object* v_ch_4336_; uint8_t v___x_4337_; 
v_ch_4336_ = lean_ctor_get(v_ch_4333_, 0);
lean_inc_ref(v_ch_4336_);
lean_dec_ref_known(v_ch_4333_, 1);
v___x_4337_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4336_, v_v_4334_);
return v___x_4337_;
}
case 1:
{
lean_object* v_ch_4338_; lean_object* v___x_4339_; uint8_t v___x_4340_; 
v_ch_4338_ = lean_ctor_get(v_ch_4333_, 0);
lean_inc_ref(v_ch_4338_);
lean_dec_ref_known(v_ch_4333_, 1);
v___x_4339_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4338_, v_v_4334_);
v___x_4340_ = lean_unbox(v___x_4339_);
lean_dec(v___x_4339_);
return v___x_4340_;
}
default: 
{
lean_object* v_ch_4341_; lean_object* v___x_4342_; uint8_t v___x_4343_; 
v_ch_4341_ = lean_ctor_get(v_ch_4333_, 0);
lean_inc_ref(v_ch_4341_);
lean_dec_ref_known(v_ch_4333_, 1);
v___x_4342_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4341_, v_v_4334_);
v___x_4343_ = lean_unbox(v___x_4342_);
lean_dec(v___x_4342_);
return v___x_4343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4344_, lean_object* v_v_4345_, lean_object* v_a_4346_){
_start:
{
uint8_t v_res_4347_; lean_object* v_r_4348_; 
v_res_4347_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4344_, v_v_4345_);
v_r_4348_ = lean_box(v_res_4347_);
return v_r_4348_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4349_, lean_object* v_ch_4350_, lean_object* v_v_4351_){
_start:
{
uint8_t v___x_4353_; 
v___x_4353_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4350_, v_v_4351_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4354_, lean_object* v_ch_4355_, lean_object* v_v_4356_, lean_object* v_a_4357_){
_start:
{
uint8_t v_res_4358_; lean_object* v_r_4359_; 
v_res_4358_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4354_, v_ch_4355_, v_v_4356_);
v_r_4359_ = lean_box(v_res_4358_);
return v_r_4359_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4360_, lean_object* v_v_4361_){
_start:
{
switch(lean_obj_tag(v_ch_4360_))
{
case 0:
{
lean_object* v_ch_4363_; lean_object* v___x_4364_; 
v_ch_4363_ = lean_ctor_get(v_ch_4360_, 0);
lean_inc_ref(v_ch_4363_);
lean_dec_ref_known(v_ch_4360_, 1);
v___x_4364_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4363_, v_v_4361_);
return v___x_4364_;
}
case 1:
{
lean_object* v_ch_4365_; lean_object* v___x_4366_; 
v_ch_4365_ = lean_ctor_get(v_ch_4360_, 0);
lean_inc_ref(v_ch_4365_);
lean_dec_ref_known(v_ch_4360_, 1);
v___x_4366_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4365_, v_v_4361_);
return v___x_4366_;
}
default: 
{
lean_object* v_ch_4367_; lean_object* v___x_4368_; 
v_ch_4367_ = lean_ctor_get(v_ch_4360_, 0);
lean_inc_ref(v_ch_4367_);
lean_dec_ref_known(v_ch_4360_, 1);
v___x_4368_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4367_, v_v_4361_);
return v___x_4368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4369_, lean_object* v_v_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Std_CloseableChannel_send___redArg(v_ch_4369_, v_v_4370_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4373_, lean_object* v_ch_4374_, lean_object* v_v_4375_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Std_CloseableChannel_send___redArg(v_ch_4374_, v_v_4375_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4378_, lean_object* v_ch_4379_, lean_object* v_v_4380_, lean_object* v_a_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l_Std_CloseableChannel_send(v_00_u03b1_4378_, v_ch_4379_, v_v_4380_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4383_){
_start:
{
switch(lean_obj_tag(v_ch_4383_))
{
case 0:
{
lean_object* v_ch_4385_; lean_object* v___x_4386_; 
v_ch_4385_ = lean_ctor_get(v_ch_4383_, 0);
lean_inc_ref(v_ch_4385_);
lean_dec_ref_known(v_ch_4383_, 1);
v___x_4386_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4385_);
return v___x_4386_;
}
case 1:
{
lean_object* v_ch_4387_; lean_object* v___x_4388_; 
v_ch_4387_ = lean_ctor_get(v_ch_4383_, 0);
lean_inc_ref(v_ch_4387_);
lean_dec_ref_known(v_ch_4383_, 1);
v___x_4388_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4387_);
return v___x_4388_;
}
default: 
{
lean_object* v_ch_4389_; lean_object* v___x_4390_; 
v_ch_4389_ = lean_ctor_get(v_ch_4383_, 0);
lean_inc_ref(v_ch_4389_);
lean_dec_ref_known(v_ch_4383_, 1);
v___x_4390_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4389_);
return v___x_4390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Std_CloseableChannel_close___redArg(v_ch_4391_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4394_, lean_object* v_ch_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Std_CloseableChannel_close___redArg(v_ch_4395_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4398_, lean_object* v_ch_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Std_CloseableChannel_close(v_00_u03b1_4398_, v_ch_4399_);
return v_res_4401_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4402_){
_start:
{
switch(lean_obj_tag(v_ch_4402_))
{
case 0:
{
lean_object* v_ch_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; 
v_ch_4404_ = lean_ctor_get(v_ch_4402_, 0);
lean_inc_ref(v_ch_4404_);
lean_dec_ref_known(v_ch_4402_, 1);
v___x_4405_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4404_);
v___x_4406_ = lean_unbox(v___x_4405_);
lean_dec(v___x_4405_);
return v___x_4406_;
}
case 1:
{
lean_object* v_ch_4407_; lean_object* v___x_4408_; uint8_t v___x_4409_; 
v_ch_4407_ = lean_ctor_get(v_ch_4402_, 0);
lean_inc_ref(v_ch_4407_);
lean_dec_ref_known(v_ch_4402_, 1);
v___x_4408_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4407_);
v___x_4409_ = lean_unbox(v___x_4408_);
lean_dec(v___x_4408_);
return v___x_4409_;
}
default: 
{
lean_object* v_ch_4410_; lean_object* v___x_4411_; uint8_t v___x_4412_; 
v_ch_4410_ = lean_ctor_get(v_ch_4402_, 0);
lean_inc_ref(v_ch_4410_);
lean_dec_ref_known(v_ch_4402_, 1);
v___x_4411_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4410_);
v___x_4412_ = lean_unbox(v___x_4411_);
lean_dec(v___x_4411_);
return v___x_4412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4413_, lean_object* v_a_4414_){
_start:
{
uint8_t v_res_4415_; lean_object* v_r_4416_; 
v_res_4415_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4413_);
v_r_4416_ = lean_box(v_res_4415_);
return v_r_4416_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4417_, lean_object* v_ch_4418_){
_start:
{
uint8_t v___x_4420_; 
v___x_4420_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4421_, lean_object* v_ch_4422_, lean_object* v_a_4423_){
_start:
{
uint8_t v_res_4424_; lean_object* v_r_4425_; 
v_res_4424_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4421_, v_ch_4422_);
v_r_4425_ = lean_box(v_res_4424_);
return v_r_4425_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4426_){
_start:
{
switch(lean_obj_tag(v_ch_4426_))
{
case 0:
{
lean_object* v_ch_4428_; lean_object* v___x_4429_; 
v_ch_4428_ = lean_ctor_get(v_ch_4426_, 0);
lean_inc_ref(v_ch_4428_);
lean_dec_ref_known(v_ch_4426_, 1);
v___x_4429_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4428_);
return v___x_4429_;
}
case 1:
{
lean_object* v_ch_4430_; lean_object* v___x_4431_; 
v_ch_4430_ = lean_ctor_get(v_ch_4426_, 0);
lean_inc_ref(v_ch_4430_);
lean_dec_ref_known(v_ch_4426_, 1);
v___x_4431_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4430_);
return v___x_4431_;
}
default: 
{
lean_object* v_ch_4432_; lean_object* v___x_4433_; 
v_ch_4432_ = lean_ctor_get(v_ch_4426_, 0);
lean_inc_ref(v_ch_4432_);
lean_dec_ref_known(v_ch_4426_, 1);
v___x_4433_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4432_);
return v___x_4433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4434_, lean_object* v_a_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4434_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4437_, lean_object* v_ch_4438_){
_start:
{
lean_object* v___x_4440_; 
v___x_4440_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4438_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4441_, lean_object* v_ch_4442_, lean_object* v_a_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4441_, v_ch_4442_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4445_){
_start:
{
switch(lean_obj_tag(v_ch_4445_))
{
case 0:
{
lean_object* v_ch_4447_; lean_object* v___x_4448_; 
v_ch_4447_ = lean_ctor_get(v_ch_4445_, 0);
lean_inc_ref(v_ch_4447_);
lean_dec_ref_known(v_ch_4445_, 1);
v___x_4448_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4447_);
return v___x_4448_;
}
case 1:
{
lean_object* v_ch_4449_; lean_object* v___x_4450_; 
v_ch_4449_ = lean_ctor_get(v_ch_4445_, 0);
lean_inc_ref(v_ch_4449_);
lean_dec_ref_known(v_ch_4445_, 1);
v___x_4450_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4449_);
return v___x_4450_;
}
default: 
{
lean_object* v_ch_4451_; lean_object* v___x_4452_; 
v_ch_4451_ = lean_ctor_get(v_ch_4445_, 0);
lean_inc_ref(v_ch_4451_);
lean_dec_ref_known(v_ch_4445_, 1);
v___x_4452_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4451_);
return v___x_4452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Std_CloseableChannel_recv___redArg(v_ch_4453_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4456_, lean_object* v_ch_4457_){
_start:
{
lean_object* v___x_4459_; 
v___x_4459_ = l_Std_CloseableChannel_recv___redArg(v_ch_4457_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4460_, lean_object* v_ch_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Std_CloseableChannel_recv(v_00_u03b1_4460_, v_ch_4461_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4464_){
_start:
{
switch(lean_obj_tag(v_ch_4464_))
{
case 0:
{
lean_object* v_ch_4465_; lean_object* v___x_4466_; 
v_ch_4465_ = lean_ctor_get(v_ch_4464_, 0);
lean_inc_ref(v_ch_4465_);
lean_dec_ref_known(v_ch_4464_, 1);
v___x_4466_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4465_);
return v___x_4466_;
}
case 1:
{
lean_object* v_ch_4467_; lean_object* v___x_4468_; 
v_ch_4467_ = lean_ctor_get(v_ch_4464_, 0);
lean_inc_ref(v_ch_4467_);
lean_dec_ref_known(v_ch_4464_, 1);
v___x_4468_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4467_);
return v___x_4468_;
}
default: 
{
lean_object* v_ch_4469_; lean_object* v___x_4470_; 
v_ch_4469_ = lean_ctor_get(v_ch_4464_, 0);
lean_inc_ref(v_ch_4469_);
lean_dec_ref_known(v_ch_4464_, 1);
v___x_4470_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4469_);
return v___x_4470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4471_, lean_object* v_ch_4472_){
_start:
{
lean_object* v___x_4473_; 
v___x_4473_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4472_);
return v___x_4473_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4474_ = lean_box(0);
v___x_4475_ = lean_task_pure(v___x_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4476_, lean_object* v_ch_4477_, lean_object* v_prio_4478_, lean_object* v_x_4479_){
_start:
{
if (lean_obj_tag(v_x_4479_) == 0)
{
lean_object* v___x_4481_; 
lean_dec(v_prio_4478_);
lean_dec_ref(v_ch_4477_);
lean_dec_ref(v_f_4476_);
v___x_4481_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4481_;
}
else
{
lean_object* v_val_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_val_4482_ = lean_ctor_get(v_x_4479_, 0);
lean_inc(v_val_4482_);
lean_dec_ref_known(v_x_4479_, 1);
lean_inc_ref(v_f_4476_);
v___x_4483_ = lean_apply_2(v_f_4476_, v_val_4482_, lean_box(0));
v___x_4484_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4476_, v_ch_4477_, v_prio_4478_);
return v___x_4484_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4485_, lean_object* v_ch_4486_, lean_object* v_prio_4487_, lean_object* v_x_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4485_, v_ch_4486_, v_prio_4487_, v_x_4488_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4491_, lean_object* v_ch_4492_, lean_object* v_prio_4493_){
_start:
{
lean_object* v___f_4495_; lean_object* v___x_4496_; uint8_t v___x_4497_; lean_object* v___x_4498_; 
lean_inc(v_prio_4493_);
lean_inc_ref(v_ch_4492_);
v___f_4495_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4495_, 0, v_f_4491_);
lean_closure_set(v___f_4495_, 1, v_ch_4492_);
lean_closure_set(v___f_4495_, 2, v_prio_4493_);
v___x_4496_ = l_Std_CloseableChannel_recv___redArg(v_ch_4492_);
v___x_4497_ = 0;
v___x_4498_ = lean_io_bind_task(v___x_4496_, v___f_4495_, v_prio_4493_, v___x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4499_, lean_object* v_ch_4500_, lean_object* v_prio_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4499_, v_ch_4500_, v_prio_4501_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4504_, lean_object* v_f_4505_, lean_object* v_ch_4506_, lean_object* v_prio_4507_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4505_, v_ch_4506_, v_prio_4507_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4510_, lean_object* v_f_4511_, lean_object* v_ch_4512_, lean_object* v_prio_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4510_, v_f_4511_, v_ch_4512_, v_prio_4513_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(lean_object* v_x_4516_){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4518_ = lean_box(0);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0___boxed(lean_object* v_x_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(v_x_4520_);
lean_dec_ref(v_x_4520_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg(){
_start:
{
lean_object* v___x_4529_; 
v___x_4529_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__2));
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object* v___dummy_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
return v_res_4531_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4533_, lean_object* v_inst_4534_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4536_, lean_object* v_inst_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4536_, v_inst_4537_);
lean_dec(v_inst_4537_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object* v_a_4539_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4540_, 0, v_a_4539_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object* v___f_4541_, lean_object* v_x_4542_){
_start:
{
if (lean_obj_tag(v_x_4542_) == 0)
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4552_; 
lean_dec_ref(v___f_4541_);
v_a_4544_ = lean_ctor_get(v_x_4542_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v_x_4542_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4546_ = v_x_4542_;
v_isShared_4547_ = v_isSharedCheck_4552_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v_x_4542_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4552_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
lean_object* v___x_4550_; 
v___x_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4549_);
return v___x_4550_;
}
}
}
else
{
lean_object* v_a_4553_; 
v_a_4553_ = lean_ctor_get(v_x_4542_, 0);
lean_inc(v_a_4553_);
lean_dec_ref_known(v_x_4542_, 1);
if (lean_obj_tag(v_a_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4562_; 
lean_dec_ref(v___f_4541_);
v_a_4554_ = lean_ctor_get(v_a_4553_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_a_4553_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4556_ = v_a_4553_;
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v_a_4553_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
lean_object* v___x_4560_; 
v___x_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
return v___x_4560_;
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4564_; uint8_t v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v_a_4563_ = lean_ctor_get(v_a_4553_, 0);
lean_inc(v_a_4563_);
lean_dec_ref_known(v_a_4553_, 1);
v___x_4564_ = lean_unsigned_to_nat(0u);
v___x_4565_ = 0;
v___x_4566_ = lean_task_map(v___f_4541_, v_a_4563_, v___x_4564_, v___x_4565_);
v___x_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
return v___x_4567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object* v___f_4568_, lean_object* v_x_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_4568_, v_x_4569_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object* v___f_4572_, lean_object* v_receiver_4573_){
_start:
{
lean_object* v___x_4575_; uint8_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4575_ = lean_unsigned_to_nat(0u);
v___x_4576_ = 0;
v___x_4577_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4573_);
v___x_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
v___x_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
v___x_4581_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4575_, v___x_4576_, v___x_4580_, v___f_4572_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object* v___f_4582_, lean_object* v_receiver_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_4582_, v_receiver_4583_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg(){
_start:
{
lean_object* v___f_4592_; 
v___f_4592_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__2));
return v___f_4592_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object* v___dummy_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
return v_res_4594_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4596_, lean_object* v_inst_4597_){
_start:
{
lean_object* v___x_4598_; 
v___x_4598_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0);
return v___x_4598_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4599_, lean_object* v_inst_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4599_, v_inst_4600_);
lean_dec(v_inst_4600_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v___f_4603_, lean_object* v_x_4604_){
_start:
{
if (lean_obj_tag(v_x_4604_) == 0)
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4614_; 
lean_dec_ref(v___f_4603_);
v_a_4606_ = lean_ctor_get(v_x_4604_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v_x_4604_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4608_ = v_x_4604_;
v_isShared_4609_ = v_isSharedCheck_4614_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v_x_4604_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4614_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v___x_4612_; 
v___x_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
return v___x_4612_;
}
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; uint8_t v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v_a_4615_ = lean_ctor_get(v_x_4604_, 0);
lean_inc(v_a_4615_);
lean_dec_ref_known(v_x_4604_, 1);
v___x_4616_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___closed__0));
v___x_4617_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4617_, 0, lean_box(0));
lean_closure_set(v___x_4617_, 1, lean_box(0));
lean_closure_set(v___x_4617_, 2, lean_box(0));
lean_closure_set(v___x_4617_, 3, v___x_4616_);
lean_closure_set(v___x_4617_, 4, v___f_4603_);
v___x_4618_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4618_, 0, lean_box(0));
lean_closure_set(v___x_4618_, 1, lean_box(0));
lean_closure_set(v___x_4618_, 2, lean_box(0));
lean_closure_set(v___x_4618_, 3, v___x_4617_);
v___x_4619_ = lean_unsigned_to_nat(0u);
v___x_4620_ = 0;
v___x_4621_ = lean_task_map(v___x_4618_, v_a_4615_, v___x_4619_, v___x_4620_);
v___x_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
return v___x_4622_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v___f_4623_, lean_object* v_x_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_4623_, v_x_4624_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v___f_4627_, lean_object* v_receiver_4628_, lean_object* v_x_4629_){
_start:
{
lean_object* v___x_4631_; uint8_t v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4631_ = lean_unsigned_to_nat(0u);
v___x_4632_ = 0;
v___x_4633_ = l_Std_CloseableChannel_send___redArg(v_receiver_4628_, v_x_4629_);
v___x_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
v___x_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
v___x_4636_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4631_, v___x_4632_, v___x_4635_, v___f_4627_);
return v___x_4636_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0___boxed(lean_object* v___f_4637_, lean_object* v_receiver_4638_, lean_object* v_x_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(v___f_4637_, v_receiver_4638_, v_x_4639_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v_x_4642_){
_start:
{
lean_object* v___x_4644_; 
v___x_4644_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v_x_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(v_x_4645_);
lean_dec_ref(v_x_4645_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(lean_object* v___f_4648_, lean_object* v_socket_4649_, lean_object* v_x_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = lean_apply_3(v___f_4648_, v_socket_4649_, v___y_4651_, lean_box(0));
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object* v___f_4654_, lean_object* v_socket_4655_, lean_object* v_x_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(v___f_4654_, v_socket_4655_, v_x_4656_, v___y_4657_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(lean_object* v___f_4660_, lean_object* v___x_4661_, lean_object* v_socket_4662_, lean_object* v_data_4663_){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v___x_4665_ = lean_unsigned_to_nat(0u);
v___x_4666_ = lean_array_get_size(v_data_4663_);
v___x_4667_ = lean_box(0);
v___x_4668_ = lean_nat_dec_lt(v___x_4665_, v___x_4666_);
if (v___x_4668_ == 0)
{
lean_object* v___x_4669_; 
lean_dec_ref(v_data_4663_);
lean_dec_ref(v_socket_4662_);
lean_dec_ref(v___x_4661_);
lean_dec_ref(v___f_4660_);
v___x_4669_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4669_;
}
else
{
lean_object* v___f_4670_; uint8_t v___x_4671_; 
v___f_4670_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4670_, 0, v___f_4660_);
lean_closure_set(v___f_4670_, 1, v_socket_4662_);
v___x_4671_ = lean_nat_dec_le(v___x_4666_, v___x_4666_);
if (v___x_4671_ == 0)
{
if (v___x_4668_ == 0)
{
lean_object* v___x_4672_; 
lean_dec_ref(v___f_4670_);
lean_dec_ref(v_data_4663_);
lean_dec_ref(v___x_4661_);
v___x_4672_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4672_;
}
else
{
size_t v___x_4673_; size_t v___x_4674_; lean_object* v___x_749__overap_4675_; lean_object* v___x_4676_; 
v___x_4673_ = ((size_t)0ULL);
v___x_4674_ = lean_usize_of_nat(v___x_4666_);
v___x_749__overap_4675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4661_, v___f_4670_, v_data_4663_, v___x_4673_, v___x_4674_, v___x_4667_);
v___x_4676_ = lean_apply_1(v___x_749__overap_4675_, lean_box(0));
return v___x_4676_;
}
}
else
{
size_t v___x_4677_; size_t v___x_4678_; lean_object* v___x_752__overap_4679_; lean_object* v___x_4680_; 
v___x_4677_ = ((size_t)0ULL);
v___x_4678_ = lean_usize_of_nat(v___x_4666_);
v___x_752__overap_4679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4661_, v___f_4670_, v_data_4663_, v___x_4677_, v___x_4678_, v___x_4667_);
v___x_4680_ = lean_apply_1(v___x_752__overap_4679_, lean_box(0));
return v___x_4680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object* v___f_4681_, lean_object* v___x_4682_, lean_object* v_socket_4683_, lean_object* v_data_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(v___f_4681_, v___x_4682_, v_socket_4683_, v_data_4684_);
return v_res_4686_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_4692_; 
v___x_4692_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_4692_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___x_4693_; lean_object* v___f_4694_; lean_object* v___f_4695_; 
v___x_4693_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_4694_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1));
v___f_4695_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4695_, 0, v___f_4694_);
lean_closure_set(v___f_4695_, 1, v___x_4693_);
return v___f_4695_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5(void){
_start:
{
lean_object* v___f_4696_; lean_object* v___f_4697_; lean_object* v___f_4698_; lean_object* v___x_4699_; 
v___f_4696_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_4697_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4);
v___f_4698_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1));
v___x_4699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4699_, 0, v___f_4698_);
lean_ctor_set(v___x_4699_, 1, v___f_4697_);
lean_ctor_set(v___x_4699_, 2, v___f_4696_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_4701_; 
v___x_4701_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
return v_res_4703_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4705_, lean_object* v_inst_4706_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4708_, lean_object* v_inst_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4708_, v_inst_4709_);
lean_dec(v_inst_4709_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4711_){
_start:
{
lean_inc_ref(v_ch_4711_);
return v_ch_4711_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l_Std_CloseableChannel_sync___redArg(v_ch_4712_);
lean_dec_ref(v_ch_4712_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4714_, lean_object* v_ch_4715_){
_start:
{
lean_inc_ref(v_ch_4715_);
return v_ch_4715_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4716_, lean_object* v_ch_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Std_CloseableChannel_sync(v_00_u03b1_4716_, v_ch_4717_);
lean_dec_ref(v_ch_4717_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Std_CloseableChannel_new___redArg(v_capacity_4719_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4722_, lean_object* v_a_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4722_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4725_, lean_object* v_capacity_4726_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = l_Std_CloseableChannel_new___redArg(v_capacity_4726_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4729_, lean_object* v_capacity_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4729_, v_capacity_4730_);
return v_res_4732_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4733_, lean_object* v_v_4734_){
_start:
{
uint8_t v___x_4736_; 
v___x_4736_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4733_, v_v_4734_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4737_, lean_object* v_v_4738_, lean_object* v_a_4739_){
_start:
{
uint8_t v_res_4740_; lean_object* v_r_4741_; 
v_res_4740_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4737_, v_v_4738_);
v_r_4741_ = lean_box(v_res_4740_);
return v_r_4741_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4742_, lean_object* v_ch_4743_, lean_object* v_v_4744_){
_start:
{
uint8_t v___x_4746_; 
v___x_4746_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4743_, v_v_4744_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4747_, lean_object* v_ch_4748_, lean_object* v_v_4749_, lean_object* v_a_4750_){
_start:
{
uint8_t v_res_4751_; lean_object* v_r_4752_; 
v_res_4751_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4747_, v_ch_4748_, v_v_4749_);
v_r_4752_ = lean_box(v_res_4751_);
return v_r_4752_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4753_, lean_object* v_v_4754_){
_start:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4756_ = l_Std_CloseableChannel_send___redArg(v_ch_4753_, v_v_4754_);
v___x_4757_ = lean_io_wait(v___x_4756_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4757_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4757_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
lean_ctor_set_tag(v___x_4760_, 1);
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
v_a_4766_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4757_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4757_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
lean_ctor_set_tag(v___x_4768_, 0);
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_4774_, lean_object* v_v_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4774_, v_v_4775_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_4778_, lean_object* v_ch_4779_, lean_object* v_v_4780_){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4779_, v_v_4780_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_4783_, lean_object* v_ch_4784_, lean_object* v_v_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_4783_, v_ch_4784_, v_v_4785_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_4788_){
_start:
{
lean_object* v___x_4790_; 
v___x_4790_ = l_Std_CloseableChannel_close___redArg(v_ch_4788_);
return v___x_4790_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_4791_, lean_object* v_a_4792_){
_start:
{
lean_object* v_res_4793_; 
v_res_4793_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_4791_);
return v_res_4793_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_4794_, lean_object* v_ch_4795_){
_start:
{
lean_object* v___x_4797_; 
v___x_4797_ = l_Std_CloseableChannel_close___redArg(v_ch_4795_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_4798_, lean_object* v_ch_4799_, lean_object* v_a_4800_){
_start:
{
lean_object* v_res_4801_; 
v_res_4801_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_4798_, v_ch_4799_);
return v_res_4801_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_4802_){
_start:
{
uint8_t v___x_4804_; 
v___x_4804_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4802_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_4805_, lean_object* v_a_4806_){
_start:
{
uint8_t v_res_4807_; lean_object* v_r_4808_; 
v_res_4807_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_4805_);
v_r_4808_ = lean_box(v_res_4807_);
return v_r_4808_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_4809_, lean_object* v_ch_4810_){
_start:
{
uint8_t v___x_4812_; 
v___x_4812_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4810_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_4813_, lean_object* v_ch_4814_, lean_object* v_a_4815_){
_start:
{
uint8_t v_res_4816_; lean_object* v_r_4817_; 
v_res_4816_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_4813_, v_ch_4814_);
v_r_4817_ = lean_box(v_res_4816_);
return v_r_4817_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_4818_){
_start:
{
lean_object* v___x_4820_; 
v___x_4820_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4818_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_4821_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_4824_, lean_object* v_ch_4825_){
_start:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4825_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_4828_, lean_object* v_ch_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_4828_, v_ch_4829_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_4832_){
_start:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = l_Std_CloseableChannel_recv___redArg(v_ch_4832_);
v___x_4835_ = lean_io_wait(v___x_4834_);
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_4836_, lean_object* v_a_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4836_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_4839_, lean_object* v_ch_4840_){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4840_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_4843_, lean_object* v_ch_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_4843_, v_ch_4844_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_4847_, lean_object* v_b_4848_, lean_object* v_f_4849_, lean_object* v_toBind_4850_, lean_object* v___f_4851_, lean_object* v_____do__lift_4852_){
_start:
{
if (lean_obj_tag(v_____do__lift_4852_) == 0)
{
lean_object* v___x_4853_; 
lean_dec(v___f_4851_);
lean_dec(v_toBind_4850_);
lean_dec(v_f_4849_);
v___x_4853_ = lean_apply_2(v_toPure_4847_, lean_box(0), v_b_4848_);
return v___x_4853_;
}
else
{
lean_object* v_val_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
lean_dec(v_toPure_4847_);
v_val_4854_ = lean_ctor_get(v_____do__lift_4852_, 0);
lean_inc(v_val_4854_);
lean_dec_ref_known(v_____do__lift_4852_, 1);
v___x_4855_ = lean_apply_2(v_f_4849_, v_val_4854_, v_b_4848_);
v___x_4856_ = lean_apply_4(v_toBind_4850_, lean_box(0), lean_box(0), v___x_4855_, v___f_4851_);
return v___x_4856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_4857_, lean_object* v_inst_4858_, lean_object* v_ch_4859_, lean_object* v_f_4860_, lean_object* v_b_4861_){
_start:
{
lean_object* v_toApplicative_4862_; lean_object* v_toBind_4863_; lean_object* v_toPure_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___f_4867_; lean_object* v___f_4868_; lean_object* v___x_4869_; 
v_toApplicative_4862_ = lean_ctor_get(v_inst_4857_, 0);
v_toBind_4863_ = lean_ctor_get(v_inst_4857_, 1);
lean_inc_n(v_toBind_4863_, 2);
v_toPure_4864_ = lean_ctor_get(v_toApplicative_4862_, 1);
lean_inc_n(v_toPure_4864_, 2);
lean_inc_ref(v_ch_4859_);
v___x_4865_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_4865_, 0, lean_box(0));
lean_closure_set(v___x_4865_, 1, v_ch_4859_);
lean_inc(v_inst_4858_);
v___x_4866_ = lean_apply_2(v_inst_4858_, lean_box(0), v___x_4865_);
lean_inc(v_f_4860_);
v___f_4867_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4867_, 0, v_toPure_4864_);
lean_closure_set(v___f_4867_, 1, v_inst_4857_);
lean_closure_set(v___f_4867_, 2, v_inst_4858_);
lean_closure_set(v___f_4867_, 3, v_ch_4859_);
lean_closure_set(v___f_4867_, 4, v_f_4860_);
v___f_4868_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_4868_, 0, v_toPure_4864_);
lean_closure_set(v___f_4868_, 1, v_b_4861_);
lean_closure_set(v___f_4868_, 2, v_f_4860_);
lean_closure_set(v___f_4868_, 3, v_toBind_4863_);
lean_closure_set(v___f_4868_, 4, v___f_4867_);
v___x_4869_ = lean_apply_4(v_toBind_4863_, lean_box(0), lean_box(0), v___x_4866_, v___f_4868_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_4870_, lean_object* v_inst_4871_, lean_object* v_inst_4872_, lean_object* v_ch_4873_, lean_object* v_f_4874_, lean_object* v_____do__lift_4875_){
_start:
{
if (lean_obj_tag(v_____do__lift_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4877_; 
lean_dec(v_f_4874_);
lean_dec_ref(v_ch_4873_);
lean_dec(v_inst_4872_);
lean_dec_ref(v_inst_4871_);
v_a_4876_ = lean_ctor_get(v_____do__lift_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v_____do__lift_4875_, 1);
v___x_4877_ = lean_apply_2(v_toPure_4870_, lean_box(0), v_a_4876_);
return v___x_4877_;
}
else
{
lean_object* v_a_4878_; lean_object* v___x_4879_; 
lean_dec(v_toPure_4870_);
v_a_4878_ = lean_ctor_get(v_____do__lift_4875_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v_____do__lift_4875_, 1);
v___x_4879_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4871_, v_inst_4872_, v_ch_4873_, v_f_4874_, v_a_4878_);
return v___x_4879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_4880_, lean_object* v_00_u03b1_4881_, lean_object* v_00_u03b2_4882_, lean_object* v_inst_4883_, lean_object* v_inst_4884_, lean_object* v_ch_4885_, lean_object* v_f_4886_, lean_object* v_b_4887_){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4883_, v_inst_4884_, v_ch_4885_, v_f_4886_, v_b_4887_);
return v___x_4888_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_4889_, lean_object* v_inst_4890_, lean_object* v_ch_4891_, lean_object* v_b_4892_, lean_object* v_f_4893_){
_start:
{
lean_object* v___x_4894_; 
v___x_4894_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4889_, v_inst_4890_, v_ch_4891_, v_f_4893_, v_b_4892_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_4895_, lean_object* v_00_u03b1_4896_, lean_object* v_inst_4897_, lean_object* v_inst_4898_, lean_object* v_00_u03b2_4899_, lean_object* v_ch_4900_, lean_object* v_b_4901_, lean_object* v_f_4902_){
_start:
{
lean_object* v___x_4903_; 
v___x_4903_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4897_, v_inst_4898_, v_ch_4900_, v_f_4902_, v_b_4901_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_4904_, lean_object* v_inst_4905_, lean_object* v_00_u03b2_4906_, lean_object* v_ch_4907_, lean_object* v_b_4908_, lean_object* v_f_4909_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4904_, v_inst_4905_, v_ch_4907_, v_f_4909_, v_b_4908_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_4911_, lean_object* v_inst_4912_){
_start:
{
lean_object* v___f_4913_; 
v___f_4913_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4913_, 0, v_inst_4911_);
lean_closure_set(v___f_4913_, 1, v_inst_4912_);
return v___f_4913_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_4914_, lean_object* v_00_u03b1_4915_, lean_object* v_inst_4916_, lean_object* v_inst_4917_){
_start:
{
lean_object* v___f_4918_; 
v___f_4918_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4918_, 0, v_inst_4916_);
lean_closure_set(v___f_4918_, 1, v_inst_4917_);
return v___f_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_4919_){
_start:
{
lean_object* v___x_4921_; 
v___x_4921_ = l_Std_CloseableChannel_new___redArg(v_capacity_4919_);
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_4922_, lean_object* v_a_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l_Std_Channel_new___redArg(v_capacity_4922_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_4925_, lean_object* v_capacity_4926_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Std_CloseableChannel_new___redArg(v_capacity_4926_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_4929_, lean_object* v_capacity_4930_, lean_object* v_a_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Std_Channel_new(v_00_u03b1_4929_, v_capacity_4930_);
return v_res_4932_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_4933_, lean_object* v_v_4934_){
_start:
{
uint8_t v___x_4936_; 
v___x_4936_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4933_, v_v_4934_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_4937_, lean_object* v_v_4938_, lean_object* v_a_4939_){
_start:
{
uint8_t v_res_4940_; lean_object* v_r_4941_; 
v_res_4940_ = l_Std_Channel_trySend___redArg(v_ch_4937_, v_v_4938_);
v_r_4941_ = lean_box(v_res_4940_);
return v_r_4941_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_4942_, lean_object* v_ch_4943_, lean_object* v_v_4944_){
_start:
{
uint8_t v___x_4946_; 
v___x_4946_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4943_, v_v_4944_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_4947_, lean_object* v_ch_4948_, lean_object* v_v_4949_, lean_object* v_a_4950_){
_start:
{
uint8_t v_res_4951_; lean_object* v_r_4952_; 
v_res_4951_ = l_Std_Channel_trySend(v_00_u03b1_4947_, v_ch_4948_, v_v_4949_);
v_r_4952_ = lean_box(v_res_4951_);
return v_r_4952_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = lean_box(0);
v___x_4954_ = lean_task_pure(v___x_4953_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_142__overap_4960_; lean_object* v___x_4961_; 
v___x_4957_ = l_instMonadBaseIO;
v___x_4958_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4959_ = l_instInhabitedOfMonad___redArg(v___x_4957_, v___x_4958_);
v___x_142__overap_4960_ = lean_panic_fn_borrowed(v___x_4959_, v_msg_4955_);
lean_dec(v___x_4959_);
v___x_4961_ = lean_apply_1(v___x_142__overap_4960_, lean_box(0));
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_4962_, lean_object* v___y_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_4962_);
return v_res_4964_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4968_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4969_ = lean_unsigned_to_nat(21u);
v___x_4970_ = lean_unsigned_to_nat(872u);
v___x_4971_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_4972_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4973_ = l_mkPanicMessageWithDecl(v___x_4972_, v___x_4971_, v___x_4970_, v___x_4969_, v___x_4968_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_4974_){
_start:
{
if (lean_obj_tag(v_x_4974_) == 0)
{
lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4976_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_4977_ = l_panic___at___00Std_Channel_send_spec__0(v___x_4976_);
return v___x_4977_;
}
else
{
lean_object* v___x_4978_; 
v___x_4978_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_4979_, lean_object* v___y_4980_){
_start:
{
lean_object* v_res_4981_; 
v_res_4981_ = l_Std_Channel_send___redArg___lam__0(v_x_4979_);
lean_dec_ref(v_x_4979_);
return v_res_4981_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_4983_, lean_object* v_v_4984_){
_start:
{
lean_object* v___f_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; uint8_t v___x_4989_; lean_object* v___x_4990_; 
v___f_4986_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_4987_ = l_Std_CloseableChannel_send___redArg(v_ch_4983_, v_v_4984_);
v___x_4988_ = lean_unsigned_to_nat(0u);
v___x_4989_ = 1;
v___x_4990_ = lean_io_bind_task(v___x_4987_, v___f_4986_, v___x_4988_, v___x_4989_);
return v___x_4990_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_4991_, lean_object* v_v_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Std_Channel_send___redArg(v_ch_4991_, v_v_4992_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_4995_, lean_object* v_ch_4996_, lean_object* v_v_4997_){
_start:
{
lean_object* v___x_4999_; 
v___x_4999_ = l_Std_Channel_send___redArg(v_ch_4996_, v_v_4997_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_5000_, lean_object* v_ch_5001_, lean_object* v_v_5002_, lean_object* v_a_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l_Std_Channel_send(v_00_u03b1_5000_, v_ch_5001_, v_v_5002_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_5005_){
_start:
{
lean_object* v___x_5007_; 
v___x_5007_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5005_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l_Std_Channel_tryRecv___redArg(v_ch_5008_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_5011_, lean_object* v_ch_5012_){
_start:
{
lean_object* v___x_5014_; 
v___x_5014_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5012_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_5015_, lean_object* v_ch_5016_, lean_object* v_a_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l_Std_Channel_tryRecv(v_00_u03b1_5015_, v_ch_5016_);
return v_res_5018_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5020_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_5021_ = lean_unsigned_to_nat(16u);
v___x_5022_ = lean_unsigned_to_nat(883u);
v___x_5023_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_5024_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_5025_ = l_mkPanicMessageWithDecl(v___x_5024_, v___x_5023_, v___x_5022_, v___x_5021_, v___x_5020_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_5026_, lean_object* v_x_5027_){
_start:
{
if (lean_obj_tag(v_x_5027_) == 0)
{
lean_object* v___x_5029_; lean_object* v___x_144__overap_5030_; lean_object* v___x_5031_; 
v___x_5029_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_144__overap_5030_ = l_panic___redArg(v___x_5026_, v___x_5029_);
v___x_5031_ = lean_apply_1(v___x_144__overap_5030_, lean_box(0));
return v___x_5031_;
}
else
{
lean_object* v_val_5032_; lean_object* v___x_5033_; 
v_val_5032_ = lean_ctor_get(v_x_5027_, 0);
lean_inc(v_val_5032_);
lean_dec_ref_known(v_x_5027_, 1);
v___x_5033_ = lean_task_pure(v_val_5032_);
return v___x_5033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_5034_, lean_object* v_x_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Std_Channel_recv___redArg___lam__0(v___x_5034_, v_x_5035_);
lean_dec(v___x_5034_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_5038_, lean_object* v_ch_5039_){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___f_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; uint8_t v___x_5047_; lean_object* v___x_5048_; 
v___x_5041_ = l_instMonadBaseIO;
v___x_5042_ = lean_task_pure(v_inst_5038_);
v___x_5043_ = l_instInhabitedOfMonad___redArg(v___x_5041_, v___x_5042_);
v___f_5044_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5044_, 0, v___x_5043_);
v___x_5045_ = l_Std_CloseableChannel_recv___redArg(v_ch_5039_);
v___x_5046_ = lean_unsigned_to_nat(0u);
v___x_5047_ = 1;
v___x_5048_ = lean_io_bind_task(v___x_5045_, v___f_5044_, v___x_5046_, v___x_5047_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_5049_, lean_object* v_ch_5050_, lean_object* v_a_5051_){
_start:
{
lean_object* v_res_5052_; 
v_res_5052_ = l_Std_Channel_recv___redArg(v_inst_5049_, v_ch_5050_);
return v_res_5052_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_5053_, lean_object* v_inst_5054_, lean_object* v_ch_5055_){
_start:
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Std_Channel_recv___redArg(v_inst_5054_, v_ch_5055_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_5058_, lean_object* v_inst_5059_, lean_object* v_ch_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Std_Channel_recv(v_00_u03b1_5058_, v_inst_5059_, v_ch_5060_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_5063_){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5065_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5063_);
v___x_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5065_);
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5068_);
return v_res_5070_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5074_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_5075_ = lean_unsigned_to_nat(14u);
v___x_5076_ = lean_unsigned_to_nat(22u);
v___x_5077_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_5078_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_5079_ = l_mkPanicMessageWithDecl(v___x_5078_, v___x_5077_, v___x_5076_, v___x_5075_, v___x_5074_);
return v___x_5079_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_5080_, lean_object* v_inst_5081_, lean_object* v_x_5082_){
_start:
{
lean_object* v___y_5085_; lean_object* v___y_5089_; 
if (lean_obj_tag(v_x_5082_) == 0)
{
lean_object* v___x_5091_; lean_object* v___x_5092_; 
v___x_5091_ = lean_box(0);
v___x_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5092_, 0, v___x_5091_);
return v___x_5092_;
}
else
{
lean_object* v_val_5093_; 
v_val_5093_ = lean_ctor_get(v_x_5082_, 0);
lean_inc(v_val_5093_);
lean_dec_ref_known(v_x_5082_, 1);
if (lean_obj_tag(v_val_5093_) == 0)
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
v_a_5094_ = lean_ctor_get(v_val_5093_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v_val_5093_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v_val_5093_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v_val_5093_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
v___y_5085_ = v___x_5099_;
goto v___jp_5084_;
}
}
}
else
{
lean_object* v_a_5102_; 
v_a_5102_ = lean_ctor_get(v_val_5093_, 0);
lean_inc(v_a_5102_);
lean_dec_ref_known(v_val_5093_, 1);
if (lean_obj_tag(v_a_5102_) == 0)
{
lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5103_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5104_ = l_panic___redArg(v_inst_5081_, v___x_5103_);
v___y_5089_ = v___x_5104_;
goto v___jp_5088_;
}
else
{
lean_object* v_val_5105_; 
v_val_5105_ = lean_ctor_get(v_a_5102_, 0);
lean_inc(v_val_5105_);
lean_dec_ref_known(v_a_5102_, 1);
v___y_5089_ = v_val_5105_;
goto v___jp_5088_;
}
}
}
v___jp_5084_:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5086_ = lean_io_promise_resolve(v___y_5085_, v_promise_5080_);
v___x_5087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5087_, 0, v___x_5086_);
return v___x_5087_;
}
v___jp_5088_:
{
lean_object* v___x_5090_; 
v___x_5090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5090_, 0, v___y_5089_);
v___y_5085_ = v___x_5090_;
goto v___jp_5084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5106_, lean_object* v_inst_5107_, lean_object* v_x_5108_, lean_object* v___y_5109_){
_start:
{
lean_object* v_res_5110_; 
v_res_5110_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5106_, v_inst_5107_, v_x_5108_);
lean_dec(v_inst_5107_);
lean_dec(v_promise_5106_);
return v_res_5110_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5111_, lean_object* v___f_5112_, lean_object* v_x_5113_){
_start:
{
lean_object* v_val_5116_; 
if (lean_obj_tag(v_x_5113_) == 0)
{
lean_object* v___x_5118_; 
lean_dec_ref(v___f_5112_);
v___x_5118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5118_, 0, v_x_5113_);
return v___x_5118_;
}
else
{
lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5134_; 
v_isSharedCheck_5134_ = !lean_is_exclusive(v_x_5113_);
if (v_isSharedCheck_5134_ == 0)
{
lean_object* v_unused_5135_; 
v_unused_5135_ = lean_ctor_get(v_x_5113_, 0);
lean_dec(v_unused_5135_);
v___x_5120_ = v_x_5113_;
v_isShared_5121_ = v_isSharedCheck_5134_;
goto v_resetjp_5119_;
}
else
{
lean_dec(v_x_5113_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5134_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; uint8_t v___x_5124_; lean_object* v___x_5125_; 
v___x_5122_ = lean_io_promise_result_opt(v_a_5111_);
v___x_5123_ = lean_unsigned_to_nat(0u);
v___x_5124_ = 1;
v___x_5125_ = l_EIO_chainTask___redArg(v___x_5122_, v___f_5112_, v___x_5123_, v___x_5124_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5128_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v___x_5125_, 1);
if (v_isShared_5121_ == 0)
{
lean_ctor_set(v___x_5120_, 0, v_a_5126_);
v___x_5128_ = v___x_5120_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5126_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
v_val_5116_ = v___x_5128_;
goto v___jp_5115_;
}
}
else
{
lean_object* v_a_5130_; lean_object* v___x_5132_; 
v_a_5130_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5125_, 1);
if (v_isShared_5121_ == 0)
{
lean_ctor_set_tag(v___x_5120_, 0);
lean_ctor_set(v___x_5120_, 0, v_a_5130_);
v___x_5132_ = v___x_5120_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5130_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
v_val_5116_ = v___x_5132_;
goto v___jp_5115_;
}
}
}
}
v___jp_5115_:
{
lean_object* v___x_5117_; 
v___x_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5117_, 0, v_val_5116_);
return v___x_5117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5136_, lean_object* v___f_5137_, lean_object* v_x_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5136_, v___f_5137_, v_x_5138_);
lean_dec(v_a_5136_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5141_, lean_object* v___f_5142_, lean_object* v_finished_5143_, lean_object* v_x_5144_){
_start:
{
if (lean_obj_tag(v_x_5144_) == 0)
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5154_; 
lean_dec(v_finished_5143_);
lean_dec_ref(v___f_5142_);
lean_dec_ref(v_sel_5141_);
v_a_5146_ = lean_ctor_get(v_x_5144_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v_x_5144_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5148_ = v_x_5144_;
v_isShared_5149_ = v_isSharedCheck_5154_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v_x_5144_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5154_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5146_);
v___x_5151_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
lean_object* v___x_5152_; 
v___x_5152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5152_, 0, v___x_5151_);
return v___x_5152_;
}
}
}
else
{
lean_object* v_a_5155_; lean_object* v_registerFn_5156_; lean_object* v___f_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; uint8_t v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v_a_5155_ = lean_ctor_get(v_x_5144_, 0);
lean_inc_n(v_a_5155_, 2);
lean_dec_ref_known(v_x_5144_, 1);
v_registerFn_5156_ = lean_ctor_get(v_sel_5141_, 1);
lean_inc_ref(v_registerFn_5156_);
lean_dec_ref(v_sel_5141_);
v___f_5157_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5157_, 0, v_a_5155_);
lean_closure_set(v___f_5157_, 1, v___f_5142_);
v___x_5158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5158_, 0, v_finished_5143_);
lean_ctor_set(v___x_5158_, 1, v_a_5155_);
v___x_5159_ = lean_unsigned_to_nat(0u);
v___x_5160_ = 0;
v___x_5161_ = lean_apply_2(v_registerFn_5156_, v___x_5158_, lean_box(0));
v___x_5162_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5159_, v___x_5160_, v___x_5161_, v___f_5157_);
return v___x_5162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5163_, lean_object* v___f_5164_, lean_object* v_finished_5165_, lean_object* v_x_5166_, lean_object* v___y_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5163_, v___f_5164_, v_finished_5165_, v_x_5166_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5169_, lean_object* v_sel_5170_, lean_object* v_waiter_5171_){
_start:
{
lean_object* v_finished_5173_; lean_object* v_promise_5174_; lean_object* v___f_5175_; lean_object* v___f_5176_; lean_object* v___x_5177_; uint8_t v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
v_finished_5173_ = lean_ctor_get(v_waiter_5171_, 0);
lean_inc(v_finished_5173_);
v_promise_5174_ = lean_ctor_get(v_waiter_5171_, 1);
lean_inc(v_promise_5174_);
lean_dec_ref(v_waiter_5171_);
v___f_5175_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5175_, 0, v_promise_5174_);
lean_closure_set(v___f_5175_, 1, v_inst_5169_);
v___f_5176_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5176_, 0, v_sel_5170_);
lean_closure_set(v___f_5176_, 1, v___f_5175_);
lean_closure_set(v___f_5176_, 2, v_finished_5173_);
v___x_5177_ = lean_unsigned_to_nat(0u);
v___x_5178_ = 0;
v___x_5179_ = lean_io_promise_new();
v___x_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5179_);
v___x_5181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5180_);
v___x_5182_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5177_, v___x_5178_, v___x_5181_, v___f_5176_);
return v___x_5182_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5183_, lean_object* v_sel_5184_, lean_object* v_waiter_5185_, lean_object* v___y_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5183_, v_sel_5184_, v_waiter_5185_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5188_, lean_object* v_ch_5189_){
_start:
{
lean_object* v_sel_5190_; lean_object* v_unregisterFn_5191_; lean_object* v___f_5192_; lean_object* v___f_5193_; lean_object* v___x_5194_; 
lean_inc_ref(v_ch_5189_);
v_sel_5190_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5189_);
v_unregisterFn_5191_ = lean_ctor_get(v_sel_5190_, 2);
lean_inc_ref(v_unregisterFn_5191_);
v___f_5192_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5192_, 0, v_ch_5189_);
v___f_5193_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5193_, 0, v_inst_5188_);
lean_closure_set(v___f_5193_, 1, v_sel_5190_);
v___x_5194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5194_, 0, v___f_5192_);
lean_ctor_set(v___x_5194_, 1, v___f_5193_);
lean_ctor_set(v___x_5194_, 2, v_unregisterFn_5191_);
return v___x_5194_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5195_, lean_object* v_inst_5196_, lean_object* v_ch_5197_){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = l_Std_Channel_recvSelector___redArg(v_inst_5196_, v_ch_5197_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5199_, lean_object* v_inst_5200_, lean_object* v_ch_5201_, lean_object* v_prio_5202_, lean_object* v_v_5203_, lean_object* v___y_5204_){
_start:
{
lean_object* v_res_5205_; 
v_res_5205_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5199_, v_inst_5200_, v_ch_5201_, v_prio_5202_, v_v_5203_);
return v_res_5205_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5206_, lean_object* v_f_5207_, lean_object* v_ch_5208_, lean_object* v_prio_5209_){
_start:
{
lean_object* v___f_5211_; lean_object* v___x_5212_; uint8_t v___x_5213_; lean_object* v___x_5214_; 
lean_inc(v_prio_5209_);
lean_inc_ref(v_ch_5208_);
lean_inc(v_inst_5206_);
v___f_5211_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5211_, 0, v_f_5207_);
lean_closure_set(v___f_5211_, 1, v_inst_5206_);
lean_closure_set(v___f_5211_, 2, v_ch_5208_);
lean_closure_set(v___f_5211_, 3, v_prio_5209_);
v___x_5212_ = l_Std_Channel_recv___redArg(v_inst_5206_, v_ch_5208_);
v___x_5213_ = 0;
v___x_5214_ = lean_io_bind_task(v___x_5212_, v___f_5211_, v_prio_5209_, v___x_5213_);
return v___x_5214_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5215_, lean_object* v_inst_5216_, lean_object* v_ch_5217_, lean_object* v_prio_5218_, lean_object* v_v_5219_){
_start:
{
lean_object* v___x_5221_; lean_object* v___x_5222_; 
lean_inc_ref(v_f_5215_);
v___x_5221_ = lean_apply_2(v_f_5215_, v_v_5219_, lean_box(0));
v___x_5222_ = l_Std_Channel_forAsync___redArg(v_inst_5216_, v_f_5215_, v_ch_5217_, v_prio_5218_);
return v___x_5222_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5223_, lean_object* v_f_5224_, lean_object* v_ch_5225_, lean_object* v_prio_5226_, lean_object* v_a_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l_Std_Channel_forAsync___redArg(v_inst_5223_, v_f_5224_, v_ch_5225_, v_prio_5226_);
return v_res_5228_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5229_, lean_object* v_inst_5230_, lean_object* v_f_5231_, lean_object* v_ch_5232_, lean_object* v_prio_5233_){
_start:
{
lean_object* v___x_5235_; 
v___x_5235_ = l_Std_Channel_forAsync___redArg(v_inst_5230_, v_f_5231_, v_ch_5232_, v_prio_5233_);
return v___x_5235_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5236_, lean_object* v_inst_5237_, lean_object* v_f_5238_, lean_object* v_ch_5239_, lean_object* v_prio_5240_, lean_object* v_a_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l_Std_Channel_forAsync(v_00_u03b1_5236_, v_inst_5237_, v_f_5238_, v_ch_5239_, v_prio_5240_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5243_, lean_object* v_channel_5244_){
_start:
{
lean_object* v___x_5245_; 
v___x_5245_ = l_Std_Channel_recvSelector___redArg(v_inst_5243_, v_channel_5244_);
return v___x_5245_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5246_){
_start:
{
lean_object* v___f_5247_; lean_object* v___f_5248_; lean_object* v___x_5249_; 
v___f_5247_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5247_, 0, v_inst_5246_);
v___f_5248_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__1));
v___x_5249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5249_, 0, v___f_5247_);
lean_ctor_set(v___x_5249_, 1, v___f_5248_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5250_, lean_object* v_inst_5251_){
_start:
{
lean_object* v___x_5252_; 
v___x_5252_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5251_);
return v___x_5252_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5253_){
_start:
{
lean_object* v___x_5254_; 
v___x_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5254_, 0, v_a_5253_);
return v___x_5254_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5255_, lean_object* v_x_5256_){
_start:
{
if (lean_obj_tag(v_x_5256_) == 0)
{
lean_object* v_a_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5266_; 
lean_dec_ref(v___f_5255_);
v_a_5258_ = lean_ctor_get(v_x_5256_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v_x_5256_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5260_ = v_x_5256_;
v_isShared_5261_ = v_isSharedCheck_5266_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_a_5258_);
lean_dec(v_x_5256_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5266_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v___x_5263_; 
if (v_isShared_5261_ == 0)
{
v___x_5263_ = v___x_5260_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5258_);
v___x_5263_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
lean_object* v___x_5264_; 
v___x_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5263_);
return v___x_5264_;
}
}
}
else
{
lean_object* v_a_5267_; 
v_a_5267_ = lean_ctor_get(v_x_5256_, 0);
lean_inc(v_a_5267_);
lean_dec_ref_known(v_x_5256_, 1);
if (lean_obj_tag(v_a_5267_) == 0)
{
lean_object* v_a_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5276_; 
lean_dec_ref(v___f_5255_);
v_a_5268_ = lean_ctor_get(v_a_5267_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v_a_5267_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5270_ = v_a_5267_;
v_isShared_5271_ = v_isSharedCheck_5276_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_a_5268_);
lean_dec(v_a_5267_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5276_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5273_; 
if (v_isShared_5271_ == 0)
{
v___x_5273_ = v___x_5270_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5268_);
v___x_5273_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
lean_object* v___x_5274_; 
v___x_5274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5273_);
return v___x_5274_;
}
}
}
else
{
lean_object* v_a_5277_; lean_object* v___x_5278_; uint8_t v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v_a_5277_ = lean_ctor_get(v_a_5267_, 0);
lean_inc(v_a_5277_);
lean_dec_ref_known(v_a_5267_, 1);
v___x_5278_ = lean_unsigned_to_nat(0u);
v___x_5279_ = 0;
v___x_5280_ = lean_task_map(v___f_5255_, v_a_5277_, v___x_5278_, v___x_5279_);
v___x_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5281_, 0, v___x_5280_);
return v___x_5281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5282_, lean_object* v_x_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5282_, v_x_5283_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5286_, lean_object* v___f_5287_, lean_object* v_receiver_5288_){
_start:
{
lean_object* v___x_5290_; uint8_t v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5290_ = lean_unsigned_to_nat(0u);
v___x_5291_ = 0;
v___x_5292_ = l_Std_Channel_recv___redArg(v_inst_5286_, v_receiver_5288_);
v___x_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
v___x_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
v___x_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5294_);
v___x_5296_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5290_, v___x_5291_, v___x_5295_, v___f_5287_);
return v___x_5296_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5297_, lean_object* v___f_5298_, lean_object* v_receiver_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5297_, v___f_5298_, v_receiver_5299_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5305_){
_start:
{
lean_object* v___f_5306_; lean_object* v___f_5307_; 
v___f_5306_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5307_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5307_, 0, v_inst_5305_);
lean_closure_set(v___f_5307_, 1, v___f_5306_);
return v___f_5307_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5308_, lean_object* v_inst_5309_){
_start:
{
lean_object* v___x_5310_; 
v___x_5310_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5309_);
return v___x_5310_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v_a_5311_){
_start:
{
lean_object* v___x_5312_; 
v___x_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5312_, 0, v_a_5311_);
return v___x_5312_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v___f_5313_, lean_object* v_x_5314_){
_start:
{
if (lean_obj_tag(v_x_5314_) == 0)
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5324_; 
lean_dec_ref(v___f_5313_);
v_a_5316_ = lean_ctor_get(v_x_5314_, 0);
v_isSharedCheck_5324_ = !lean_is_exclusive(v_x_5314_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5318_ = v_x_5314_;
v_isShared_5319_ = v_isSharedCheck_5324_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v_x_5314_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5324_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
lean_object* v___x_5322_; 
v___x_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5322_, 0, v___x_5321_);
return v___x_5322_;
}
}
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5326_; uint8_t v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; 
v_a_5325_ = lean_ctor_get(v_x_5314_, 0);
lean_inc(v_a_5325_);
lean_dec_ref_known(v_x_5314_, 1);
v___x_5326_ = lean_unsigned_to_nat(0u);
v___x_5327_ = 0;
v___x_5328_ = lean_task_map(v___f_5313_, v_a_5325_, v___x_5326_, v___x_5327_);
v___x_5329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5328_);
return v___x_5329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5330_, lean_object* v_x_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v_res_5333_; 
v_res_5333_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_5330_, v_x_5331_);
return v_res_5333_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v___f_5334_, lean_object* v_receiver_5335_, lean_object* v_x_5336_){
_start:
{
lean_object* v___x_5338_; uint8_t v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; 
v___x_5338_ = lean_unsigned_to_nat(0u);
v___x_5339_ = 0;
v___x_5340_ = l_Std_Channel_send___redArg(v_receiver_5335_, v_x_5336_);
v___x_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5340_);
v___x_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5342_, 0, v___x_5341_);
v___x_5343_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5338_, v___x_5339_, v___x_5342_, v___f_5334_);
return v___x_5343_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5344_, lean_object* v_receiver_5345_, lean_object* v_x_5346_, lean_object* v___y_5347_){
_start:
{
lean_object* v_res_5348_; 
v_res_5348_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(v___f_5344_, v_receiver_5345_, v_x_5346_);
return v_res_5348_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_5354_; lean_object* v___f_5355_; lean_object* v___f_5356_; 
v___x_5354_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5355_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5356_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5356_, 0, v___f_5355_);
lean_closure_set(v___f_5356_, 1, v___x_5354_);
return v___f_5356_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___f_5357_; lean_object* v___f_5358_; lean_object* v___f_5359_; lean_object* v___x_5360_; 
v___f_5357_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5358_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5359_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2));
v___x_5360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5360_, 0, v___f_5359_);
lean_ctor_set(v___x_5360_, 1, v___f_5358_);
lean_ctor_set(v___x_5360_, 2, v___f_5357_);
return v___x_5360_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_5362_; 
v___x_5362_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg();
return v_res_5364_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5365_; 
v___x_5365_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg();
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5366_, lean_object* v_inst_5367_){
_start:
{
lean_object* v___x_5368_; 
v___x_5368_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__0, &l_Std_Channel_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__0);
return v___x_5368_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5369_, lean_object* v_inst_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_5369_, v_inst_5370_);
lean_dec(v_inst_5370_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object* v_ch_5372_){
_start:
{
lean_inc_ref(v_ch_5372_);
return v_ch_5372_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object* v_ch_5373_){
_start:
{
lean_object* v_res_5374_; 
v_res_5374_ = l_Std_Channel_sync___redArg(v_ch_5373_);
lean_dec_ref(v_ch_5373_);
return v_res_5374_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object* v_00_u03b1_5375_, lean_object* v_ch_5376_){
_start:
{
lean_inc_ref(v_ch_5376_);
return v_ch_5376_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object* v_00_u03b1_5377_, lean_object* v_ch_5378_){
_start:
{
lean_object* v_res_5379_; 
v_res_5379_ = l_Std_Channel_sync(v_00_u03b1_5377_, v_ch_5378_);
lean_dec_ref(v_ch_5378_);
return v_res_5379_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg(lean_object* v_capacity_5380_){
_start:
{
lean_object* v___x_5382_; 
v___x_5382_ = l_Std_CloseableChannel_new___redArg(v_capacity_5380_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object* v_capacity_5383_, lean_object* v_a_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l_Std_Channel_Sync_new___redArg(v_capacity_5383_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new(lean_object* v_00_u03b1_5386_, lean_object* v_capacity_5387_){
_start:
{
lean_object* v___x_5389_; 
v___x_5389_ = l_Std_CloseableChannel_new___redArg(v_capacity_5387_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object* v_00_u03b1_5390_, lean_object* v_capacity_5391_, lean_object* v_a_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l_Std_Channel_Sync_new(v_00_u03b1_5390_, v_capacity_5391_);
return v_res_5393_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object* v_ch_5394_, lean_object* v_v_5395_){
_start:
{
uint8_t v___x_5397_; 
v___x_5397_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5394_, v_v_5395_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object* v_ch_5398_, lean_object* v_v_5399_, lean_object* v_a_5400_){
_start:
{
uint8_t v_res_5401_; lean_object* v_r_5402_; 
v_res_5401_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5398_, v_v_5399_);
v_r_5402_ = lean_box(v_res_5401_);
return v_r_5402_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend(lean_object* v_00_u03b1_5403_, lean_object* v_ch_5404_, lean_object* v_v_5405_){
_start:
{
uint8_t v___x_5407_; 
v___x_5407_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5404_, v_v_5405_);
return v___x_5407_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object* v_00_u03b1_5408_, lean_object* v_ch_5409_, lean_object* v_v_5410_, lean_object* v_a_5411_){
_start:
{
uint8_t v_res_5412_; lean_object* v_r_5413_; 
v_res_5412_ = l_Std_Channel_Sync_trySend(v_00_u03b1_5408_, v_ch_5409_, v_v_5410_);
v_r_5413_ = lean_box(v_res_5412_);
return v_r_5413_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg(lean_object* v_ch_5414_, lean_object* v_v_5415_){
_start:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; 
v___x_5417_ = l_Std_Channel_send___redArg(v_ch_5414_, v_v_5415_);
v___x_5418_ = lean_io_wait(v___x_5417_);
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object* v_ch_5419_, lean_object* v_v_5420_, lean_object* v_a_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l_Std_Channel_Sync_send___redArg(v_ch_5419_, v_v_5420_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send(lean_object* v_00_u03b1_5423_, lean_object* v_ch_5424_, lean_object* v_v_5425_){
_start:
{
lean_object* v___x_5427_; 
v___x_5427_ = l_Std_Channel_Sync_send___redArg(v_ch_5424_, v_v_5425_);
return v___x_5427_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object* v_00_u03b1_5428_, lean_object* v_ch_5429_, lean_object* v_v_5430_, lean_object* v_a_5431_){
_start:
{
lean_object* v_res_5432_; 
v_res_5432_ = l_Std_Channel_Sync_send(v_00_u03b1_5428_, v_ch_5429_, v_v_5430_);
return v_res_5432_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object* v_ch_5433_){
_start:
{
lean_object* v___x_5435_; 
v___x_5435_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5433_);
return v___x_5435_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5436_, lean_object* v_a_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5436_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv(lean_object* v_00_u03b1_5439_, lean_object* v_ch_5440_){
_start:
{
lean_object* v___x_5442_; 
v___x_5442_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5440_);
return v___x_5442_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5443_, lean_object* v_ch_5444_, lean_object* v_a_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_5443_, v_ch_5444_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg(lean_object* v_inst_5447_, lean_object* v_ch_5448_){
_start:
{
lean_object* v___x_5450_; lean_object* v___x_5451_; 
v___x_5450_ = l_Std_Channel_recv___redArg(v_inst_5447_, v_ch_5448_);
v___x_5451_ = lean_io_wait(v___x_5450_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object* v_inst_5452_, lean_object* v_ch_5453_, lean_object* v_a_5454_){
_start:
{
lean_object* v_res_5455_; 
v_res_5455_ = l_Std_Channel_Sync_recv___redArg(v_inst_5452_, v_ch_5453_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv(lean_object* v_00_u03b1_5456_, lean_object* v_inst_5457_, lean_object* v_ch_5458_){
_start:
{
lean_object* v___x_5460_; 
v___x_5460_ = l_Std_Channel_Sync_recv___redArg(v_inst_5457_, v_ch_5458_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object* v_00_u03b1_5461_, lean_object* v_inst_5462_, lean_object* v_ch_5463_, lean_object* v_a_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l_Std_Channel_Sync_recv(v_00_u03b1_5461_, v_inst_5462_, v_ch_5463_);
return v_res_5465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object* v_f_5466_, lean_object* v_b_5467_, lean_object* v_toBind_5468_, lean_object* v___f_5469_, lean_object* v_a_5470_){
_start:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5471_ = lean_apply_2(v_f_5466_, v_a_5470_, v_b_5467_);
v___x_5472_ = lean_apply_4(v_toBind_5468_, lean_box(0), lean_box(0), v___x_5471_, v___f_5469_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object* v_inst_5473_, lean_object* v_inst_5474_, lean_object* v_inst_5475_, lean_object* v_ch_5476_, lean_object* v_f_5477_, lean_object* v_b_5478_){
_start:
{
lean_object* v_toApplicative_5479_; lean_object* v_toBind_5480_; lean_object* v_toPure_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___f_5484_; lean_object* v___f_5485_; lean_object* v___x_5486_; 
v_toApplicative_5479_ = lean_ctor_get(v_inst_5474_, 0);
v_toBind_5480_ = lean_ctor_get(v_inst_5474_, 1);
lean_inc_n(v_toBind_5480_, 2);
v_toPure_5481_ = lean_ctor_get(v_toApplicative_5479_, 1);
lean_inc(v_toPure_5481_);
lean_inc_ref(v_ch_5476_);
lean_inc(v_inst_5473_);
v___x_5482_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_recv___boxed), 4, 3);
lean_closure_set(v___x_5482_, 0, lean_box(0));
lean_closure_set(v___x_5482_, 1, v_inst_5473_);
lean_closure_set(v___x_5482_, 2, v_ch_5476_);
lean_inc(v_inst_5475_);
v___x_5483_ = lean_apply_2(v_inst_5475_, lean_box(0), v___x_5482_);
lean_inc(v_f_5477_);
v___f_5484_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5484_, 0, v_toPure_5481_);
lean_closure_set(v___f_5484_, 1, v_inst_5473_);
lean_closure_set(v___f_5484_, 2, v_inst_5474_);
lean_closure_set(v___f_5484_, 3, v_inst_5475_);
lean_closure_set(v___f_5484_, 4, v_ch_5476_);
lean_closure_set(v___f_5484_, 5, v_f_5477_);
v___f_5485_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1), 5, 4);
lean_closure_set(v___f_5485_, 0, v_f_5477_);
lean_closure_set(v___f_5485_, 1, v_b_5478_);
lean_closure_set(v___f_5485_, 2, v_toBind_5480_);
lean_closure_set(v___f_5485_, 3, v___f_5484_);
v___x_5486_ = lean_apply_4(v_toBind_5480_, lean_box(0), lean_box(0), v___x_5483_, v___f_5485_);
return v___x_5486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5487_, lean_object* v_inst_5488_, lean_object* v_inst_5489_, lean_object* v_inst_5490_, lean_object* v_ch_5491_, lean_object* v_f_5492_, lean_object* v_____do__lift_5493_){
_start:
{
if (lean_obj_tag(v_____do__lift_5493_) == 0)
{
lean_object* v_a_5494_; lean_object* v___x_5495_; 
lean_dec(v_f_5492_);
lean_dec_ref(v_ch_5491_);
lean_dec(v_inst_5490_);
lean_dec_ref(v_inst_5489_);
lean_dec(v_inst_5488_);
v_a_5494_ = lean_ctor_get(v_____do__lift_5493_, 0);
lean_inc(v_a_5494_);
lean_dec_ref_known(v_____do__lift_5493_, 1);
v___x_5495_ = lean_apply_2(v_toPure_5487_, lean_box(0), v_a_5494_);
return v___x_5495_;
}
else
{
lean_object* v_a_5496_; lean_object* v___x_5497_; 
lean_dec(v_toPure_5487_);
v_a_5496_ = lean_ctor_get(v_____do__lift_5493_, 0);
lean_inc(v_a_5496_);
lean_dec_ref_known(v_____do__lift_5493_, 1);
v___x_5497_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5488_, v_inst_5489_, v_inst_5490_, v_ch_5491_, v_f_5492_, v_a_5496_);
return v___x_5497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object* v_00_u03b1_5498_, lean_object* v_m_5499_, lean_object* v_00_u03b2_5500_, lean_object* v_inst_5501_, lean_object* v_inst_5502_, lean_object* v_inst_5503_, lean_object* v_ch_5504_, lean_object* v_f_5505_, lean_object* v_b_5506_){
_start:
{
lean_object* v___x_5507_; 
v___x_5507_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5501_, v_inst_5502_, v_inst_5503_, v_ch_5504_, v_f_5505_, v_b_5506_);
return v___x_5507_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5508_, lean_object* v_inst_5509_, lean_object* v_inst_5510_, lean_object* v_ch_5511_, lean_object* v_b_5512_, lean_object* v_f_5513_){
_start:
{
lean_object* v___x_5514_; 
v___x_5514_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5508_, v_inst_5509_, v_inst_5510_, v_ch_5511_, v_f_5513_, v_b_5512_);
return v___x_5514_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_00_u03b1_5515_, lean_object* v_m_5516_, lean_object* v_inst_5517_, lean_object* v_inst_5518_, lean_object* v_inst_5519_, lean_object* v_00_u03b2_5520_, lean_object* v_ch_5521_, lean_object* v_b_5522_, lean_object* v_f_5523_){
_start:
{
lean_object* v___x_5524_; 
v___x_5524_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5517_, v_inst_5518_, v_inst_5519_, v_ch_5521_, v_f_5523_, v_b_5522_);
return v___x_5524_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5525_, lean_object* v_inst_5526_, lean_object* v_inst_5527_, lean_object* v_00_u03b2_5528_, lean_object* v_ch_5529_, lean_object* v_b_5530_, lean_object* v_f_5531_){
_start:
{
lean_object* v___x_5532_; 
v___x_5532_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5525_, v_inst_5526_, v_inst_5527_, v_ch_5529_, v_f_5531_, v_b_5530_);
return v___x_5532_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5533_, lean_object* v_inst_5534_, lean_object* v_inst_5535_){
_start:
{
lean_object* v___f_5536_; 
v___f_5536_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5536_, 0, v_inst_5533_);
lean_closure_set(v___f_5536_, 1, v_inst_5534_);
lean_closure_set(v___f_5536_, 2, v_inst_5535_);
return v___f_5536_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5537_, lean_object* v_m_5538_, lean_object* v_inst_5539_, lean_object* v_inst_5540_, lean_object* v_inst_5541_){
_start:
{
lean_object* v___f_5542_; 
v___f_5542_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5542_, 0, v_inst_5539_);
lean_closure_set(v___f_5542_, 1, v_inst_5540_);
lean_closure_set(v___f_5542_, 2, v_inst_5541_);
return v___f_5542_;
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

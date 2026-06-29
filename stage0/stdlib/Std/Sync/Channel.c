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
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_CloseableChannel_Error_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Std_CloseableChannel_Error_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_CloseableChannel_Error_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Std_CloseableChannel_Error_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___redArg(lean_object* v_closed_27_){
_start:
{
lean_inc(v_closed_27_);
return v_closed_27_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___redArg___boxed(lean_object* v_closed_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_CloseableChannel_Error_closed_elim___redArg(v_closed_28_);
lean_dec(v_closed_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_closed_33_){
_start:
{
lean_inc(v_closed_33_);
return v_closed_33_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_closed_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Std_CloseableChannel_Error_closed_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_closed_37_);
lean_dec(v_closed_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg(lean_object* v_alreadyClosed_40_){
_start:
{
lean_inc(v_alreadyClosed_40_);
return v_alreadyClosed_40_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg___boxed(lean_object* v_alreadyClosed_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg(v_alreadyClosed_41_);
lean_dec(v_alreadyClosed_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_alreadyClosed_46_){
_start:
{
lean_inc(v_alreadyClosed_46_);
return v_alreadyClosed_46_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_alreadyClosed_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Std_CloseableChannel_Error_alreadyClosed_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_alreadyClosed_50_);
lean_dec(v_alreadyClosed_50_);
return v_res_52_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instReprError_repr___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(2u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instReprError_repr___closed__5(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instReprError_repr(uint8_t v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___y_66_; lean_object* v___y_73_; 
if (v_x_63_ == 0)
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1024u);
v___x_80_ = lean_nat_dec_le(v___x_79_, v_prec_64_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__4, &l_Std_CloseableChannel_instReprError_repr___closed__4_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__4);
v___y_66_ = v___x_81_;
goto v___jp_65_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__5, &l_Std_CloseableChannel_instReprError_repr___closed__5_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__5);
v___y_66_ = v___x_82_;
goto v___jp_65_;
}
}
else
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(1024u);
v___x_84_ = lean_nat_dec_le(v___x_83_, v_prec_64_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__4, &l_Std_CloseableChannel_instReprError_repr___closed__4_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__4);
v___y_73_ = v___x_85_;
goto v___jp_72_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__5, &l_Std_CloseableChannel_instReprError_repr___closed__5_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__5);
v___y_73_ = v___x_86_;
goto v___jp_72_;
}
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_67_ = ((lean_object*)(l_Std_CloseableChannel_instReprError_repr___closed__1));
lean_inc(v___y_66_);
v___x_68_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_68_, 0, v___y_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = 0;
v___x_70_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___x_69_);
v___x_71_ = l_Repr_addAppParen(v___x_70_, v_prec_64_);
return v___x_71_;
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = ((lean_object*)(l_Std_CloseableChannel_instReprError_repr___closed__3));
lean_inc(v___y_73_);
v___x_75_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_75_, 0, v___y_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = 0;
v___x_77_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_76_);
v___x_78_ = l_Repr_addAppParen(v___x_77_, v_prec_64_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instReprError_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_121__boxed_89_; lean_object* v_res_90_; 
v_x_121__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Std_CloseableChannel_instReprError_repr(v_x_121__boxed_89_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_90_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Error_ofNat(lean_object* v_n_93_){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_dec_le(v_n_93_, v___x_94_);
if (v___x_95_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ofNat___boxed(lean_object* v_n_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Std_CloseableChannel_Error_ofNat(v_n_98_);
lean_dec(v_n_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_instDecidableEqError(uint8_t v_x_101_, uint8_t v_y_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = l_Std_CloseableChannel_Error_ctorIdx(v_x_101_);
v___x_104_ = l_Std_CloseableChannel_Error_ctorIdx(v_y_102_);
v___x_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
lean_dec(v___x_104_);
lean_dec(v___x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instDecidableEqError___boxed(lean_object* v_x_106_, lean_object* v_y_107_){
_start:
{
uint8_t v_x_13__boxed_108_; uint8_t v_y_14__boxed_109_; uint8_t v_res_110_; lean_object* v_r_111_; 
v_x_13__boxed_108_ = lean_unbox(v_x_106_);
v_y_14__boxed_109_ = lean_unbox(v_y_107_);
v_res_110_ = l_Std_CloseableChannel_instDecidableEqError(v_x_13__boxed_108_, v_y_14__boxed_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint64_t l_Std_CloseableChannel_instHashableError_hash(uint8_t v_x_112_){
_start:
{
if (v_x_112_ == 0)
{
uint64_t v___x_113_; 
v___x_113_ = 0ULL;
return v___x_113_;
}
else
{
uint64_t v___x_114_; 
v___x_114_ = 1ULL;
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instHashableError_hash___boxed(lean_object* v_x_115_){
_start:
{
uint8_t v_x_28__boxed_116_; uint64_t v_res_117_; lean_object* v_r_118_; 
v_x_28__boxed_116_ = lean_unbox(v_x_115_);
v_res_117_ = l_Std_CloseableChannel_instHashableError_hash(v_x_28__boxed_116_);
v_r_118_ = lean_box_uint64(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instToStringError___lam__0(uint8_t v_x_123_){
_start:
{
if (v_x_123_ == 0)
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l_Std_CloseableChannel_instToStringError___lam__0___closed__0));
return v___x_124_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = ((lean_object*)(l_Std_CloseableChannel_instToStringError___lam__0___closed__1));
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instToStringError___lam__0___boxed(lean_object* v_x_126_){
_start:
{
uint8_t v_x_26__boxed_127_; lean_object* v_res_128_; 
v_x_26__boxed_127_ = lean_unbox(v_x_126_);
v_res_128_ = l_Std_CloseableChannel_instToStringError___lam__0(v_x_26__boxed_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(lean_object* v_00_u03b1_135_, lean_object* v_x_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_apply_1(v_x_136_, lean_box(0));
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_160_; 
v_a_147_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_160_ == 0)
{
v___x_149_ = v___x_138_;
v_isShared_150_ = v_isSharedCheck_160_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_138_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_160_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
uint8_t v___x_151_; 
v___x_151_ = lean_unbox(v_a_147_);
lean_dec(v_a_147_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = ((lean_object*)(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0));
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_152_);
v___x_154_ = v___x_149_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = ((lean_object*)(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1));
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_156_);
v___x_158_ = v___x_149_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___boxed(lean_object* v_00_u03b1_161_, lean_object* v_x_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(v_00_u03b1_161_, v_x_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_unsigned_to_nat(0u);
return v___x_168_;
}
else
{
lean_object* v___x_169_; 
v___x_169_ = lean_unsigned_to_nat(1u);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg___boxed(lean_object* v_x_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(v_x_170_);
lean_dec_ref(v_x_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx(lean_object* v_00_u03b1_172_, lean_object* v_x_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(v_x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___boxed(lean_object* v_00_u03b1_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx(v_00_u03b1_175_, v_x_176_);
lean_dec_ref(v_x_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(lean_object* v_t_178_, lean_object* v_k_179_){
_start:
{
if (lean_obj_tag(v_t_178_) == 0)
{
lean_object* v_promise_180_; lean_object* v___x_181_; 
v_promise_180_ = lean_ctor_get(v_t_178_, 0);
lean_inc(v_promise_180_);
lean_dec_ref_known(v_t_178_, 1);
v___x_181_ = lean_apply_1(v_k_179_, v_promise_180_);
return v___x_181_;
}
else
{
lean_object* v_finished_182_; lean_object* v___x_183_; 
v_finished_182_ = lean_ctor_get(v_t_178_, 0);
lean_inc_ref(v_finished_182_);
lean_dec_ref_known(v_t_178_, 1);
v___x_183_ = lean_apply_1(v_k_179_, v_finished_182_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(lean_object* v_00_u03b1_184_, lean_object* v_motive_185_, lean_object* v_ctorIdx_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_k_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_187_, v_k_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___boxed(lean_object* v_00_u03b1_191_, lean_object* v_motive_192_, lean_object* v_ctorIdx_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_k_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(v_00_u03b1_191_, v_motive_192_, v_ctorIdx_193_, v_t_194_, v_h_195_, v_k_196_);
lean_dec(v_ctorIdx_193_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim___redArg(lean_object* v_t_198_, lean_object* v_normal_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_198_, v_normal_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim(lean_object* v_00_u03b1_201_, lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_normal_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_203_, v_normal_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim___redArg(lean_object* v_t_207_, lean_object* v_select_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_207_, v_select_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim(lean_object* v_00_u03b1_210_, lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_select_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_212_, v_select_214_);
return v___x_215_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(lean_object* v_x_216_, lean_object* v_w_217_, lean_object* v_lose_218_){
_start:
{
lean_object* v_finished_220_; lean_object* v_promise_221_; lean_object* v___x_222_; uint8_t v___y_224_; uint8_t v___x_232_; 
v_finished_220_ = lean_ctor_get(v_w_217_, 0);
v_promise_221_ = lean_ctor_get(v_w_217_, 1);
v___x_222_ = lean_st_ref_take(v_finished_220_);
v___x_232_ = lean_unbox(v___x_222_);
lean_dec(v___x_222_);
if (v___x_232_ == 0)
{
uint8_t v___x_233_; 
v___x_233_ = 1;
v___y_224_ = v___x_233_;
goto v___jp_223_;
}
else
{
uint8_t v___x_234_; 
v___x_234_ = 0;
v___y_224_ = v___x_234_;
goto v___jp_223_;
}
v___jp_223_:
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = 1;
v___x_226_ = lean_box(v___x_225_);
v___x_227_ = lean_st_ref_set(v_finished_220_, v___x_226_);
if (v___y_224_ == 0)
{
lean_object* v___x_228_; uint8_t v___x_229_; 
lean_dec(v_x_216_);
v___x_228_ = lean_apply_1(v_lose_218_, lean_box(0));
v___x_229_ = lean_unbox(v___x_228_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec_ref(v_lose_218_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v_x_216_);
v___x_231_ = lean_io_promise_resolve(v___x_230_, v_promise_221_);
return v___y_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg___boxed(lean_object* v_x_235_, lean_object* v_w_236_, lean_object* v_lose_237_, lean_object* v___y_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_235_, v_w_236_, v_lose_237_);
lean_dec_ref(v_w_236_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(lean_object* v_00_u03b1_241_, lean_object* v_x_242_, lean_object* v_w_243_, lean_object* v_lose_244_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_242_, v_w_243_, v_lose_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___boxed(lean_object* v_00_u03b1_247_, lean_object* v_x_248_, lean_object* v_w_249_, lean_object* v_lose_250_, lean_object* v___y_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(v_00_u03b1_247_, v_x_248_, v_w_249_, v_lose_250_);
lean_dec_ref(v_w_249_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(uint8_t v___x_254_){
_start:
{
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0___boxed(lean_object* v___x_256_, lean_object* v___y_257_){
_start:
{
uint8_t v___x_400__boxed_258_; uint8_t v_res_259_; lean_object* v_r_260_; 
v___x_400__boxed_258_ = lean_unbox(v___x_256_);
v_res_259_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(v___x_400__boxed_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(lean_object* v_c_264_, lean_object* v_x_265_){
_start:
{
if (lean_obj_tag(v_c_264_) == 0)
{
lean_object* v_promise_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_promise_267_ = lean_ctor_get(v_c_264_, 0);
v___x_268_ = lean_io_promise_resolve(v_x_265_, v_promise_267_);
v___x_269_ = 1;
return v___x_269_;
}
else
{
lean_object* v_finished_270_; lean_object* v_lose_271_; uint8_t v___x_272_; 
v_finished_270_ = lean_ctor_get(v_c_264_, 0);
v_lose_271_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0));
v___x_272_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_265_, v_finished_270_, v_lose_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___boxed(lean_object* v_c_273_, lean_object* v_x_274_, lean_object* v_a_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_c_273_, v_x_274_);
lean_dec_ref(v_c_273_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(lean_object* v_00_u03b1_278_, lean_object* v_c_279_, lean_object* v_x_280_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_c_279_, v_x_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___boxed(lean_object* v_00_u03b1_283_, lean_object* v_c_284_, lean_object* v_x_285_, lean_object* v_a_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(v_00_u03b1_283_, v_c_284_, v_x_285_);
lean_dec_ref(v_c_284_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_Queue_empty(lean_box(0));
return v___x_289_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = 0;
v___x_291_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_292_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*2, v___x_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg(){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1);
v___x_295_ = l_Std_Mutex_new___redArg(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___boxed(lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(lean_object* v_00_u03b1_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___boxed(lean_object* v_00_u03b1_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(v_00_u03b1_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(lean_object* v_mutex_304_, lean_object* v_k_305_){
_start:
{
lean_object* v_ref_307_; lean_object* v_mutex_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_ref_307_ = lean_ctor_get(v_mutex_304_, 0);
lean_inc(v_ref_307_);
v_mutex_308_ = lean_ctor_get(v_mutex_304_, 1);
lean_inc(v_mutex_308_);
lean_dec_ref(v_mutex_304_);
v___x_309_ = lean_io_basemutex_lock(v_mutex_308_);
v___x_310_ = lean_apply_2(v_k_305_, v_ref_307_, lean_box(0));
v___x_311_ = lean_io_basemutex_unlock(v_mutex_308_);
lean_dec(v_mutex_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg___boxed(lean_object* v_mutex_312_, lean_object* v_k_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_312_, v_k_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(lean_object* v_00_u03b1_316_, lean_object* v_00_u03b2_317_, lean_object* v_mutex_318_, lean_object* v_k_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_318_, v_k_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___boxed(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_mutex_324_, lean_object* v_k_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(v_00_u03b1_322_, v_00_u03b2_323_, v_mutex_324_, v_k_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(lean_object* v_v_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; lean_object* v_values_332_; lean_object* v_consumers_333_; uint8_t v_closed_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_361_; 
v___x_331_ = lean_st_ref_get(v___y_329_);
v_values_332_ = lean_ctor_get(v___x_331_, 0);
v_consumers_333_ = lean_ctor_get(v___x_331_, 1);
v_closed_334_ = lean_ctor_get_uint8(v___x_331_, sizeof(void*)*2);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_361_ == 0)
{
v___x_336_ = v___x_331_;
v_isShared_337_ = v_isSharedCheck_361_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_consumers_333_);
lean_inc(v_values_332_);
lean_dec(v___x_331_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_361_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_box(0);
lean_inc_ref(v_consumers_333_);
v___x_339_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_333_);
if (lean_obj_tag(v___x_339_) == 1)
{
lean_object* v_val_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v_consumers_333_);
v_val_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_355_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_355_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_val_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_355_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_347_; 
v_fst_344_ = lean_ctor_get(v_val_340_, 0);
lean_inc(v_fst_344_);
v_snd_345_ = lean_ctor_get(v_val_340_, 1);
lean_inc(v_snd_345_);
lean_dec(v_val_340_);
lean_inc(v_v_328_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v_v_328_);
v___x_347_ = v___x_342_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_v_328_);
v___x_347_ = v_reuseFailAlloc_354_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
uint8_t v___x_348_; lean_object* v___x_350_; 
v___x_348_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_344_, v___x_347_);
lean_dec(v_fst_344_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_snd_345_);
v___x_350_ = v___x_336_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_values_332_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_snd_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_353_, sizeof(void*)*2, v_closed_334_);
v___x_350_ = v_reuseFailAlloc_353_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; 
v___x_351_ = lean_st_ref_set(v___y_329_, v___x_350_);
if (v___x_348_ == 0)
{
goto _start;
}
else
{
lean_dec(v_v_328_);
return v___x_338_;
}
}
}
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec(v___x_339_);
v___x_356_ = l_Std_Queue_enqueue___redArg(v_v_328_, v_values_332_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_356_);
v___x_358_ = v___x_336_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_consumers_333_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*2, v_closed_334_);
v___x_358_ = v_reuseFailAlloc_360_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; 
v___x_359_ = lean_st_ref_set(v___y_329_, v___x_358_);
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg___boxed(lean_object* v_v_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_362_, v___y_363_);
lean_dec(v___y_363_);
return v_res_365_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(lean_object* v_v_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; uint8_t v_closed_370_; 
v___x_369_ = lean_st_ref_get(v___y_367_);
v_closed_370_ = lean_ctor_get_uint8(v___x_369_, sizeof(void*)*2);
lean_dec(v___x_369_);
if (v_closed_370_ == 0)
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_366_, v___y_367_);
v___x_372_ = 1;
return v___x_372_;
}
else
{
uint8_t v___x_373_; 
lean_dec(v_v_366_);
v___x_373_ = 0;
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed(lean_object* v_v_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(v_v_374_, v___y_375_);
lean_dec(v___y_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(lean_object* v_ch_379_, lean_object* v_v_380_){
_start:
{
lean_object* v___f_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___f_382_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_382_, 0, v_v_380_);
v___x_383_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_379_, v___f_382_);
v___x_384_ = lean_unbox(v___x_383_);
lean_dec(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___boxed(lean_object* v_ch_385_, lean_object* v_v_386_, lean_object* v_a_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_385_, v_v_386_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(lean_object* v_00_u03b1_390_, lean_object* v_ch_391_, lean_object* v_v_392_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_391_, v_v_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___boxed(lean_object* v_00_u03b1_395_, lean_object* v_ch_396_, lean_object* v_v_397_, lean_object* v_a_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(v_00_u03b1_395_, v_ch_396_, v_v_397_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(lean_object* v_00_u03b1_401_, lean_object* v_v_402_, lean_object* v_inst_403_, lean_object* v_a_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_402_, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_408_, lean_object* v_v_409_, lean_object* v_inst_410_, lean_object* v_a_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(v_00_u03b1_408_, v_v_409_, v_inst_410_, v_a_411_, v___y_412_);
lean_dec(v___y_412_);
return v_res_414_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
v___x_419_ = lean_task_pure(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
v___x_423_ = lean_task_pure(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(lean_object* v_ch_424_, lean_object* v_v_425_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_424_, v_v_425_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
v___x_428_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_428_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___boxed(lean_object* v_ch_430_, lean_object* v_v_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_430_, v_v_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(lean_object* v_00_u03b1_434_, lean_object* v_ch_435_, lean_object* v_v_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_435_, v_v_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___boxed(lean_object* v_00_u03b1_439_, lean_object* v_ch_440_, lean_object* v_v_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(v_00_u03b1_439_, v_ch_440_, v_v_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(lean_object* v_mutex_444_, lean_object* v_k_445_){
_start:
{
lean_object* v_ref_447_; lean_object* v_mutex_448_; lean_object* v___x_449_; lean_object* v_r_450_; 
v_ref_447_ = lean_ctor_get(v_mutex_444_, 0);
lean_inc(v_ref_447_);
v_mutex_448_ = lean_ctor_get(v_mutex_444_, 1);
lean_inc(v_mutex_448_);
lean_dec_ref(v_mutex_444_);
v___x_449_ = lean_io_basemutex_lock(v_mutex_448_);
v_r_450_ = lean_apply_2(v_k_445_, v_ref_447_, lean_box(0));
if (lean_obj_tag(v_r_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_459_; 
v_a_451_ = lean_ctor_get(v_r_450_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_r_450_);
if (v_isSharedCheck_459_ == 0)
{
v___x_453_ = v_r_450_;
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v_r_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_io_basemutex_unlock(v_mutex_448_);
lean_dec(v_mutex_448_);
if (v_isShared_454_ == 0)
{
v___x_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_451_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_468_; 
v_a_460_ = lean_ctor_get(v_r_450_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_r_450_);
if (v_isSharedCheck_468_ == 0)
{
v___x_462_ = v_r_450_;
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v_r_450_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_io_basemutex_unlock(v_mutex_448_);
lean_dec(v_mutex_448_);
if (v_isShared_463_ == 0)
{
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_460_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg___boxed(lean_object* v_mutex_469_, lean_object* v_k_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_469_, v_k_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_mutex_475_, lean_object* v_k_476_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_475_, v_k_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___boxed(lean_object* v_00_u03b1_479_, lean_object* v_00_u03b2_480_, lean_object* v_mutex_481_, lean_object* v_k_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(v_00_u03b1_479_, v_00_u03b2_480_, v_mutex_481_, v_k_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(lean_object* v_as_485_, size_t v_sz_486_, size_t v_i_487_, lean_object* v_b_488_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = lean_usize_dec_lt(v_i_487_, v_sz_486_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v_b_488_);
return v___x_491_;
}
else
{
lean_object* v_a_492_; lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; size_t v___x_496_; size_t v___x_497_; 
v_a_492_ = lean_array_uget_borrowed(v_as_485_, v_i_487_);
v___x_493_ = lean_box(0);
v___x_494_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_492_, v___x_493_);
v___x_495_ = lean_box(0);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_487_, v___x_496_);
v_i_487_ = v___x_497_;
v_b_488_ = v___x_495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg___boxed(lean_object* v_as_499_, lean_object* v_sz_500_, lean_object* v_i_501_, lean_object* v_b_502_, lean_object* v___y_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_500_);
lean_dec(v_sz_500_);
v_i_boxed_505_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_499_, v_sz_boxed_504_, v_i_boxed_505_, v_b_502_);
lean_dec_ref(v_as_499_);
return v_res_506_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_Queue_empty(lean_box(0));
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; uint8_t v_closed_511_; 
v___x_510_ = lean_st_ref_get(v___y_508_);
v_closed_511_ = lean_ctor_get_uint8(v___x_510_, sizeof(void*)*2);
if (v_closed_511_ == 0)
{
lean_object* v_values_512_; lean_object* v_consumers_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_536_; 
v_values_512_ = lean_ctor_get(v___x_510_, 0);
v_consumers_513_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_536_ == 0)
{
v___x_515_ = v___x_510_;
v_isShared_516_ = v_isSharedCheck_536_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_consumers_513_);
lean_inc(v_values_512_);
lean_dec(v___x_510_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_536_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; size_t v_sz_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_517_ = l_Std_Queue_toArray___redArg(v_consumers_513_);
v___x_518_ = lean_box(0);
v_sz_519_ = lean_array_size(v___x_517_);
v___x_520_ = ((size_t)0ULL);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v___x_517_, v_sz_519_, v___x_520_, v___x_518_);
lean_dec_ref(v___x_517_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_534_; 
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v___x_521_, 0);
lean_dec(v_unused_535_);
v___x_523_ = v___x_521_;
v_isShared_524_ = v_isSharedCheck_534_;
goto v_resetjp_522_;
}
else
{
lean_dec(v___x_521_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_534_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_528_; 
v___x_525_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
v___x_526_ = 1;
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_525_);
v___x_528_ = v___x_515_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_values_512_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_525_);
v___x_528_ = v_reuseFailAlloc_533_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*2, v___x_526_);
v___x_529_ = lean_st_ref_set(v___y_508_, v___x_528_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_518_);
v___x_531_ = v___x_523_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_518_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_del_object(v___x_515_);
lean_dec_ref(v_values_512_);
return v___x_521_;
}
}
}
else
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec(v___x_510_);
v___x_537_ = 1;
v___x_538_ = lean_box(v___x_537_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___boxed(lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(v___y_540_);
lean_dec(v___y_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(lean_object* v_ch_544_){
_start:
{
lean_object* v___f_546_; lean_object* v___x_547_; 
v___f_546_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0));
v___x_547_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_544_, v___f_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___boxed(lean_object* v_ch_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(lean_object* v_00_u03b1_551_, lean_object* v_ch_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___boxed(lean_object* v_00_u03b1_555_, lean_object* v_ch_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(v_00_u03b1_555_, v_ch_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(lean_object* v_00_u03b1_559_, lean_object* v_as_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_560_, v_sz_561_, v_i_562_, v_b_563_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___boxed(lean_object* v_00_u03b1_567_, lean_object* v_as_568_, lean_object* v_sz_569_, lean_object* v_i_570_, lean_object* v_b_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v_sz_boxed_574_ = lean_unbox_usize(v_sz_569_);
lean_dec(v_sz_569_);
v_i_boxed_575_ = lean_unbox_usize(v_i_570_);
lean_dec(v_i_570_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(v_00_u03b1_567_, v_as_568_, v_sz_boxed_574_, v_i_boxed_575_, v_b_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v_as_568_);
return v_res_576_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; uint8_t v_closed_580_; 
v___x_579_ = lean_st_ref_get(v___y_577_);
v_closed_580_ = lean_ctor_get_uint8(v___x_579_, sizeof(void*)*2);
lean_dec(v___x_579_);
return v_closed_580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(v___y_581_);
lean_dec(v___y_581_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(lean_object* v_ch_586_){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___f_588_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0));
v___x_589_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_586_, v___f_588_);
v___x_590_ = lean_unbox(v___x_589_);
lean_dec(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___boxed(lean_object* v_ch_591_, lean_object* v_a_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_591_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(lean_object* v_00_u03b1_595_, lean_object* v_ch_596_){
_start:
{
uint8_t v___x_598_; 
v___x_598_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___boxed(lean_object* v_00_u03b1_599_, lean_object* v_ch_600_, lean_object* v_a_601_){
_start:
{
uint8_t v_res_602_; lean_object* v_r_603_; 
v_res_602_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(v_00_u03b1_599_, v_ch_600_);
v_r_603_ = lean_box(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_604_, lean_object* v_fst_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_toPure_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_toPure_607_ = lean_ctor_get(v_toApplicative_604_, 1);
lean_inc(v_toPure_607_);
lean_dec_ref(v_toApplicative_604_);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v_fst_605_);
v___x_609_ = lean_apply_2(v_toPure_607_, lean_box(0), v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_610_, lean_object* v_a_611_, lean_object* v_inst_612_, lean_object* v_toBind_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_values_615_; lean_object* v_consumers_616_; uint8_t v_closed_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_635_; 
v_values_615_ = lean_ctor_get(v_a_614_, 0);
v_consumers_616_ = lean_ctor_get(v_a_614_, 1);
v_closed_617_ = lean_ctor_get_uint8(v_a_614_, sizeof(void*)*2);
v_isSharedCheck_635_ = !lean_is_exclusive(v_a_614_);
if (v_isSharedCheck_635_ == 0)
{
v___x_619_ = v_a_614_;
v_isShared_620_ = v_isSharedCheck_635_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_consumers_616_);
lean_inc(v_values_615_);
lean_dec(v_a_614_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_635_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_Queue_dequeue_x3f___redArg(v_values_615_);
if (lean_obj_tag(v___x_621_) == 1)
{
lean_object* v_val_622_; lean_object* v_fst_623_; lean_object* v_snd_624_; lean_object* v___f_625_; lean_object* v___x_627_; 
v_val_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v___x_621_, 1);
v_fst_623_ = lean_ctor_get(v_val_622_, 0);
lean_inc(v_fst_623_);
v_snd_624_ = lean_ctor_get(v_val_622_, 1);
lean_inc(v_snd_624_);
lean_dec(v_val_622_);
v___f_625_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_625_, 0, v_toApplicative_610_);
lean_closure_set(v___f_625_, 1, v_fst_623_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v_snd_624_);
v___x_627_ = v___x_619_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_snd_624_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_consumers_616_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*2, v_closed_617_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_inc(v_a_611_);
v___x_628_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_628_, 0, lean_box(0));
lean_closure_set(v___x_628_, 1, lean_box(0));
lean_closure_set(v___x_628_, 2, v_a_611_);
lean_closure_set(v___x_628_, 3, v___x_627_);
v___x_629_ = lean_apply_2(v_inst_612_, lean_box(0), v___x_628_);
v___x_630_ = lean_apply_4(v_toBind_613_, lean_box(0), lean_box(0), v___x_629_, v___f_625_);
return v___x_630_;
}
}
else
{
lean_object* v_toPure_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v___x_621_);
lean_del_object(v___x_619_);
lean_dec_ref(v_consumers_616_);
lean_dec(v_toBind_613_);
lean_dec(v_inst_612_);
v_toPure_632_ = lean_ctor_get(v_toApplicative_610_, 1);
lean_inc(v_toPure_632_);
lean_dec_ref(v_toApplicative_610_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_apply_2(v_toPure_632_, lean_box(0), v___x_633_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_636_, lean_object* v_a_637_, lean_object* v_inst_638_, lean_object* v_toBind_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(v_toApplicative_636_, v_a_637_, v_inst_638_, v_toBind_639_, v_a_640_);
lean_dec(v_a_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_toApplicative_645_; lean_object* v_toBind_646_; lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_toApplicative_645_ = lean_ctor_get(v_inst_642_, 0);
lean_inc_ref(v_toApplicative_645_);
v_toBind_646_ = lean_ctor_get(v_inst_642_, 1);
lean_inc_n(v_toBind_646_, 2);
lean_dec_ref(v_inst_642_);
lean_inc(v_inst_643_);
lean_inc_n(v_a_644_, 2);
v___f_647_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_647_, 0, v_toApplicative_645_);
lean_closure_set(v___f_647_, 1, v_a_644_);
lean_closure_set(v___f_647_, 2, v_inst_643_);
lean_closure_set(v___f_647_, 3, v_toBind_646_);
v___x_648_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_648_, 0, lean_box(0));
lean_closure_set(v___x_648_, 1, lean_box(0));
lean_closure_set(v___x_648_, 2, v_a_644_);
v___x_649_ = lean_apply_2(v_inst_643_, lean_box(0), v___x_648_);
v___x_650_ = lean_apply_4(v_toBind_646_, lean_box(0), lean_box(0), v___x_649_, v___f_647_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_651_, v_inst_652_, v_a_653_);
lean_dec(v_a_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(lean_object* v_m_655_, lean_object* v_00_u03b1_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_657_, v_inst_658_, v_a_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___boxed(lean_object* v_m_661_, lean_object* v_00_u03b1_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(v_m_661_, v_00_u03b1_662_, v_inst_663_, v_inst_664_, v_a_665_);
lean_dec(v_a_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(lean_object* v_a_667_){
_start:
{
lean_object* v___x_669_; lean_object* v_values_670_; lean_object* v_consumers_671_; uint8_t v_closed_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_692_; 
v___x_669_ = lean_st_ref_get(v_a_667_);
v_values_670_ = lean_ctor_get(v___x_669_, 0);
v_consumers_671_ = lean_ctor_get(v___x_669_, 1);
v_closed_672_ = lean_ctor_get_uint8(v___x_669_, sizeof(void*)*2);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_692_ == 0)
{
v___x_674_ = v___x_669_;
v_isShared_675_ = v_isSharedCheck_692_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_consumers_671_);
lean_inc(v_values_670_);
lean_dec(v___x_669_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_692_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_Queue_dequeue_x3f___redArg(v_values_670_);
if (lean_obj_tag(v___x_676_) == 1)
{
lean_object* v_val_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_690_; 
v_val_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_690_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_690_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_val_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_690_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_684_; 
v_fst_681_ = lean_ctor_get(v_val_677_, 0);
lean_inc(v_fst_681_);
v_snd_682_ = lean_ctor_get(v_val_677_, 1);
lean_inc(v_snd_682_);
lean_dec(v_val_677_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v_snd_682_);
v___x_684_ = v___x_674_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_snd_682_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_consumers_671_);
lean_ctor_set_uint8(v_reuseFailAlloc_689_, sizeof(void*)*2, v_closed_672_);
v___x_684_ = v_reuseFailAlloc_689_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = lean_st_ref_set(v_a_667_, v___x_684_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v_fst_681_);
v___x_687_ = v___x_679_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_fst_681_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v___x_691_; 
lean_dec(v___x_676_);
lean_del_object(v___x_674_);
lean_dec_ref(v_consumers_671_);
v___x_691_ = lean_box(0);
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_693_);
lean_dec(v_a_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(lean_object* v_00_u03b1_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_697_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_700_, lean_object* v_a_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(v_00_u03b1_700_, v_a_701_);
lean_dec(v_a_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(lean_object* v_ch_705_){
_start:
{
lean_object* v___f_707_; lean_object* v___x_708_; 
v___f_707_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0));
v___x_708_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_705_, v___f_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___boxed(lean_object* v_ch_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(lean_object* v_00_u03b1_712_, lean_object* v_ch_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___boxed(lean_object* v_00_u03b1_716_, lean_object* v_ch_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(v_00_u03b1_716_, v_ch_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
lean_object* v___x_721_; 
v___x_721_ = lean_box(0);
return v___x_721_;
}
else
{
lean_object* v_val_722_; 
v_val_722_ = lean_ctor_get(v_x_720_, 0);
lean_inc(v_val_722_);
return v_val_722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed(lean_object* v_x_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(v_x_723_);
lean_dec(v_x_723_);
return v_res_724_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_box(0);
v___x_726_ = lean_task_pure(v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(lean_object* v___f_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v___y_728_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v___x_731_; 
lean_dec_ref(v___f_727_);
v___x_731_ = lean_task_pure(v___x_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; uint8_t v_closed_733_; 
lean_dec(v___x_730_);
v___x_732_ = lean_st_ref_get(v___y_728_);
v_closed_733_ = lean_ctor_get_uint8(v___x_732_, sizeof(void*)*2);
lean_dec(v___x_732_);
if (v_closed_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_values_736_; lean_object* v_consumers_737_; uint8_t v_closed_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_752_; 
v___x_734_ = lean_io_promise_new();
v___x_735_ = lean_st_ref_take(v___y_728_);
v_values_736_ = lean_ctor_get(v___x_735_, 0);
v_consumers_737_ = lean_ctor_get(v___x_735_, 1);
v_closed_738_ = lean_ctor_get_uint8(v___x_735_, sizeof(void*)*2);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_752_ == 0)
{
v___x_740_ = v___x_735_;
v_isShared_741_ = v_isSharedCheck_752_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_consumers_737_);
lean_inc(v_values_736_);
lean_dec(v___x_735_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_752_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
lean_inc(v___x_734_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_734_);
v___x_743_ = l_Std_Queue_enqueue___redArg(v___x_742_, v_consumers_737_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_743_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_values_736_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_751_, sizeof(void*)*2, v_closed_738_);
v___x_745_ = v_reuseFailAlloc_751_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_746_ = lean_st_ref_set(v___y_728_, v___x_745_);
v___x_747_ = 1;
v___x_748_ = lean_io_promise_result_opt(v___x_734_);
lean_dec(v___x_734_);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_task_map(v___f_727_, v___x_748_, v___x_749_, v___x_747_);
return v___x_750_;
}
}
}
else
{
lean_object* v___x_753_; 
lean_dec_ref(v___f_727_);
v___x_753_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed(lean_object* v___f_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(v___f_754_, v___y_755_);
lean_dec(v___y_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(lean_object* v_ch_761_){
_start:
{
lean_object* v___f_763_; lean_object* v___x_764_; 
v___f_763_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1));
v___x_764_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_761_, v___f_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___boxed(lean_object* v_ch_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(lean_object* v_00_u03b1_768_, lean_object* v_ch_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___boxed(lean_object* v_00_u03b1_772_, lean_object* v_ch_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(v_00_u03b1_772_, v_ch_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_776_, lean_object* v_a_777_){
_start:
{
uint8_t v___y_779_; lean_object* v_values_783_; uint8_t v_closed_784_; uint8_t v___x_785_; 
v_values_783_ = lean_ctor_get(v_a_777_, 0);
v_closed_784_ = lean_ctor_get_uint8(v_a_777_, sizeof(void*)*2);
v___x_785_ = l_Std_Queue_isEmpty___redArg(v_values_783_);
if (v___x_785_ == 0)
{
uint8_t v___x_786_; 
v___x_786_ = 1;
v___y_779_ = v___x_786_;
goto v___jp_778_;
}
else
{
v___y_779_ = v_closed_784_;
goto v___jp_778_;
}
v___jp_778_:
{
lean_object* v_toPure_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_toPure_780_ = lean_ctor_get(v_toApplicative_776_, 1);
lean_inc(v_toPure_780_);
lean_dec_ref(v_toApplicative_776_);
v___x_781_ = lean_box(v___y_779_);
v___x_782_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_781_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(v_toApplicative_787_, v_a_788_);
lean_dec_ref(v_a_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_toApplicative_793_; lean_object* v_toBind_794_; lean_object* v___f_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_toApplicative_793_ = lean_ctor_get(v_inst_790_, 0);
lean_inc_ref(v_toApplicative_793_);
v_toBind_794_ = lean_ctor_get(v_inst_790_, 1);
lean_inc(v_toBind_794_);
lean_dec_ref(v_inst_790_);
v___f_795_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_795_, 0, v_toApplicative_793_);
lean_inc(v_a_792_);
v___x_796_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_796_, 0, lean_box(0));
lean_closure_set(v___x_796_, 1, lean_box(0));
lean_closure_set(v___x_796_, 2, v_a_792_);
v___x_797_ = lean_apply_2(v_inst_791_, lean_box(0), v___x_796_);
v___x_798_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_797_, v___f_795_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___boxed(lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(v_inst_799_, v_inst_800_, v_a_801_);
lean_dec(v_a_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(lean_object* v_m_803_, lean_object* v_00_u03b1_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_toApplicative_808_; lean_object* v_toBind_809_; lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_toApplicative_808_ = lean_ctor_get(v_inst_805_, 0);
lean_inc_ref(v_toApplicative_808_);
v_toBind_809_ = lean_ctor_get(v_inst_805_, 1);
lean_inc(v_toBind_809_);
lean_dec_ref(v_inst_805_);
v___f_810_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_810_, 0, v_toApplicative_808_);
lean_inc(v_a_807_);
v___x_811_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_811_, 0, lean_box(0));
lean_closure_set(v___x_811_, 1, lean_box(0));
lean_closure_set(v___x_811_, 2, v_a_807_);
v___x_812_ = lean_apply_2(v_inst_806_, lean_box(0), v___x_811_);
v___x_813_ = lean_apply_4(v_toBind_809_, lean_box(0), lean_box(0), v___x_812_, v___f_810_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___boxed(lean_object* v_m_814_, lean_object* v_00_u03b1_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(v_m_814_, v_00_u03b1_815_, v_inst_816_, v_inst_817_, v_a_818_);
lean_dec(v_a_818_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_fst_820_, lean_object* v_x_821_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_fst_820_);
v_a_823_ = lean_ctor_get(v_x_821_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_821_);
if (v_isSharedCheck_831_ == 0)
{
v___x_825_ = v_x_821_;
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v_x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
}
else
{
lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_840_; 
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_821_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v_x_821_, 0);
lean_dec(v_unused_841_);
v___x_833_ = v_x_821_;
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
else
{
lean_dec(v_x_821_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v_fst_820_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_839_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; 
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_842_, lean_object* v_x_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(v_fst_842_, v_x_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
if (lean_obj_tag(v_x_851_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_a_853_ = lean_ctor_get(v_x_851_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x_851_);
if (v_isSharedCheck_861_ == 0)
{
v___x_855_ = v_x_851_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v_x_851_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_860_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_896_; 
v_a_862_ = lean_ctor_get(v_x_851_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_x_851_);
if (v_isSharedCheck_896_ == 0)
{
v___x_864_ = v_x_851_;
v_isShared_865_ = v_isSharedCheck_896_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v_x_851_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_896_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_values_866_; lean_object* v_consumers_867_; uint8_t v_closed_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_895_; 
v_values_866_ = lean_ctor_get(v_a_862_, 0);
v_consumers_867_ = lean_ctor_get(v_a_862_, 1);
v_closed_868_ = lean_ctor_get_uint8(v_a_862_, sizeof(void*)*2);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_895_ == 0)
{
v___x_870_ = v_a_862_;
v_isShared_871_ = v_isSharedCheck_895_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_consumers_867_);
lean_inc(v_values_866_);
lean_dec(v_a_862_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_895_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_Queue_dequeue_x3f___redArg(v_values_866_);
if (lean_obj_tag(v___x_872_) == 1)
{
lean_object* v_val_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_893_; 
v_val_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_893_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_val_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_fst_877_; lean_object* v_snd_878_; lean_object* v___x_880_; 
v_fst_877_ = lean_ctor_get(v_val_873_, 0);
lean_inc(v_fst_877_);
v_snd_878_ = lean_ctor_get(v_val_873_, 1);
lean_inc(v_snd_878_);
lean_dec(v_val_873_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_snd_878_);
v___x_880_ = v___x_870_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_snd_878_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_consumers_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*2, v_closed_868_);
v___x_880_ = v_reuseFailAlloc_892_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___f_882_; lean_object* v___x_884_; 
v___x_881_ = lean_st_ref_set(v_a_850_, v___x_880_);
v___f_882_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_882_, 0, v_fst_877_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_881_);
v___x_884_ = v___x_864_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_881_);
v___x_884_ = v_reuseFailAlloc_891_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 0);
lean_ctor_set(v___x_875_, 0, v___x_884_);
v___x_886_ = v___x_875_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_890_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = 0;
v___x_889_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_887_, v___x_888_, v___x_886_, v___f_882_);
return v___x_889_;
}
}
}
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v___x_872_);
lean_del_object(v___x_870_);
lean_dec_ref(v_consumers_867_);
lean_del_object(v___x_864_);
v___x_894_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_897_, lean_object* v_x_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_897_, v_x_898_);
lean_dec(v_a_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; 
v___x_903_ = lean_st_ref_get(v_a_901_);
lean_inc(v_a_901_);
v___f_904_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_904_, 0, v_a_901_);
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = 0;
v___x_909_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_907_, v___x_908_, v___x_906_, v___f_904_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_910_);
lean_dec(v_a_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_object* v_00_u03b1_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_917_, lean_object* v_a_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(v_00_u03b1_917_, v_a_918_);
lean_dec(v_a_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_promise_921_, lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_932_; 
v_a_924_ = lean_ctor_get(v_x_922_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_922_);
if (v_isSharedCheck_932_ == 0)
{
v___x_926_ = v_x_922_;
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v_x_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_931_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; 
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_io_promise_resolve(v_x_922_, v_promise_921_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_promise_936_, lean_object* v_x_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_936_, v_x_937_);
lean_dec(v_promise_936_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_940_, lean_object* v___y_941_, lean_object* v___f_942_, lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v___f_942_);
lean_dec_ref(v_lose_940_);
v_a_945_ = lean_ctor_get(v_x_943_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_943_);
if (v_isSharedCheck_953_ == 0)
{
v___x_947_ = v_x_943_;
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v_x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
}
else
{
lean_object* v_a_954_; uint8_t v___x_955_; 
v_a_954_ = lean_ctor_get(v_x_943_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v_x_943_, 1);
v___x_955_ = lean_unbox(v_a_954_);
lean_dec(v_a_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec_ref(v___f_942_);
lean_inc(v___y_941_);
v___x_956_ = lean_apply_2(v_lose_940_, v___y_941_, lean_box(0));
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; lean_object* v___x_960_; 
lean_dec_ref(v_lose_940_);
v___x_957_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_941_);
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = 0;
v___x_960_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_958_, v___x_959_, v___x_957_, v___f_942_);
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_961_, lean_object* v___y_962_, lean_object* v___f_963_, lean_object* v_x_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_961_, v___y_962_, v___f_963_, v_x_964_);
lean_dec(v___y_962_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object* v_w_967_, lean_object* v_lose_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_finished_971_; lean_object* v_promise_972_; lean_object* v___x_973_; lean_object* v___f_974_; lean_object* v___f_975_; uint8_t v___y_977_; uint8_t v___x_987_; 
v_finished_971_ = lean_ctor_get(v_w_967_, 0);
lean_inc(v_finished_971_);
v_promise_972_ = lean_ctor_get(v_w_967_, 1);
lean_inc(v_promise_972_);
lean_dec_ref(v_w_967_);
v___x_973_ = lean_st_ref_take(v_finished_971_);
v___f_974_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_974_, 0, v_promise_972_);
lean_inc(v___y_969_);
v___f_975_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_975_, 0, v_lose_968_);
lean_closure_set(v___f_975_, 1, v___y_969_);
lean_closure_set(v___f_975_, 2, v___f_974_);
v___x_987_ = lean_unbox(v___x_973_);
lean_dec(v___x_973_);
if (v___x_987_ == 0)
{
uint8_t v___x_988_; 
v___x_988_ = 1;
v___y_977_ = v___x_988_;
goto v___jp_976_;
}
else
{
uint8_t v___x_989_; 
v___x_989_ = 0;
v___y_977_ = v___x_989_;
goto v___jp_976_;
}
v___jp_976_:
{
uint8_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; lean_object* v___x_986_; 
v___x_978_ = 1;
v___x_979_ = lean_box(v___x_978_);
v___x_980_ = lean_st_ref_set(v_finished_971_, v___x_979_);
lean_dec(v_finished_971_);
v___x_981_ = lean_box(v___y_977_);
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = 0;
v___x_986_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_984_, v___x_985_, v___x_983_, v___f_975_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object* v_w_990_, lean_object* v_lose_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_990_, v_lose_991_, v___y_992_);
lean_dec(v___y_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object* v_00_u03b1_995_, lean_object* v_w_996_, lean_object* v_lose_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_996_, v_lose_997_, v___y_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_1001_, lean_object* v_w_1002_, lean_object* v_lose_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(v_00_u03b1_1001_, v_w_1002_, v_lose_1003_, v___y_1004_);
lean_dec(v___y_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_io_basemutex_unlock(v_mutex_1007_);
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_1013_, lean_object* v_x_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(v_mutex_1013_, v_x_1014_);
lean_dec(v_x_1014_);
lean_dec(v_mutex_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_1017_, lean_object* v_ref_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_ref_1018_);
lean_dec_ref(v_k_1017_);
v_a_1021_ = lean_ctor_get(v_x_1019_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1023_ = v_x_1019_;
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v_x_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
}
else
{
lean_object* v___x_1030_; 
lean_dec_ref_known(v_x_1019_, 1);
v___x_1030_ = lean_apply_2(v_k_1017_, v_ref_1018_, lean_box(0));
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_1031_, lean_object* v_ref_1032_, lean_object* v_x_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_k_1031_, v_ref_1032_, v_x_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_1036_, lean_object* v___f_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; 
v___x_1039_ = lean_io_basemutex_lock(v_mutex_1036_);
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = 0;
v___x_1044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1042_, v___x_1043_, v___x_1041_, v___f_1037_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_1045_, lean_object* v___f_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_mutex_1045_, v___f_1046_);
lean_dec(v_mutex_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_1049_){
_start:
{
if (lean_obj_tag(v___y_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_a_1050_ = lean_ctor_get(v___y_1049_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___y_1049_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___y_1049_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___y_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_a_1058_ = lean_ctor_get(v___y_1049_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___y_1049_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1060_ = v___y_1049_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___y_1049_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_fst_1062_; lean_object* v___x_1064_; 
v_fst_1062_ = lean_ctor_get(v_a_1058_, 0);
lean_inc(v_fst_1062_);
lean_dec(v_a_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v_fst_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_fst_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(lean_object* v_mutex_1068_, lean_object* v_k_1069_){
_start:
{
lean_object* v_ref_1071_; lean_object* v_mutex_1072_; lean_object* v___f_1073_; lean_object* v___f_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___y_1080_; 
v_ref_1071_ = lean_ctor_get(v_mutex_1068_, 0);
lean_inc(v_ref_1071_);
v_mutex_1072_ = lean_ctor_get(v_mutex_1068_, 1);
lean_inc_n(v_mutex_1072_, 2);
lean_dec_ref(v_mutex_1068_);
v___f_1073_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1073_, 0, v_mutex_1072_);
v___f_1074_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1074_, 0, v_k_1069_);
lean_closure_set(v___f_1074_, 1, v_ref_1071_);
v___f_1075_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1075_, 0, v_mutex_1072_);
lean_closure_set(v___f_1075_, 1, v___f_1074_);
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = 0;
v___x_1078_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1075_, v___f_1073_, v___x_1076_, v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1082_; 
v_a_1082_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1078_, 1);
if (lean_obj_tag(v_a_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v_a_1082_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_a_1082_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v_a_1082_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v_a_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v___y_1080_ = v___x_1088_;
goto v___jp_1079_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1099_; 
v_a_1091_ = lean_ctor_get(v_a_1082_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_a_1082_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1093_ = v_a_1082_;
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v_a_1082_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_fst_1095_; lean_object* v___x_1097_; 
v_fst_1095_ = lean_ctor_get(v_a_1091_, 0);
lean_inc(v_fst_1095_);
lean_dec(v_a_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v_fst_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fst_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
v___y_1080_ = v___x_1097_;
goto v___jp_1079_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1109_; 
v_a_1100_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1102_ = v___x_1078_;
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1078_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___f_1104_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0));
v___x_1105_ = lean_task_map(v___f_1104_, v_a_1100_, v___x_1076_, v___x_1077_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
v___jp_1079_:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___y_1080_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_1110_, lean_object* v_k_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1110_, v_k_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_object* v_00_u03b1_1114_, lean_object* v_00_u03b2_1115_, lean_object* v_mutex_1116_, lean_object* v_k_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1116_, v_k_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_00_u03b2_1121_, lean_object* v_mutex_1122_, lean_object* v_k_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(v_00_u03b1_1120_, v_00_u03b2_1121_, v_mutex_1122_, v_k_1123_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(lean_object* v_x_1126_){
_start:
{
if (lean_obj_tag(v_x_1126_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
v_a_1128_ = lean_ctor_get(v_x_1126_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1126_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1130_ = v_x_1126_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v_x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1146_; 
v_a_1137_ = lean_ctor_get(v_x_1126_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_x_1126_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1139_ = v_x_1126_;
v_isShared_1140_ = v_isSharedCheck_1146_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v_x_1126_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1146_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_a_1137_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1141_);
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(lean_object* v_x_1150_){
_start:
{
uint8_t v___y_1153_; 
if (lean_obj_tag(v_x_1150_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
v_a_1157_ = lean_ctor_get(v_x_1150_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1159_ = v_x_1150_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v_x_1150_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v_values_1167_; uint8_t v_closed_1168_; uint8_t v___x_1169_; 
v_a_1166_ = lean_ctor_get(v_x_1150_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v_x_1150_, 1);
v_values_1167_ = lean_ctor_get(v_a_1166_, 0);
lean_inc_ref(v_values_1167_);
v_closed_1168_ = lean_ctor_get_uint8(v_a_1166_, sizeof(void*)*2);
lean_dec(v_a_1166_);
v___x_1169_ = l_Std_Queue_isEmpty___redArg(v_values_1167_);
lean_dec_ref(v_values_1167_);
if (v___x_1169_ == 0)
{
uint8_t v___x_1170_; 
v___x_1170_ = 1;
v___y_1153_ = v___x_1170_;
goto v___jp_1152_;
}
else
{
v___y_1153_ = v_closed_1168_;
goto v___jp_1152_;
}
}
v___jp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_box(v___y_1153_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(lean_object* v_x_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(lean_object* v___x_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1174_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_1179_, v___y_1180_);
lean_dec(v___y_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(lean_object* v___y_1189_, lean_object* v_waiter_1190_, lean_object* v_x_1191_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_waiter_1190_);
v_a_1193_ = lean_ctor_get(v_x_1191_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1195_ = v_x_1191_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v_x_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; uint8_t v___x_1203_; 
v_a_1202_ = lean_ctor_get(v_x_1191_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v_x_1191_, 1);
v___x_1203_ = lean_unbox(v_a_1202_);
lean_dec(v_a_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v_values_1205_; lean_object* v_consumers_1206_; uint8_t v_closed_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1218_; 
v___x_1204_ = lean_st_ref_take(v___y_1189_);
v_values_1205_ = lean_ctor_get(v___x_1204_, 0);
v_consumers_1206_ = lean_ctor_get(v___x_1204_, 1);
v_closed_1207_ = lean_ctor_get_uint8(v___x_1204_, sizeof(void*)*2);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1209_ = v___x_1204_;
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_consumers_1206_);
lean_inc(v_values_1205_);
lean_dec(v___x_1204_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_waiter_1190_);
v___x_1212_ = l_Std_Queue_enqueue___redArg(v___x_1211_, v_consumers_1206_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1212_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_values_1205_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*2, v_closed_1207_);
v___x_1214_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_st_ref_set(v___y_1189_, v___x_1214_);
v___x_1216_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_1216_;
}
}
}
else
{
lean_object* v_lose_1219_; lean_object* v___x_1220_; 
v_lose_1219_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2));
v___x_1220_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_waiter_1190_, v_lose_1219_, v___y_1189_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(lean_object* v___y_1221_, lean_object* v_waiter_1222_, lean_object* v_x_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_1221_, v_waiter_1222_, v_x_1223_);
lean_dec(v___y_1221_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(lean_object* v___f_1226_, lean_object* v_waiter_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; 
v___x_1230_ = lean_st_ref_get(v___y_1228_);
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = 0;
v___x_1235_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1233_, v___x_1234_, v___x_1232_, v___f_1226_);
lean_inc(v___y_1228_);
v___f_1236_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1236_, 0, v___y_1228_);
lean_closure_set(v___f_1236_, 1, v_waiter_1227_);
v___x_1237_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1233_, v___x_1234_, v___x_1235_, v___f_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(lean_object* v___f_1238_, lean_object* v_waiter_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v___f_1238_, v_waiter_1239_, v___y_1240_);
lean_dec(v___y_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(lean_object* v___f_1243_, lean_object* v_ch_1244_, lean_object* v_waiter_1245_){
_start:
{
lean_object* v___f_1247_; lean_object* v___x_1248_; 
v___f_1247_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1247_, 0, v___f_1243_);
lean_closure_set(v___f_1247_, 1, v_waiter_1245_);
v___x_1248_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_1244_, v___f_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(lean_object* v___f_1249_, lean_object* v_ch_1250_, lean_object* v_waiter_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_1249_, v_ch_1250_, v_waiter_1251_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(lean_object* v___y_1258_, lean_object* v___f_1259_, lean_object* v_x_1260_){
_start:
{
if (lean_obj_tag(v_x_1260_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v___f_1259_);
v_a_1262_ = lean_ctor_get(v_x_1260_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_x_1260_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1264_ = v_x_1260_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v_x_1260_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
}
else
{
lean_object* v_a_1271_; uint8_t v___x_1272_; 
v_a_1271_ = lean_ctor_get(v_x_1260_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v_x_1260_, 1);
v___x_1272_ = lean_unbox(v_a_1271_);
lean_dec(v_a_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
lean_dec_ref(v___f_1259_);
v___x_1273_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1274_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_1258_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = 0;
v___x_1277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1275_, v___x_1276_, v___x_1274_, v___f_1259_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(lean_object* v___y_1278_, lean_object* v___f_1279_, lean_object* v_x_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_1278_, v___f_1279_, v_x_1280_);
lean_dec(v___y_1278_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(lean_object* v___f_1283_, lean_object* v___f_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; 
v___x_1287_ = lean_st_ref_get(v___y_1285_);
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = 0;
v___x_1292_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1290_, v___x_1291_, v___x_1289_, v___f_1283_);
lean_inc(v___y_1285_);
v___f_1293_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1293_, 0, v___y_1285_);
lean_closure_set(v___f_1293_, 1, v___f_1284_);
v___x_1294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1290_, v___x_1291_, v___x_1292_, v___f_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(lean_object* v___f_1295_, lean_object* v___f_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_1295_, v___f_1296_, v___y_1297_);
lean_dec(v___y_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(lean_object* v_values_1300_, uint8_t v_closed_1301_, lean_object* v___y_1302_, lean_object* v_x_1303_){
_start:
{
if (lean_obj_tag(v_x_1303_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_values_1300_);
v_a_1305_ = lean_ctor_get(v_x_1303_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_x_1303_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1307_ = v_x_1303_;
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v_x_1303_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1324_; 
v_a_1314_ = lean_ctor_get(v_x_1303_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_x_1303_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1316_ = v_x_1303_;
v_isShared_1317_ = v_isSharedCheck_1324_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v_x_1303_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1324_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1318_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1318_, 0, v_values_1300_);
lean_ctor_set(v___x_1318_, 1, v_a_1314_);
lean_ctor_set_uint8(v___x_1318_, sizeof(void*)*2, v_closed_1301_);
v___x_1319_ = lean_st_ref_set(v___y_1302_, v___x_1318_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1319_);
v___x_1321_ = v___x_1316_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed(lean_object* v_values_1325_, lean_object* v_closed_1326_, lean_object* v___y_1327_, lean_object* v_x_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v_closed_boxed_1330_; lean_object* v_res_1331_; 
v_closed_boxed_1330_ = lean_unbox(v_closed_1326_);
v_res_1331_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(v_values_1325_, v_closed_boxed_1330_, v___y_1327_, v_x_1328_);
lean_dec(v___y_1327_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_1332_){
_start:
{
if (lean_obj_tag(v_x_1332_) == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_x_1332_);
return v___x_1334_;
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1344_; 
v_a_1335_ = lean_ctor_get(v_x_1332_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_x_1332_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1337_ = v_x_1332_;
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v_x_1332_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = l_List_reverse___redArg(v_a_1335_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1341_ = v___x_1337_;
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(v_x_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_1348_, lean_object* v___x_1349_, lean_object* v_x_1350_){
_start:
{
if (lean_obj_tag(v_x_1350_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v___x_1349_);
lean_dec(v_a_1348_);
v_a_1352_ = lean_ctor_get(v_x_1350_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_x_1350_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v_x_1350_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v_x_1350_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1377_; 
v_a_1361_ = lean_ctor_get(v_x_1350_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1350_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1363_ = v_x_1350_;
v_isShared_1364_ = v_isSharedCheck_1377_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v_x_1350_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1377_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
uint8_t v___x_1365_; 
v___x_1365_ = l_List_isEmpty___redArg(v_a_1348_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec(v___x_1349_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1361_);
lean_ctor_set(v___x_1366_, 1, v_a_1348_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1366_);
v___x_1368_ = v___x_1363_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_dec(v_a_1348_);
v___x_1371_ = l_List_reverse___redArg(v_a_1361_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1349_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1372_);
v___x_1374_ = v___x_1363_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
return v___x_1375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_1378_, lean_object* v___x_1379_, lean_object* v_x_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(v_a_1378_, v___x_1379_, v_x_1380_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(lean_object* v_x_1383_){
_start:
{
uint8_t v___y_1386_; 
if (lean_obj_tag(v_x_1383_) == 0)
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_x_1383_);
return v___x_1390_;
}
else
{
lean_object* v_a_1391_; uint8_t v___x_1392_; 
v_a_1391_ = lean_ctor_get(v_x_1383_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v_x_1383_, 1);
v___x_1392_ = lean_unbox(v_a_1391_);
lean_dec(v_a_1391_);
if (v___x_1392_ == 0)
{
uint8_t v___x_1393_; 
v___x_1393_ = 1;
v___y_1386_ = v___x_1393_;
goto v___jp_1385_;
}
else
{
uint8_t v___x_1394_; 
v___x_1394_ = 0;
v___y_1386_ = v___x_1394_;
goto v___jp_1385_;
}
}
v___jp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = lean_box(v___y_1386_);
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(lean_object* v_x_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_tail_1398_, lean_object* v_x_1399_, lean_object* v_head_1400_, lean_object* v_x_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_1398_, v_x_1399_, v_head_1400_, v_x_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_x_1411_);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
else
{
lean_object* v_head_1415_; lean_object* v_tail_1416_; lean_object* v___f_1417_; lean_object* v_val_1419_; 
v_head_1415_ = lean_ctor_get(v_x_1410_, 0);
lean_inc_n(v_head_1415_, 2);
v_tail_1416_ = lean_ctor_get(v_x_1410_, 1);
lean_inc(v_tail_1416_);
lean_dec_ref_known(v_x_1410_, 2);
v___f_1417_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1417_, 0, v_tail_1416_);
lean_closure_set(v___f_1417_, 1, v_x_1411_);
lean_closure_set(v___f_1417_, 2, v_head_1415_);
if (lean_obj_tag(v_head_1415_) == 0)
{
lean_object* v___x_1423_; 
lean_dec_ref_known(v_head_1415_, 1);
v___x_1423_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_1419_ = v___x_1423_;
goto v___jp_1418_;
}
else
{
lean_object* v_finished_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1438_; 
v_finished_1424_ = lean_ctor_get(v_head_1415_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_head_1415_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1426_ = v_head_1415_;
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_finished_1424_);
lean_dec(v_head_1415_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_finished_1428_; lean_object* v___x_1429_; lean_object* v___f_1430_; lean_object* v___x_1432_; 
v_finished_1428_ = lean_ctor_get(v_finished_1424_, 0);
lean_inc(v_finished_1428_);
lean_dec_ref(v_finished_1424_);
v___x_1429_ = lean_st_ref_get(v_finished_1428_);
lean_dec(v_finished_1428_);
v___f_1430_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1429_);
v___x_1432_ = v___x_1426_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1429_);
v___x_1432_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; 
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = 0;
v___x_1436_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1434_, v___x_1435_, v___x_1433_, v___f_1430_);
v_val_1419_ = v___x_1436_;
goto v___jp_1418_;
}
}
}
v___jp_1418_:
{
lean_object* v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = 0;
v___x_1422_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1420_, v___x_1421_, v_val_1419_, v___f_1417_);
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object* v_tail_1439_, lean_object* v_x_1440_, lean_object* v_head_1441_, lean_object* v_x_1442_){
_start:
{
if (lean_obj_tag(v_x_1442_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v_head_1441_);
lean_dec(v_x_1440_);
lean_dec(v_tail_1439_);
v_a_1444_ = lean_ctor_get(v_x_1442_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_x_1442_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1446_ = v_x_1442_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v_x_1442_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
}
else
{
lean_object* v_a_1453_; uint8_t v___x_1454_; 
v_a_1453_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v_x_1442_, 1);
v___x_1454_ = lean_unbox(v_a_1453_);
lean_dec(v_a_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec_ref(v_head_1441_);
v___x_1455_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1439_, v_x_1440_);
return v___x_1455_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_head_1441_);
lean_ctor_set(v___x_1456_, 1, v_x_1440_);
v___x_1457_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1439_, v___x_1456_);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1458_, v_x_1459_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_1462_, lean_object* v___x_1463_, lean_object* v___f_1464_, lean_object* v_x_1465_){
_start:
{
if (lean_obj_tag(v_x_1465_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v___f_1464_);
lean_dec(v___x_1463_);
lean_dec(v_eList_1462_);
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
lean_object* v_a_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___f_1481_; lean_object* v___x_1482_; 
v_a_1476_ = lean_ctor_get(v_x_1465_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v_x_1465_, 1);
lean_inc(v___x_1463_);
v___x_1477_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_1462_, v___x_1463_);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = 0;
v___x_1480_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1478_, v___x_1479_, v___x_1477_, v___f_1464_);
v___f_1481_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1481_, 0, v_a_1476_);
lean_closure_set(v___f_1481_, 1, v___x_1463_);
v___x_1482_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1478_, v___x_1479_, v___x_1480_, v___f_1481_);
return v___x_1482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_1483_, lean_object* v___x_1484_, lean_object* v___f_1485_, lean_object* v_x_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v_eList_1483_, v___x_1484_, v___f_1485_, v_x_1486_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object* v_q_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_eList_1493_; lean_object* v_dList_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___f_1501_; lean_object* v___x_1502_; 
v_eList_1493_ = lean_ctor_get(v_q_1490_, 0);
lean_inc(v_eList_1493_);
v_dList_1494_ = lean_ctor_get(v_q_1490_, 1);
lean_inc(v_dList_1494_);
lean_dec_ref(v_q_1490_);
v___x_1495_ = lean_box(0);
v___x_1496_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_1494_, v___x_1495_);
v___f_1497_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = 0;
v___x_1500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1498_, v___x_1499_, v___x_1496_, v___f_1497_);
v___f_1501_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1501_, 0, v_eList_1493_);
lean_closure_set(v___f_1501_, 1, v___x_1495_);
lean_closure_set(v___f_1501_, 2, v___f_1497_);
v___x_1502_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1498_, v___x_1499_, v___x_1500_, v___f_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object* v_q_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1503_, v___y_1504_);
lean_dec(v___y_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object* v___y_1507_, lean_object* v_x_1508_){
_start:
{
if (lean_obj_tag(v_x_1508_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1518_; 
v_a_1510_ = lean_ctor_get(v_x_1508_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_x_1508_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1512_ = v_x_1508_;
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v_x_1508_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v_values_1520_; lean_object* v_consumers_1521_; uint8_t v_closed_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; 
v_a_1519_ = lean_ctor_get(v_x_1508_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v_x_1508_, 1);
v_values_1520_ = lean_ctor_get(v_a_1519_, 0);
lean_inc_ref(v_values_1520_);
v_consumers_1521_ = lean_ctor_get(v_a_1519_, 1);
lean_inc_ref(v_consumers_1521_);
v_closed_1522_ = lean_ctor_get_uint8(v_a_1519_, sizeof(void*)*2);
lean_dec(v_a_1519_);
v___x_1523_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_1521_, v___y_1507_);
v___x_1524_ = lean_box(v_closed_1522_);
lean_inc(v___y_1507_);
v___f_1525_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1525_, 0, v_values_1520_);
lean_closure_set(v___f_1525_, 1, v___x_1524_);
lean_closure_set(v___f_1525_, 2, v___y_1507_);
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = 0;
v___x_1528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1526_, v___x_1527_, v___x_1523_, v___f_1525_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object* v___y_1529_, lean_object* v_x_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1529_, v_x_1530_);
lean_dec(v___y_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; 
v___x_1535_ = lean_st_ref_get(v___y_1533_);
lean_inc(v___y_1533_);
v___f_1536_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1536_, 0, v___y_1533_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = 0;
v___x_1541_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1539_, v___x_1540_, v___x_1538_, v___f_1536_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1542_);
lean_dec(v___y_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object* v_ch_1551_){
_start:
{
lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___f_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___f_1552_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1));
lean_inc_ref_n(v_ch_1551_, 2);
v___f_1553_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1553_, 0, v___f_1552_);
lean_closure_set(v___f_1553_, 1, v_ch_1551_);
v___f_1554_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2));
v___f_1555_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3));
v___x_1556_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1556_, 0, lean_box(0));
lean_closure_set(v___x_1556_, 1, lean_box(0));
lean_closure_set(v___x_1556_, 2, v_ch_1551_);
lean_closure_set(v___x_1556_, 3, v___f_1554_);
v___x_1557_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1557_, 0, lean_box(0));
lean_closure_set(v___x_1557_, 1, lean_box(0));
lean_closure_set(v___x_1557_, 2, v_ch_1551_);
lean_closure_set(v___x_1557_, 3, v___f_1555_);
v___x_1558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___f_1553_);
lean_ctor_set(v___x_1558_, 2, v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object* v_00_u03b1_1559_, lean_object* v_ch_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object* v_00_u03b1_1562_, lean_object* v_q_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1563_, v___y_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_1567_, lean_object* v_q_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_1567_, v_q_1568_, v___y_1569_);
lean_dec(v___y_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object* v_00_u03b1_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1573_, v_x_1574_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_1578_, v_x_1579_, v_x_1580_, v___y_1581_);
lean_dec(v___y_1581_);
return v_res_1583_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_Queue_empty(lean_box(0));
return v___x_1584_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = 0;
v___x_1586_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0);
v___x_1587_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*2, v___x_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg(){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1);
v___x_1590_ = l_Std_Mutex_new___redArg(v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object* v_00_u03b1_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object* v_v_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; lean_object* v_producers_1612_; lean_object* v_consumers_1613_; uint8_t v_closed_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1637_; 
v___x_1611_ = lean_st_ref_get(v___y_1609_);
v_producers_1612_ = lean_ctor_get(v___x_1611_, 0);
v_consumers_1613_ = lean_ctor_get(v___x_1611_, 1);
v_closed_1614_ = lean_ctor_get_uint8(v___x_1611_, sizeof(void*)*2);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1616_ = v___x_1611_;
v_isShared_1617_ = v_isSharedCheck_1637_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_consumers_1613_);
lean_inc(v_producers_1612_);
lean_dec(v___x_1611_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1637_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_1613_);
if (lean_obj_tag(v___x_1618_) == 1)
{
lean_object* v_val_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1635_; 
v_val_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1635_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_val_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1635_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_fst_1623_; lean_object* v_snd_1624_; lean_object* v___x_1626_; 
v_fst_1623_ = lean_ctor_get(v_val_1619_, 0);
lean_inc(v_fst_1623_);
v_snd_1624_ = lean_ctor_get(v_val_1619_, 1);
lean_inc(v_snd_1624_);
lean_dec(v_val_1619_);
lean_inc(v_v_1608_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_v_1608_);
v___x_1626_ = v___x_1621_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_v_1608_);
v___x_1626_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
uint8_t v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_1623_, v___x_1626_);
lean_dec(v_fst_1623_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 1, v_snd_1624_);
v___x_1629_ = v___x_1616_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_producers_1612_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_snd_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*2, v_closed_1614_);
v___x_1629_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_st_ref_set(v___y_1609_, v___x_1629_);
if (v___x_1627_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_1632_; 
lean_dec(v_v_1608_);
v___x_1632_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0));
return v___x_1632_;
}
}
}
}
}
else
{
lean_object* v___x_1636_; 
lean_dec(v___x_1618_);
lean_del_object(v___x_1616_);
lean_dec_ref(v_producers_1612_);
lean_dec(v_v_1608_);
v___x_1636_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2));
return v___x_1636_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object* v_v_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1638_, v___y_1639_);
lean_dec(v___y_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object* v_v_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v_fst_1646_; 
v___x_1645_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1642_, v_a_1643_);
v_fst_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_fst_1646_);
lean_dec_ref(v___x_1645_);
if (lean_obj_tag(v_fst_1646_) == 0)
{
uint8_t v___x_1647_; 
v___x_1647_ = 1;
return v___x_1647_;
}
else
{
lean_object* v_val_1648_; uint8_t v___x_1649_; 
v_val_1648_ = lean_ctor_get(v_fst_1646_, 0);
lean_inc(v_val_1648_);
lean_dec_ref_known(v_fst_1646_, 1);
v___x_1649_ = lean_unbox(v_val_1648_);
lean_dec(v_val_1648_);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object* v_v_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
uint8_t v_res_1653_; lean_object* v_r_1654_; 
v_res_1653_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1650_, v_a_1651_);
lean_dec(v_a_1651_);
v_r_1654_ = lean_box(v_res_1653_);
return v_r_1654_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object* v_00_u03b1_1655_, lean_object* v_v_1656_, lean_object* v_a_1657_){
_start:
{
uint8_t v___x_1659_; 
v___x_1659_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1656_, v_a_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object* v_00_u03b1_1660_, lean_object* v_v_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
uint8_t v_res_1664_; lean_object* v_r_1665_; 
v_res_1664_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(v_00_u03b1_1660_, v_v_1661_, v_a_1662_);
lean_dec(v_a_1662_);
v_r_1665_ = lean_box(v_res_1664_);
return v_r_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object* v_00_u03b1_1666_, lean_object* v_v_1667_, lean_object* v_inst_1668_, lean_object* v_a_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1667_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_v_1674_, lean_object* v_inst_1675_, lean_object* v_a_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_1673_, v_v_1674_, v_inst_1675_, v_a_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object* v_v_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; uint8_t v_closed_1684_; 
v___x_1683_ = lean_st_ref_get(v___y_1681_);
v_closed_1684_ = lean_ctor_get_uint8(v___x_1683_, sizeof(void*)*2);
lean_dec(v___x_1683_);
if (v_closed_1684_ == 0)
{
uint8_t v___x_1685_; 
v___x_1685_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1680_, v___y_1681_);
return v___x_1685_;
}
else
{
uint8_t v___x_1686_; 
lean_dec(v_v_1680_);
v___x_1686_ = 0;
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object* v_v_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
uint8_t v_res_1690_; lean_object* v_r_1691_; 
v_res_1690_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1687_, v___y_1688_);
lean_dec(v___y_1688_);
v_r_1691_ = lean_box(v_res_1690_);
return v_r_1691_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object* v_ch_1692_, lean_object* v_v_1693_){
_start:
{
lean_object* v___f_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___f_1695_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1695_, 0, v_v_1693_);
v___x_1696_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1692_, v___f_1695_);
v___x_1697_ = lean_unbox(v___x_1696_);
lean_dec(v___x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object* v_ch_1698_, lean_object* v_v_1699_, lean_object* v_a_1700_){
_start:
{
uint8_t v_res_1701_; lean_object* v_r_1702_; 
v_res_1701_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1698_, v_v_1699_);
v_r_1702_ = lean_box(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object* v_00_u03b1_1703_, lean_object* v_ch_1704_, lean_object* v_v_1705_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1704_, v_v_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_ch_1709_, lean_object* v_v_1710_, lean_object* v_a_1711_){
_start:
{
uint8_t v_res_1712_; lean_object* v_r_1713_; 
v_res_1712_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(v_00_u03b1_1708_, v_ch_1709_, v_v_1710_);
v_r_1713_ = lean_box(v_res_1712_);
return v_r_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object* v_x_1714_){
_start:
{
if (lean_obj_tag(v_x_1714_) == 0)
{
goto v___jp_1715_;
}
else
{
lean_object* v_val_1717_; uint8_t v___x_1718_; 
v_val_1717_ = lean_ctor_get(v_x_1714_, 0);
v___x_1718_ = lean_unbox(v_val_1717_);
if (v___x_1718_ == 0)
{
goto v___jp_1715_;
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
return v___x_1719_;
}
}
v___jp_1715_:
{
lean_object* v___x_1716_; 
v___x_1716_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object* v_x_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_1720_);
lean_dec(v_x_1720_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object* v_v_1722_, lean_object* v___f_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; uint8_t v_closed_1727_; 
v___x_1726_ = lean_st_ref_get(v___y_1724_);
v_closed_1727_ = lean_ctor_get_uint8(v___x_1726_, sizeof(void*)*2);
lean_dec(v___x_1726_);
if (v_closed_1727_ == 0)
{
uint8_t v___x_1728_; 
lean_inc(v_v_1722_);
v___x_1728_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1722_, v___y_1724_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v_producers_1731_; lean_object* v_consumers_1732_; uint8_t v_closed_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1747_; 
v___x_1729_ = lean_io_promise_new();
v___x_1730_ = lean_st_ref_take(v___y_1724_);
v_producers_1731_ = lean_ctor_get(v___x_1730_, 0);
v_consumers_1732_ = lean_ctor_get(v___x_1730_, 1);
v_closed_1733_ = lean_ctor_get_uint8(v___x_1730_, sizeof(void*)*2);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1735_ = v___x_1730_;
v_isShared_1736_ = v_isSharedCheck_1747_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_consumers_1732_);
lean_inc(v_producers_1731_);
lean_dec(v___x_1730_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1747_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
lean_inc(v___x_1729_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_v_1722_);
lean_ctor_set(v___x_1737_, 1, v___x_1729_);
v___x_1738_ = l_Std_Queue_enqueue___redArg(v___x_1737_, v_producers_1731_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1738_);
v___x_1740_ = v___x_1735_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_consumers_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1746_, sizeof(void*)*2, v_closed_1733_);
v___x_1740_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1741_ = lean_st_ref_set(v___y_1724_, v___x_1740_);
v___x_1742_ = 1;
v___x_1743_ = lean_io_promise_result_opt(v___x_1729_);
lean_dec(v___x_1729_);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = lean_task_map(v___f_1723_, v___x_1743_, v___x_1744_, v___x_1742_);
return v___x_1745_;
}
}
}
else
{
lean_object* v___x_1748_; 
lean_dec_ref(v___f_1723_);
lean_dec(v_v_1722_);
v___x_1748_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_1748_;
}
}
else
{
lean_object* v___x_1749_; 
lean_dec_ref(v___f_1723_);
lean_dec(v_v_1722_);
v___x_1749_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object* v_v_1750_, lean_object* v___f_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1750_, v___f_1751_, v___y_1752_);
lean_dec(v___y_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object* v_ch_1756_, lean_object* v_v_1757_){
_start:
{
lean_object* v___f_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; 
v___f_1759_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0));
v___f_1760_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1760_, 0, v_v_1757_);
lean_closure_set(v___f_1760_, 1, v___f_1759_);
v___x_1761_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1756_, v___f_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object* v_ch_1762_, lean_object* v_v_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1762_, v_v_1763_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object* v_00_u03b1_1766_, lean_object* v_ch_1767_, lean_object* v_v_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1767_, v_v_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object* v_00_u03b1_1771_, lean_object* v_ch_1772_, lean_object* v_v_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(v_00_u03b1_1771_, v_ch_1772_, v_v_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object* v_as_1776_, size_t v_sz_1777_, size_t v_i_1778_, lean_object* v_b_1779_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_usize_dec_lt(v_i_1778_, v_sz_1777_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_b_1779_);
return v___x_1782_;
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; size_t v___x_1787_; size_t v___x_1788_; 
v_a_1783_ = lean_array_uget_borrowed(v_as_1776_, v_i_1778_);
v___x_1784_ = lean_box(0);
v___x_1785_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_1783_, v___x_1784_);
v___x_1786_ = lean_box(0);
v___x_1787_ = ((size_t)1ULL);
v___x_1788_ = lean_usize_add(v_i_1778_, v___x_1787_);
v_i_1778_ = v___x_1788_;
v_b_1779_ = v___x_1786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object* v_as_1790_, lean_object* v_sz_1791_, lean_object* v_i_1792_, lean_object* v_b_1793_, lean_object* v___y_1794_){
_start:
{
size_t v_sz_boxed_1795_; size_t v_i_boxed_1796_; lean_object* v_res_1797_; 
v_sz_boxed_1795_ = lean_unbox_usize(v_sz_1791_);
lean_dec(v_sz_1791_);
v_i_boxed_1796_ = lean_unbox_usize(v_i_1792_);
lean_dec(v_i_1792_);
v_res_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1790_, v_sz_boxed_1795_, v_i_boxed_1796_, v_b_1793_);
lean_dec_ref(v_as_1790_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; uint8_t v_closed_1801_; 
v___x_1800_ = lean_st_ref_get(v___y_1798_);
v_closed_1801_ = lean_ctor_get_uint8(v___x_1800_, sizeof(void*)*2);
if (v_closed_1801_ == 0)
{
lean_object* v_producers_1802_; lean_object* v_consumers_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1826_; 
v_producers_1802_ = lean_ctor_get(v___x_1800_, 0);
v_consumers_1803_ = lean_ctor_get(v___x_1800_, 1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1805_ = v___x_1800_;
v_isShared_1806_ = v_isSharedCheck_1826_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_consumers_1803_);
lean_inc(v_producers_1802_);
lean_dec(v___x_1800_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1826_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; size_t v_sz_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1807_ = l_Std_Queue_toArray___redArg(v_consumers_1803_);
v___x_1808_ = lean_box(0);
v_sz_1809_ = lean_array_size(v___x_1807_);
v___x_1810_ = ((size_t)0ULL);
v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_1807_, v_sz_1809_, v___x_1810_, v___x_1808_);
lean_dec_ref(v___x_1807_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1824_; 
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1811_, 0);
lean_dec(v_unused_1825_);
v___x_1813_ = v___x_1811_;
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
else
{
lean_dec(v___x_1811_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1818_; 
v___x_1815_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
v___x_1816_ = 1;
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1815_);
v___x_1818_ = v___x_1805_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_producers_1802_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1815_);
v___x_1818_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_ctor_set_uint8(v___x_1818_, sizeof(void*)*2, v___x_1816_);
v___x_1819_ = lean_st_ref_set(v___y_1798_, v___x_1818_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1808_);
v___x_1821_ = v___x_1813_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1808_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_del_object(v___x_1805_);
lean_dec_ref(v_producers_1802_);
return v___x_1811_;
}
}
}
else
{
uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec(v___x_1800_);
v___x_1827_ = 1;
v___x_1828_ = lean_box(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1830_);
lean_dec(v___y_1830_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object* v_ch_1834_){
_start:
{
lean_object* v___f_1836_; lean_object* v___x_1837_; 
v___f_1836_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0));
v___x_1837_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_1834_, v___f_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object* v_ch_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1838_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object* v_00_u03b1_1841_, lean_object* v_ch_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object* v_00_u03b1_1845_, lean_object* v_ch_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(v_00_u03b1_1845_, v_ch_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object* v_00_u03b1_1849_, lean_object* v_as_1850_, size_t v_sz_1851_, size_t v_i_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1850_, v_sz_1851_, v_i_1852_, v_b_1853_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object* v_00_u03b1_1857_, lean_object* v_as_1858_, lean_object* v_sz_1859_, lean_object* v_i_1860_, lean_object* v_b_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
size_t v_sz_boxed_1864_; size_t v_i_boxed_1865_; lean_object* v_res_1866_; 
v_sz_boxed_1864_ = lean_unbox_usize(v_sz_1859_);
lean_dec(v_sz_1859_);
v_i_boxed_1865_ = lean_unbox_usize(v_i_1860_);
lean_dec(v_i_1860_);
v_res_1866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_1857_, v_as_1858_, v_sz_boxed_1864_, v_i_boxed_1865_, v_b_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v_as_1858_);
return v_res_1866_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; uint8_t v_closed_1870_; 
v___x_1869_ = lean_st_ref_get(v___y_1867_);
v_closed_1870_ = lean_ctor_get_uint8(v___x_1869_, sizeof(void*)*2);
lean_dec(v___x_1869_);
return v_closed_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
uint8_t v_res_1873_; lean_object* v_r_1874_; 
v_res_1873_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1871_);
lean_dec(v___y_1871_);
v_r_1874_ = lean_box(v_res_1873_);
return v_r_1874_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object* v_ch_1876_){
_start:
{
lean_object* v___f_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___f_1878_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0));
v___x_1879_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1876_, v___f_1878_);
v___x_1880_ = lean_unbox(v___x_1879_);
lean_dec(v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object* v_ch_1881_, lean_object* v_a_1882_){
_start:
{
uint8_t v_res_1883_; lean_object* v_r_1884_; 
v_res_1883_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1881_);
v_r_1884_ = lean_box(v_res_1883_);
return v_r_1884_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object* v_00_u03b1_1885_, lean_object* v_ch_1886_){
_start:
{
uint8_t v___x_1888_; 
v___x_1888_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object* v_00_u03b1_1889_, lean_object* v_ch_1890_, lean_object* v_a_1891_){
_start:
{
uint8_t v_res_1892_; lean_object* v_r_1893_; 
v_res_1892_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(v_00_u03b1_1889_, v_ch_1890_);
v_r_1893_ = lean_box(v_res_1892_);
return v_r_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object* v_snd_1894_, lean_object* v_inst_1895_, lean_object* v_toBind_1896_, lean_object* v___f_1897_, lean_object* v_a_1898_){
_start:
{
uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1899_ = 1;
v___x_1900_ = lean_box(v___x_1899_);
v___x_1901_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1901_, 0, lean_box(0));
lean_closure_set(v___x_1901_, 1, v___x_1900_);
lean_closure_set(v___x_1901_, 2, v_snd_1894_);
v___x_1902_ = lean_apply_2(v_inst_1895_, lean_box(0), v___x_1901_);
v___x_1903_ = lean_apply_4(v_toBind_1896_, lean_box(0), lean_box(0), v___x_1902_, v___f_1897_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_1904_, lean_object* v_inst_1905_, lean_object* v_toBind_1906_, lean_object* v_a_1907_, lean_object* v_inst_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_producers_1910_; lean_object* v_consumers_1911_; uint8_t v_closed_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1933_; 
v_producers_1910_ = lean_ctor_get(v_a_1909_, 0);
v_consumers_1911_ = lean_ctor_get(v_a_1909_, 1);
v_closed_1912_ = lean_ctor_get_uint8(v_a_1909_, sizeof(void*)*2);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_a_1909_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1914_ = v_a_1909_;
v_isShared_1915_ = v_isSharedCheck_1933_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_consumers_1911_);
lean_inc(v_producers_1910_);
lean_dec(v_a_1909_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1933_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1910_);
if (lean_obj_tag(v___x_1916_) == 1)
{
lean_object* v_val_1917_; lean_object* v_fst_1918_; lean_object* v_snd_1919_; lean_object* v_fst_1920_; lean_object* v_snd_1921_; lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___x_1925_; 
v_val_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v_fst_1918_ = lean_ctor_get(v_val_1917_, 0);
lean_inc(v_fst_1918_);
v_snd_1919_ = lean_ctor_get(v_val_1917_, 1);
lean_inc(v_snd_1919_);
lean_dec(v_val_1917_);
v_fst_1920_ = lean_ctor_get(v_fst_1918_, 0);
lean_inc(v_fst_1920_);
v_snd_1921_ = lean_ctor_get(v_fst_1918_, 1);
lean_inc(v_snd_1921_);
lean_dec(v_fst_1918_);
v___f_1922_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1922_, 0, v_toApplicative_1904_);
lean_closure_set(v___f_1922_, 1, v_fst_1920_);
lean_inc(v_toBind_1906_);
v___f_1923_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1923_, 0, v_snd_1921_);
lean_closure_set(v___f_1923_, 1, v_inst_1905_);
lean_closure_set(v___f_1923_, 2, v_toBind_1906_);
lean_closure_set(v___f_1923_, 3, v___f_1922_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v_snd_1919_);
v___x_1925_ = v___x_1914_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_snd_1919_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_consumers_1911_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*2, v_closed_1912_);
v___x_1925_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_inc(v_a_1907_);
v___x_1926_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1926_, 0, lean_box(0));
lean_closure_set(v___x_1926_, 1, lean_box(0));
lean_closure_set(v___x_1926_, 2, v_a_1907_);
lean_closure_set(v___x_1926_, 3, v___x_1925_);
v___x_1927_ = lean_apply_2(v_inst_1908_, lean_box(0), v___x_1926_);
v___x_1928_ = lean_apply_4(v_toBind_1906_, lean_box(0), lean_box(0), v___x_1927_, v___f_1923_);
return v___x_1928_;
}
}
else
{
lean_object* v_toPure_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec(v___x_1916_);
lean_del_object(v___x_1914_);
lean_dec_ref(v_consumers_1911_);
lean_dec(v_inst_1908_);
lean_dec(v_toBind_1906_);
lean_dec(v_inst_1905_);
v_toPure_1930_ = lean_ctor_get(v_toApplicative_1904_, 1);
lean_inc(v_toPure_1930_);
lean_dec_ref(v_toApplicative_1904_);
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_apply_2(v_toPure_1930_, lean_box(0), v___x_1931_);
return v___x_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_1934_, lean_object* v_inst_1935_, lean_object* v_toBind_1936_, lean_object* v_a_1937_, lean_object* v_inst_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(v_toApplicative_1934_, v_inst_1935_, v_toBind_1936_, v_a_1937_, v_inst_1938_, v_a_1939_);
lean_dec(v_a_1937_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_toApplicative_1945_; lean_object* v_toBind_1946_; lean_object* v___f_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_toApplicative_1945_ = lean_ctor_get(v_inst_1941_, 0);
lean_inc_ref(v_toApplicative_1945_);
v_toBind_1946_ = lean_ctor_get(v_inst_1941_, 1);
lean_inc_n(v_toBind_1946_, 2);
lean_dec_ref(v_inst_1941_);
lean_inc(v_inst_1942_);
lean_inc_n(v_a_1944_, 2);
v___f_1947_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1947_, 0, v_toApplicative_1945_);
lean_closure_set(v___f_1947_, 1, v_inst_1943_);
lean_closure_set(v___f_1947_, 2, v_toBind_1946_);
lean_closure_set(v___f_1947_, 3, v_a_1944_);
lean_closure_set(v___f_1947_, 4, v_inst_1942_);
v___x_1948_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1948_, 0, lean_box(0));
lean_closure_set(v___x_1948_, 1, lean_box(0));
lean_closure_set(v___x_1948_, 2, v_a_1944_);
v___x_1949_ = lean_apply_2(v_inst_1942_, lean_box(0), v___x_1948_);
v___x_1950_ = lean_apply_4(v_toBind_1946_, lean_box(0), lean_box(0), v___x_1949_, v___f_1947_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1951_, v_inst_1952_, v_inst_1953_, v_a_1954_);
lean_dec(v_a_1954_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object* v_m_1956_, lean_object* v_00_u03b1_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1958_, v_inst_1959_, v_inst_1960_, v_a_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(lean_object* v_m_1963_, lean_object* v_00_u03b1_1964_, lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_inst_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(v_m_1963_, v_00_u03b1_1964_, v_inst_1965_, v_inst_1966_, v_inst_1967_, v_a_1968_);
lean_dec(v_a_1968_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; lean_object* v_producers_1973_; lean_object* v_consumers_1974_; uint8_t v_closed_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2000_; 
v___x_1972_ = lean_st_ref_get(v_a_1970_);
v_producers_1973_ = lean_ctor_get(v___x_1972_, 0);
v_consumers_1974_ = lean_ctor_get(v___x_1972_, 1);
v_closed_1975_ = lean_ctor_get_uint8(v___x_1972_, sizeof(void*)*2);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1977_ = v___x_1972_;
v_isShared_1978_ = v_isSharedCheck_2000_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_consumers_1974_);
lean_inc(v_producers_1973_);
lean_dec(v___x_1972_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2000_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1973_);
if (lean_obj_tag(v___x_1979_) == 1)
{
lean_object* v_val_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1998_; 
v_val_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1998_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_val_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1998_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_fst_1984_; lean_object* v_snd_1985_; lean_object* v_fst_1986_; lean_object* v_snd_1987_; lean_object* v___x_1989_; 
v_fst_1984_ = lean_ctor_get(v_val_1980_, 0);
lean_inc(v_fst_1984_);
v_snd_1985_ = lean_ctor_get(v_val_1980_, 1);
lean_inc(v_snd_1985_);
lean_dec(v_val_1980_);
v_fst_1986_ = lean_ctor_get(v_fst_1984_, 0);
lean_inc(v_fst_1986_);
v_snd_1987_ = lean_ctor_get(v_fst_1984_, 1);
lean_inc(v_snd_1987_);
lean_dec(v_fst_1984_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v_snd_1985_);
v___x_1989_ = v___x_1977_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_snd_1985_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_consumers_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1997_, sizeof(void*)*2, v_closed_1975_);
v___x_1989_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1990_ = lean_st_ref_set(v_a_1970_, v___x_1989_);
v___x_1991_ = 1;
v___x_1992_ = lean_box(v___x_1991_);
v___x_1993_ = lean_io_promise_resolve(v___x_1992_, v_snd_1987_);
lean_dec(v_snd_1987_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_fst_1986_);
v___x_1995_ = v___x_1982_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_fst_1986_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v___x_1999_; 
lean_dec(v___x_1979_);
lean_del_object(v___x_1977_);
lean_dec_ref(v_consumers_1974_);
v___x_1999_ = lean_box(0);
return v___x_1999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object* v_a_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_2001_);
lean_dec(v_a_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object* v_00_u03b1_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_2005_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_2008_, lean_object* v_a_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_2008_, v_a_2009_);
lean_dec(v_a_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object* v_ch_2013_){
_start:
{
lean_object* v___f_2015_; lean_object* v___x_2016_; 
v___f_2015_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0));
v___x_2016_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2013_, v___f_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object* v_ch_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object* v_00_u03b1_2020_, lean_object* v_ch_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_ch_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(v_00_u03b1_2024_, v_ch_2025_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object* v___f_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_st_ref_get(v___y_2029_);
v___x_2032_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_2029_);
if (lean_obj_tag(v___x_2032_) == 1)
{
lean_object* v___x_2033_; 
lean_dec(v___x_2031_);
lean_dec_ref(v___f_2028_);
v___x_2033_ = lean_task_pure(v___x_2032_);
return v___x_2033_;
}
else
{
uint8_t v_closed_2034_; 
lean_dec(v___x_2032_);
v_closed_2034_ = lean_ctor_get_uint8(v___x_2031_, sizeof(void*)*2);
if (v_closed_2034_ == 0)
{
lean_object* v_producers_2035_; lean_object* v_consumers_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2051_; 
v_producers_2035_ = lean_ctor_get(v___x_2031_, 0);
v_consumers_2036_ = lean_ctor_get(v___x_2031_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2038_ = v___x_2031_;
v_isShared_2039_ = v_isSharedCheck_2051_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_consumers_2036_);
lean_inc(v_producers_2035_);
lean_dec(v___x_2031_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2051_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2040_ = lean_io_promise_new();
lean_inc(v___x_2040_);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
v___x_2042_ = l_Std_Queue_enqueue___redArg(v___x_2041_, v_consumers_2036_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 1, v___x_2042_);
v___x_2044_ = v___x_2038_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_producers_2035_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*2, v_closed_2034_);
v___x_2044_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2045_ = lean_st_ref_set(v___y_2029_, v___x_2044_);
v___x_2046_ = 1;
v___x_2047_ = lean_io_promise_result_opt(v___x_2040_);
lean_dec(v___x_2040_);
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = lean_task_map(v___f_2028_, v___x_2047_, v___x_2048_, v___x_2046_);
return v___x_2049_;
}
}
}
else
{
lean_object* v___x_2052_; 
lean_dec(v___x_2031_);
lean_dec_ref(v___f_2028_);
v___x_2052_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object* v___f_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2053_, v___y_2054_);
lean_dec(v___y_2054_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object* v_ch_2059_){
_start:
{
lean_object* v___f_2061_; lean_object* v___x_2062_; 
v___f_2061_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0));
v___x_2062_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2059_, v___f_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object* v_ch_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object* v_00_u03b1_2066_, lean_object* v_ch_2067_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2067_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object* v_00_u03b1_2070_, lean_object* v_ch_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(v_00_u03b1_2070_, v_ch_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_2074_, lean_object* v_a_2075_){
_start:
{
uint8_t v___y_2077_; lean_object* v_producers_2081_; uint8_t v_closed_2082_; uint8_t v___x_2083_; 
v_producers_2081_ = lean_ctor_get(v_a_2075_, 0);
v_closed_2082_ = lean_ctor_get_uint8(v_a_2075_, sizeof(void*)*2);
v___x_2083_ = l_Std_Queue_isEmpty___redArg(v_producers_2081_);
if (v___x_2083_ == 0)
{
uint8_t v___x_2084_; 
v___x_2084_ = 1;
v___y_2077_ = v___x_2084_;
goto v___jp_2076_;
}
else
{
v___y_2077_ = v_closed_2082_;
goto v___jp_2076_;
}
v___jp_2076_:
{
lean_object* v_toPure_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_toPure_2078_ = lean_ctor_get(v_toApplicative_2074_, 1);
lean_inc(v_toPure_2078_);
lean_dec_ref(v_toApplicative_2074_);
v___x_2079_ = lean_box(v___y_2077_);
v___x_2080_ = lean_apply_2(v_toPure_2078_, lean_box(0), v___x_2079_);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(v_toApplicative_2085_, v_a_2086_);
lean_dec_ref(v_a_2086_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_toApplicative_2091_; lean_object* v_toBind_2092_; lean_object* v___f_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_toApplicative_2091_ = lean_ctor_get(v_inst_2088_, 0);
lean_inc_ref(v_toApplicative_2091_);
v_toBind_2092_ = lean_ctor_get(v_inst_2088_, 1);
lean_inc(v_toBind_2092_);
lean_dec_ref(v_inst_2088_);
v___f_2093_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2093_, 0, v_toApplicative_2091_);
lean_inc(v_a_2090_);
v___x_2094_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2094_, 0, lean_box(0));
lean_closure_set(v___x_2094_, 1, lean_box(0));
lean_closure_set(v___x_2094_, 2, v_a_2090_);
v___x_2095_ = lean_apply_2(v_inst_2089_, lean_box(0), v___x_2094_);
v___x_2096_ = lean_apply_4(v_toBind_2092_, lean_box(0), lean_box(0), v___x_2095_, v___f_2093_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(v_inst_2097_, v_inst_2098_, v_a_2099_);
lean_dec(v_a_2099_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object* v_m_2101_, lean_object* v_00_u03b1_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_toApplicative_2106_; lean_object* v_toBind_2107_; lean_object* v___f_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_toApplicative_2106_ = lean_ctor_get(v_inst_2103_, 0);
lean_inc_ref(v_toApplicative_2106_);
v_toBind_2107_ = lean_ctor_get(v_inst_2103_, 1);
lean_inc(v_toBind_2107_);
lean_dec_ref(v_inst_2103_);
v___f_2108_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2108_, 0, v_toApplicative_2106_);
lean_inc(v_a_2105_);
v___x_2109_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2109_, 0, lean_box(0));
lean_closure_set(v___x_2109_, 1, lean_box(0));
lean_closure_set(v___x_2109_, 2, v_a_2105_);
v___x_2110_ = lean_apply_2(v_inst_2104_, lean_box(0), v___x_2109_);
v___x_2111_ = lean_apply_4(v_toBind_2107_, lean_box(0), lean_box(0), v___x_2110_, v___f_2108_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(lean_object* v_m_2112_, lean_object* v_00_u03b1_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(v_m_2112_, v_00_u03b1_2113_, v_inst_2114_, v_inst_2115_, v_a_2116_);
lean_dec(v_a_2116_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object* v_snd_2118_, lean_object* v___f_2119_, lean_object* v_x_2120_){
_start:
{
if (lean_obj_tag(v_x_2120_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v___f_2119_);
v_a_2122_ = lean_ctor_get(v_x_2120_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_x_2120_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2124_ = v_x_2120_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v_x_2120_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
}
}
else
{
lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2144_; 
v_isSharedCheck_2144_ = !lean_is_exclusive(v_x_2120_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v_x_2120_, 0);
lean_dec(v_unused_2145_);
v___x_2132_ = v_x_2120_;
v_isShared_2133_ = v_isSharedCheck_2144_;
goto v_resetjp_2131_;
}
else
{
lean_dec(v_x_2120_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2144_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2134_ = 1;
v___x_2135_ = lean_box(v___x_2134_);
v___x_2136_ = lean_io_promise_resolve(v___x_2135_, v_snd_2118_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2136_);
v___x_2138_ = v___x_2132_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
v___x_2140_ = lean_unsigned_to_nat(0u);
v___x_2141_ = 0;
v___x_2142_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2140_, v___x_2141_, v___x_2139_, v___f_2119_);
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_snd_2146_, lean_object* v___f_2147_, lean_object* v_x_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2146_, v___f_2147_, v_x_2148_);
lean_dec(v_snd_2146_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object* v_a_2151_, lean_object* v_x_2152_){
_start:
{
if (lean_obj_tag(v_x_2152_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2162_; 
v_a_2154_ = lean_ctor_get(v_x_2152_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_x_2152_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2156_ = v_x_2152_;
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v_x_2152_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2200_; 
v_a_2163_ = lean_ctor_get(v_x_2152_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_x_2152_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2165_ = v_x_2152_;
v_isShared_2166_ = v_isSharedCheck_2200_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v_x_2152_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2200_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v_producers_2167_; lean_object* v_consumers_2168_; uint8_t v_closed_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2199_; 
v_producers_2167_ = lean_ctor_get(v_a_2163_, 0);
v_consumers_2168_ = lean_ctor_get(v_a_2163_, 1);
v_closed_2169_ = lean_ctor_get_uint8(v_a_2163_, sizeof(void*)*2);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_a_2163_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2171_ = v_a_2163_;
v_isShared_2172_ = v_isSharedCheck_2199_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_consumers_2168_);
lean_inc(v_producers_2167_);
lean_dec(v_a_2163_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2199_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2167_);
if (lean_obj_tag(v___x_2173_) == 1)
{
lean_object* v_val_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2197_; 
v_val_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2197_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_val_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2197_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v_fst_2180_; lean_object* v_snd_2181_; lean_object* v___x_2183_; 
v_fst_2178_ = lean_ctor_get(v_val_2174_, 0);
lean_inc(v_fst_2178_);
v_snd_2179_ = lean_ctor_get(v_val_2174_, 1);
lean_inc(v_snd_2179_);
lean_dec(v_val_2174_);
v_fst_2180_ = lean_ctor_get(v_fst_2178_, 0);
lean_inc(v_fst_2180_);
v_snd_2181_ = lean_ctor_get(v_fst_2178_, 1);
lean_inc(v_snd_2181_);
lean_dec(v_fst_2178_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v_snd_2179_);
v___x_2183_ = v___x_2171_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_snd_2179_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_consumers_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2196_, sizeof(void*)*2, v_closed_2169_);
v___x_2183_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v___f_2185_; lean_object* v___f_2186_; lean_object* v___x_2188_; 
v___x_2184_ = lean_st_ref_set(v_a_2151_, v___x_2183_);
v___f_2185_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2185_, 0, v_fst_2180_);
v___f_2186_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2186_, 0, v_snd_2181_);
lean_closure_set(v___f_2186_, 1, v___f_2185_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2184_);
v___x_2188_ = v___x_2165_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2184_);
v___x_2188_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2190_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2188_);
v___x_2190_ = v___x_2176_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = 0;
v___x_2193_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2191_, v___x_2192_, v___x_2190_, v___f_2186_);
return v___x_2193_;
}
}
}
}
}
else
{
lean_object* v___x_2198_; 
lean_dec(v___x_2173_);
lean_del_object(v___x_2171_);
lean_dec_ref(v_consumers_2168_);
lean_del_object(v___x_2165_);
v___x_2198_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_a_2201_, lean_object* v_x_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2201_, v_x_2202_);
lean_dec(v_a_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object* v_a_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v___f_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; lean_object* v___x_2213_; 
v___x_2207_ = lean_st_ref_get(v_a_2205_);
lean_inc(v_a_2205_);
v___f_2208_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2208_, 0, v_a_2205_);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = 0;
v___x_2213_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2211_, v___x_2212_, v___x_2210_, v___f_2208_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object* v_a_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2214_);
lean_dec(v_a_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object* v_00_u03b1_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_a_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_2221_, v_a_2222_);
lean_dec(v_a_2222_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_2225_, lean_object* v___y_2226_, lean_object* v___f_2227_, lean_object* v_x_2228_){
_start:
{
if (lean_obj_tag(v_x_2228_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v___f_2227_);
lean_dec_ref(v_lose_2225_);
v_a_2230_ = lean_ctor_get(v_x_2228_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_x_2228_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2232_ = v_x_2228_;
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v_x_2228_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
}
else
{
lean_object* v_a_2239_; uint8_t v___x_2240_; 
v_a_2239_ = lean_ctor_get(v_x_2228_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v_x_2228_, 1);
v___x_2240_ = lean_unbox(v_a_2239_);
lean_dec(v_a_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
lean_dec_ref(v___f_2227_);
lean_inc(v___y_2226_);
v___x_2241_ = lean_apply_2(v_lose_2225_, v___y_2226_, lean_box(0));
return v___x_2241_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; lean_object* v___x_2245_; 
lean_dec_ref(v_lose_2225_);
v___x_2242_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2226_);
v___x_2243_ = lean_unsigned_to_nat(0u);
v___x_2244_ = 0;
v___x_2245_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2243_, v___x_2244_, v___x_2242_, v___f_2227_);
return v___x_2245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_2246_, lean_object* v___y_2247_, lean_object* v___f_2248_, lean_object* v_x_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2246_, v___y_2247_, v___f_2248_, v_x_2249_);
lean_dec(v___y_2247_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object* v_w_2252_, lean_object* v_lose_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_finished_2256_; lean_object* v_promise_2257_; lean_object* v___x_2258_; lean_object* v___f_2259_; lean_object* v___f_2260_; uint8_t v___y_2262_; uint8_t v___x_2272_; 
v_finished_2256_ = lean_ctor_get(v_w_2252_, 0);
lean_inc(v_finished_2256_);
v_promise_2257_ = lean_ctor_get(v_w_2252_, 1);
lean_inc(v_promise_2257_);
lean_dec_ref(v_w_2252_);
v___x_2258_ = lean_st_ref_take(v_finished_2256_);
v___f_2259_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2259_, 0, v_promise_2257_);
lean_inc(v___y_2254_);
v___f_2260_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2260_, 0, v_lose_2253_);
lean_closure_set(v___f_2260_, 1, v___y_2254_);
lean_closure_set(v___f_2260_, 2, v___f_2259_);
v___x_2272_ = lean_unbox(v___x_2258_);
lean_dec(v___x_2258_);
if (v___x_2272_ == 0)
{
uint8_t v___x_2273_; 
v___x_2273_ = 1;
v___y_2262_ = v___x_2273_;
goto v___jp_2261_;
}
else
{
uint8_t v___x_2274_; 
v___x_2274_ = 0;
v___y_2262_ = v___x_2274_;
goto v___jp_2261_;
}
v___jp_2261_:
{
uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; lean_object* v___x_2271_; 
v___x_2263_ = 1;
v___x_2264_ = lean_box(v___x_2263_);
v___x_2265_ = lean_st_ref_set(v_finished_2256_, v___x_2264_);
lean_dec(v_finished_2256_);
v___x_2266_ = lean_box(v___y_2262_);
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = 0;
v___x_2271_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2269_, v___x_2270_, v___x_2268_, v___f_2260_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object* v_w_2275_, lean_object* v_lose_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2275_, v_lose_2276_, v___y_2277_);
lean_dec(v___y_2277_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object* v_00_u03b1_2280_, lean_object* v_w_2281_, lean_object* v_lose_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2281_, v_lose_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_2286_, lean_object* v_w_2287_, lean_object* v_lose_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_2286_, v_w_2287_, v_lose_2288_, v___y_2289_);
lean_dec(v___y_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object* v_x_2292_){
_start:
{
uint8_t v___y_2295_; 
if (lean_obj_tag(v_x_2292_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2307_; 
v_a_2299_ = lean_ctor_get(v_x_2292_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_x_2292_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2301_ = v_x_2292_;
v_isShared_2302_ = v_isSharedCheck_2307_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v_x_2292_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2307_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
return v___x_2305_;
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v_producers_2309_; uint8_t v_closed_2310_; uint8_t v___x_2311_; 
v_a_2308_ = lean_ctor_get(v_x_2292_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v_x_2292_, 1);
v_producers_2309_ = lean_ctor_get(v_a_2308_, 0);
lean_inc_ref(v_producers_2309_);
v_closed_2310_ = lean_ctor_get_uint8(v_a_2308_, sizeof(void*)*2);
lean_dec(v_a_2308_);
v___x_2311_ = l_Std_Queue_isEmpty___redArg(v_producers_2309_);
lean_dec_ref(v_producers_2309_);
if (v___x_2311_ == 0)
{
uint8_t v___x_2312_; 
v___x_2312_ = 1;
v___y_2295_ = v___x_2312_;
goto v___jp_2294_;
}
else
{
v___y_2295_ = v_closed_2310_;
goto v___jp_2294_;
}
}
v___jp_2294_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_box(v___y_2295_);
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object* v_x_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2313_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object* v___y_2316_, lean_object* v_waiter_2317_, lean_object* v_x_2318_){
_start:
{
if (lean_obj_tag(v_x_2318_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_waiter_2317_);
v_a_2320_ = lean_ctor_get(v_x_2318_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_x_2318_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2322_ = v_x_2318_;
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v_x_2318_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
}
else
{
lean_object* v_a_2329_; uint8_t v___x_2330_; 
v_a_2329_ = lean_ctor_get(v_x_2318_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v_x_2318_, 1);
v___x_2330_ = lean_unbox(v_a_2329_);
lean_dec(v_a_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v_producers_2332_; lean_object* v_consumers_2333_; uint8_t v_closed_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2345_; 
v___x_2331_ = lean_st_ref_take(v___y_2316_);
v_producers_2332_ = lean_ctor_get(v___x_2331_, 0);
v_consumers_2333_ = lean_ctor_get(v___x_2331_, 1);
v_closed_2334_ = lean_ctor_get_uint8(v___x_2331_, sizeof(void*)*2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2336_ = v___x_2331_;
v_isShared_2337_ = v_isSharedCheck_2345_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_consumers_2333_);
lean_inc(v_producers_2332_);
lean_dec(v___x_2331_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2345_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2338_, 0, v_waiter_2317_);
v___x_2339_ = l_Std_Queue_enqueue___redArg(v___x_2338_, v_consumers_2333_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2339_);
v___x_2341_ = v___x_2336_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_producers_2332_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2339_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, sizeof(void*)*2, v_closed_2334_);
v___x_2341_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_st_ref_set(v___y_2316_, v___x_2341_);
v___x_2343_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_2343_;
}
}
}
else
{
lean_object* v_lose_2346_; lean_object* v___x_2347_; 
v_lose_2346_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2));
v___x_2347_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_2317_, v_lose_2346_, v___y_2316_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object* v___y_2348_, lean_object* v_waiter_2349_, lean_object* v_x_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2348_, v_waiter_2349_, v_x_2350_);
lean_dec(v___y_2348_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object* v___f_2353_, lean_object* v_waiter_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___f_2363_; lean_object* v___x_2364_; 
v___x_2357_ = lean_st_ref_get(v___y_2355_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
v___x_2360_ = lean_unsigned_to_nat(0u);
v___x_2361_ = 0;
v___x_2362_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2360_, v___x_2361_, v___x_2359_, v___f_2353_);
lean_inc(v___y_2355_);
v___f_2363_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2363_, 0, v___y_2355_);
lean_closure_set(v___f_2363_, 1, v_waiter_2354_);
v___x_2364_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2360_, v___x_2361_, v___x_2362_, v___f_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object* v___f_2365_, lean_object* v_waiter_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v___f_2365_, v_waiter_2366_, v___y_2367_);
lean_dec(v___y_2367_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object* v___f_2370_, lean_object* v_ch_2371_, lean_object* v_waiter_2372_){
_start:
{
lean_object* v___f_2374_; lean_object* v___x_2375_; 
v___f_2374_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2374_, 0, v___f_2370_);
lean_closure_set(v___f_2374_, 1, v_waiter_2372_);
v___x_2375_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_2371_, v___f_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object* v___f_2376_, lean_object* v_ch_2377_, lean_object* v_waiter_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2376_, v_ch_2377_, v_waiter_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object* v___y_2381_, lean_object* v___f_2382_, lean_object* v_x_2383_){
_start:
{
if (lean_obj_tag(v_x_2383_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v___f_2382_);
v_a_2385_ = lean_ctor_get(v_x_2383_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_x_2383_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2387_ = v_x_2383_;
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v_x_2383_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
}
}
else
{
lean_object* v_a_2394_; uint8_t v___x_2395_; 
v_a_2394_ = lean_ctor_get(v_x_2383_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v_x_2383_, 1);
v___x_2395_ = lean_unbox(v_a_2394_);
lean_dec(v_a_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
lean_dec_ref(v___f_2382_);
v___x_2396_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_2396_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2397_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2381_);
v___x_2398_ = lean_unsigned_to_nat(0u);
v___x_2399_ = 0;
v___x_2400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2398_, v___x_2399_, v___x_2397_, v___f_2382_);
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object* v___y_2401_, lean_object* v___f_2402_, lean_object* v_x_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2401_, v___f_2402_, v_x_2403_);
lean_dec(v___y_2401_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object* v___f_2406_, lean_object* v___f_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___f_2416_; lean_object* v___x_2417_; 
v___x_2410_ = lean_st_ref_get(v___y_2408_);
v___x_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
v___x_2413_ = lean_unsigned_to_nat(0u);
v___x_2414_ = 0;
v___x_2415_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2413_, v___x_2414_, v___x_2412_, v___f_2406_);
lean_inc(v___y_2408_);
v___f_2416_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2416_, 0, v___y_2408_);
lean_closure_set(v___f_2416_, 1, v___f_2407_);
v___x_2417_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2413_, v___x_2414_, v___x_2415_, v___f_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object* v___f_2418_, lean_object* v___f_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2418_, v___f_2419_, v___y_2420_);
lean_dec(v___y_2420_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object* v_producers_2423_, uint8_t v_closed_2424_, lean_object* v___y_2425_, lean_object* v_x_2426_){
_start:
{
if (lean_obj_tag(v_x_2426_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2436_; 
lean_dec_ref(v_producers_2423_);
v_a_2428_ = lean_ctor_get(v_x_2426_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_x_2426_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2430_ = v_x_2426_;
v_isShared_2431_ = v_isSharedCheck_2436_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v_x_2426_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2436_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2447_; 
v_a_2437_ = lean_ctor_get(v_x_2426_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_x_2426_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2439_ = v_x_2426_;
v_isShared_2440_ = v_isSharedCheck_2447_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v_x_2426_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2447_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2441_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2441_, 0, v_producers_2423_);
lean_ctor_set(v___x_2441_, 1, v_a_2437_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*2, v_closed_2424_);
v___x_2442_ = lean_st_ref_set(v___y_2425_, v___x_2441_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2442_);
v___x_2444_ = v___x_2439_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object* v_producers_2448_, lean_object* v_closed_2449_, lean_object* v___y_2450_, lean_object* v_x_2451_, lean_object* v___y_2452_){
_start:
{
uint8_t v_closed_boxed_2453_; lean_object* v_res_2454_; 
v_closed_boxed_2453_ = lean_unbox(v_closed_2449_);
v_res_2454_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2448_, v_closed_boxed_2453_, v___y_2450_, v_x_2451_);
lean_dec(v___y_2450_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_2455_, lean_object* v_x_2456_, lean_object* v_head_2457_, lean_object* v_x_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2455_, v_x_2456_, v_head_2457_, v_x_2458_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object* v_x_2461_, lean_object* v_x_2462_){
_start:
{
if (lean_obj_tag(v_x_2461_) == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v_x_2462_);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
else
{
lean_object* v_head_2466_; lean_object* v_tail_2467_; lean_object* v___f_2468_; lean_object* v_val_2470_; 
v_head_2466_ = lean_ctor_get(v_x_2461_, 0);
lean_inc_n(v_head_2466_, 2);
v_tail_2467_ = lean_ctor_get(v_x_2461_, 1);
lean_inc(v_tail_2467_);
lean_dec_ref_known(v_x_2461_, 2);
v___f_2468_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2468_, 0, v_tail_2467_);
lean_closure_set(v___f_2468_, 1, v_x_2462_);
lean_closure_set(v___f_2468_, 2, v_head_2466_);
if (lean_obj_tag(v_head_2466_) == 0)
{
lean_object* v___x_2474_; 
lean_dec_ref_known(v_head_2466_, 1);
v___x_2474_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_2470_ = v___x_2474_;
goto v___jp_2469_;
}
else
{
lean_object* v_finished_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2489_; 
v_finished_2475_ = lean_ctor_get(v_head_2466_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_head_2466_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2477_ = v_head_2466_;
v_isShared_2478_ = v_isSharedCheck_2489_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_finished_2475_);
lean_dec(v_head_2466_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2489_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_finished_2479_; lean_object* v___x_2480_; lean_object* v___f_2481_; lean_object* v___x_2483_; 
v_finished_2479_ = lean_ctor_get(v_finished_2475_, 0);
lean_inc(v_finished_2479_);
lean_dec_ref(v_finished_2475_);
v___x_2480_ = lean_st_ref_get(v_finished_2479_);
lean_dec(v_finished_2479_);
v___f_2481_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2480_);
v___x_2483_ = v___x_2477_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2480_);
v___x_2483_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = 0;
v___x_2487_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2485_, v___x_2486_, v___x_2484_, v___f_2481_);
v_val_2470_ = v___x_2487_;
goto v___jp_2469_;
}
}
}
v___jp_2469_:
{
lean_object* v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = lean_unsigned_to_nat(0u);
v___x_2472_ = 0;
v___x_2473_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2471_, v___x_2472_, v_val_2470_, v___f_2468_);
return v___x_2473_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_2490_, lean_object* v_x_2491_, lean_object* v_head_2492_, lean_object* v_x_2493_){
_start:
{
if (lean_obj_tag(v_x_2493_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v_head_2492_);
lean_dec(v_x_2491_);
lean_dec(v_tail_2490_);
v_a_2495_ = lean_ctor_get(v_x_2493_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_x_2493_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2497_ = v_x_2493_;
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v_x_2493_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
}
else
{
lean_object* v_a_2504_; uint8_t v___x_2505_; 
v_a_2504_ = lean_ctor_get(v_x_2493_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v_x_2493_, 1);
v___x_2505_ = lean_unbox(v_a_2504_);
lean_dec(v_a_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
lean_dec_ref(v_head_2492_);
v___x_2506_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2490_, v_x_2491_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v_head_2492_);
lean_ctor_set(v___x_2507_, 1, v_x_2491_);
v___x_2508_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2490_, v___x_2507_);
return v___x_2508_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object* v_x_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2509_, v_x_2510_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object* v_eList_2513_, lean_object* v___x_2514_, lean_object* v___f_2515_, lean_object* v_x_2516_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v___f_2515_);
lean_dec(v___x_2514_);
lean_dec(v_eList_2513_);
v_a_2518_ = lean_ctor_get(v_x_2516_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_x_2516_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2520_ = v_x_2516_;
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v_x_2516_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
return v___x_2524_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___f_2532_; lean_object* v___x_2533_; 
v_a_2527_ = lean_ctor_get(v_x_2516_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v_x_2516_, 1);
lean_inc(v___x_2514_);
v___x_2528_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_2513_, v___x_2514_);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = 0;
v___x_2531_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2529_, v___x_2530_, v___x_2528_, v___f_2515_);
v___f_2532_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2532_, 0, v_a_2527_);
lean_closure_set(v___f_2532_, 1, v___x_2514_);
v___x_2533_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2529_, v___x_2530_, v___x_2531_, v___f_2532_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_eList_2534_, lean_object* v___x_2535_, lean_object* v___f_2536_, lean_object* v_x_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v_eList_2534_, v___x_2535_, v___f_2536_, v_x_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object* v_q_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_eList_2543_; lean_object* v_dList_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___f_2551_; lean_object* v___x_2552_; 
v_eList_2543_ = lean_ctor_get(v_q_2540_, 0);
lean_inc(v_eList_2543_);
v_dList_2544_ = lean_ctor_get(v_q_2540_, 1);
lean_inc(v_dList_2544_);
lean_dec_ref(v_q_2540_);
v___x_2545_ = lean_box(0);
v___x_2546_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_2544_, v___x_2545_);
v___f_2547_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_2548_ = lean_unsigned_to_nat(0u);
v___x_2549_ = 0;
v___x_2550_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2548_, v___x_2549_, v___x_2546_, v___f_2547_);
v___f_2551_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2551_, 0, v_eList_2543_);
lean_closure_set(v___f_2551_, 1, v___x_2545_);
lean_closure_set(v___f_2551_, 2, v___f_2547_);
v___x_2552_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2548_, v___x_2549_, v___x_2550_, v___f_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object* v_q_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2553_, v___y_2554_);
lean_dec(v___y_2554_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object* v___y_2557_, lean_object* v_x_2558_){
_start:
{
if (lean_obj_tag(v_x_2558_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2568_; 
v_a_2560_ = lean_ctor_get(v_x_2558_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_x_2558_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2562_ = v_x_2558_;
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v_x_2558_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v_producers_2570_; lean_object* v_consumers_2571_; uint8_t v_closed_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___f_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; 
v_a_2569_ = lean_ctor_get(v_x_2558_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v_x_2558_, 1);
v_producers_2570_ = lean_ctor_get(v_a_2569_, 0);
lean_inc_ref(v_producers_2570_);
v_consumers_2571_ = lean_ctor_get(v_a_2569_, 1);
lean_inc_ref(v_consumers_2571_);
v_closed_2572_ = lean_ctor_get_uint8(v_a_2569_, sizeof(void*)*2);
lean_dec(v_a_2569_);
v___x_2573_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_2571_, v___y_2557_);
v___x_2574_ = lean_box(v_closed_2572_);
lean_inc(v___y_2557_);
v___f_2575_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2575_, 0, v_producers_2570_);
lean_closure_set(v___f_2575_, 1, v___x_2574_);
lean_closure_set(v___f_2575_, 2, v___y_2557_);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = 0;
v___x_2578_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2576_, v___x_2577_, v___x_2573_, v___f_2575_);
return v___x_2578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object* v___y_2579_, lean_object* v_x_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2579_, v_x_2580_);
lean_dec(v___y_2579_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object* v___y_2583_){
_start:
{
lean_object* v___x_2585_; lean_object* v___f_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; 
v___x_2585_ = lean_st_ref_get(v___y_2583_);
lean_inc(v___y_2583_);
v___f_2586_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2586_, 0, v___y_2583_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = 0;
v___x_2591_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2589_, v___x_2590_, v___x_2588_, v___f_2586_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2592_);
lean_dec(v___y_2592_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object* v_ch_2600_){
_start:
{
lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___f_2601_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0));
lean_inc_ref_n(v_ch_2600_, 2);
v___f_2602_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2602_, 0, v___f_2601_);
lean_closure_set(v___f_2602_, 1, v_ch_2600_);
v___f_2603_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1));
v___f_2604_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2));
v___x_2605_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2605_, 0, lean_box(0));
lean_closure_set(v___x_2605_, 1, lean_box(0));
lean_closure_set(v___x_2605_, 2, v_ch_2600_);
lean_closure_set(v___x_2605_, 3, v___f_2603_);
v___x_2606_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2606_, 0, lean_box(0));
lean_closure_set(v___x_2606_, 1, lean_box(0));
lean_closure_set(v___x_2606_, 2, v_ch_2600_);
lean_closure_set(v___x_2606_, 3, v___f_2604_);
v___x_2607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___f_2602_);
lean_ctor_set(v___x_2607_, 2, v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object* v_00_u03b1_2608_, lean_object* v_ch_2609_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object* v_00_u03b1_2611_, lean_object* v_q_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2612_, v___y_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_2616_, lean_object* v_q_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_2616_, v_q_2617_, v___y_2618_);
lean_dec(v___y_2618_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object* v_00_u03b1_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2622_, v_x_2623_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2627_, lean_object* v_x_2628_, lean_object* v_x_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_2627_, v_x_2628_, v_x_2629_, v___y_2630_);
lean_dec(v___y_2630_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object* v_c_2633_, uint8_t v_b_2634_){
_start:
{
lean_object* v_promise_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_promise_2636_ = lean_ctor_get(v_c_2633_, 0);
v___x_2637_ = lean_box(v_b_2634_);
v___x_2638_ = lean_io_promise_resolve(v___x_2637_, v_promise_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object* v_c_2639_, lean_object* v_b_2640_, lean_object* v_a_2641_){
_start:
{
uint8_t v_b_boxed_2642_; lean_object* v_res_2643_; 
v_b_boxed_2642_ = lean_unbox(v_b_2640_);
v_res_2643_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2639_, v_b_boxed_2642_);
lean_dec_ref(v_c_2639_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object* v_00_u03b1_2644_, lean_object* v_c_2645_, uint8_t v_b_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2645_, v_b_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object* v_00_u03b1_2649_, lean_object* v_c_2650_, lean_object* v_b_2651_, lean_object* v_a_2652_){
_start:
{
uint8_t v_b_boxed_2653_; lean_object* v_res_2654_; 
v_b_boxed_2653_ = lean_unbox(v_b_2651_);
v_res_2654_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(v_00_u03b1_2649_, v_c_2650_, v_b_boxed_2653_);
lean_dec_ref(v_c_2650_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object* v_x_2655_){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_box(0);
v___x_2658_ = lean_st_mk_ref(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2659_);
lean_dec(v_x_2659_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object* v_n_2662_, lean_object* v_f_2663_, lean_object* v_xs_2664_, lean_object* v_k_2665_, lean_object* v_acc_2666_){
_start:
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_nat_dec_lt(v_k_2665_, v_n_2662_);
if (v___x_2668_ == 0)
{
lean_dec(v_k_2665_);
lean_dec_ref(v_f_2663_);
return v_acc_2666_;
}
else
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2669_ = lean_array_fget_borrowed(v_xs_2664_, v_k_2665_);
lean_inc_ref(v_f_2663_);
lean_inc(v___x_2669_);
v___x_2670_ = lean_apply_2(v_f_2663_, v___x_2669_, lean_box(0));
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = lean_nat_add(v_k_2665_, v___x_2671_);
lean_dec(v_k_2665_);
v___x_2673_ = lean_array_push(v_acc_2666_, v___x_2670_);
v_k_2665_ = v___x_2672_;
v_acc_2666_ = v___x_2673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_2675_, lean_object* v_f_2676_, lean_object* v_xs_2677_, lean_object* v_k_2678_, lean_object* v_acc_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2675_, v_f_2676_, v_xs_2677_, v_k_2678_, v_acc_2679_);
lean_dec_ref(v_xs_2677_);
lean_dec(v_n_2675_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object* v_capacity_2685_){
_start:
{
lean_object* v___f_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___f_2687_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0));
lean_inc(v_capacity_2685_);
v___x_2688_ = l_Array_range(v_capacity_2685_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1));
v___x_2691_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_2685_, v___f_2687_, v___x_2688_, v___x_2689_, v___x_2690_);
lean_dec_ref(v___x_2688_);
v___x_2692_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2693_ = 0;
v___x_2694_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2692_);
lean_ctor_set(v___x_2694_, 2, v_capacity_2685_);
lean_ctor_set(v___x_2694_, 3, v___x_2691_);
lean_ctor_set(v___x_2694_, 4, v___x_2689_);
lean_ctor_set(v___x_2694_, 5, v___x_2689_);
lean_ctor_set(v___x_2694_, 6, v___x_2689_);
lean_ctor_set_uint8(v___x_2694_, sizeof(void*)*7, v___x_2693_);
v___x_2695_ = l_Std_Mutex_new___redArg(v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object* v_capacity_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2696_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object* v_00_u03b1_2699_, lean_object* v_capacity_2700_, lean_object* v_hcap_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2700_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object* v_00_u03b1_2704_, lean_object* v_capacity_2705_, lean_object* v_hcap_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(v_00_u03b1_2704_, v_capacity_2705_, v_hcap_2706_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object* v_00_u03b1_2709_, lean_object* v_00_u03b2_2710_, lean_object* v_n_2711_, lean_object* v_f_2712_, lean_object* v_xs_2713_, lean_object* v_k_2714_, lean_object* v_h_2715_, lean_object* v_acc_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2711_, v_f_2712_, v_xs_2713_, v_k_2714_, v_acc_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_2719_, lean_object* v_00_u03b2_2720_, lean_object* v_n_2721_, lean_object* v_f_2722_, lean_object* v_xs_2723_, lean_object* v_k_2724_, lean_object* v_h_2725_, lean_object* v_acc_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_2719_, v_00_u03b2_2720_, v_n_2721_, v_f_2722_, v_xs_2723_, v_k_2724_, v_h_2725_, v_acc_2726_);
lean_dec_ref(v_xs_2723_);
lean_dec(v_n_2721_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object* v_idx_2729_, lean_object* v_cap_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2731_ = lean_unsigned_to_nat(1u);
v___x_2732_ = lean_nat_add(v_idx_2729_, v___x_2731_);
v___x_2733_ = lean_nat_dec_eq(v___x_2732_, v_cap_2730_);
if (v___x_2733_ == 0)
{
return v___x_2732_;
}
else
{
lean_object* v___x_2734_; 
lean_dec(v___x_2732_);
v___x_2734_ = lean_unsigned_to_nat(0u);
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object* v_idx_2735_, lean_object* v_cap_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(v_idx_2735_, v_cap_2736_);
lean_dec(v_cap_2736_);
lean_dec(v_idx_2735_);
return v_res_2737_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object* v_v_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_st_2742_; lean_object* v___y_2743_; lean_object* v___x_2746_; lean_object* v_producers_2747_; lean_object* v_consumers_2748_; lean_object* v_capacity_2749_; lean_object* v_buf_2750_; lean_object* v_bufCount_2751_; lean_object* v_sendIdx_2752_; lean_object* v_recvIdx_2753_; uint8_t v_closed_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2780_; 
v___x_2746_ = lean_st_ref_get(v_a_2739_);
v_producers_2747_ = lean_ctor_get(v___x_2746_, 0);
v_consumers_2748_ = lean_ctor_get(v___x_2746_, 1);
v_capacity_2749_ = lean_ctor_get(v___x_2746_, 2);
v_buf_2750_ = lean_ctor_get(v___x_2746_, 3);
v_bufCount_2751_ = lean_ctor_get(v___x_2746_, 4);
v_sendIdx_2752_ = lean_ctor_get(v___x_2746_, 5);
v_recvIdx_2753_ = lean_ctor_get(v___x_2746_, 6);
v_closed_2754_ = lean_ctor_get_uint8(v___x_2746_, sizeof(void*)*7);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2756_ = v___x_2746_;
v_isShared_2757_ = v_isSharedCheck_2780_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_recvIdx_2753_);
lean_inc(v_sendIdx_2752_);
lean_inc(v_bufCount_2751_);
lean_inc(v_buf_2750_);
lean_inc(v_capacity_2749_);
lean_inc(v_consumers_2748_);
lean_inc(v_producers_2747_);
lean_dec(v___x_2746_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2780_;
goto v_resetjp_2755_;
}
v___jp_2741_:
{
lean_object* v___x_2744_; uint8_t v___x_2745_; 
v___x_2744_ = lean_st_ref_set(v___y_2743_, v_st_2742_);
v___x_2745_ = 1;
return v___x_2745_;
}
v_resetjp_2755_:
{
uint8_t v___x_2758_; 
v___x_2758_ = lean_nat_dec_eq(v_bufCount_2751_, v_capacity_2749_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___y_2765_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2759_ = lean_array_fget_borrowed(v_buf_2750_, v_sendIdx_2752_);
v___x_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_v_2738_);
v___x_2761_ = lean_st_ref_set(v___x_2759_, v___x_2760_);
v___x_2762_ = lean_unsigned_to_nat(1u);
v___x_2763_ = lean_nat_add(v_bufCount_2751_, v___x_2762_);
lean_dec(v_bufCount_2751_);
v___x_2776_ = lean_nat_add(v_sendIdx_2752_, v___x_2762_);
lean_dec(v_sendIdx_2752_);
v___x_2777_ = lean_nat_dec_eq(v___x_2776_, v_capacity_2749_);
if (v___x_2777_ == 0)
{
v___y_2765_ = v___x_2776_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2778_; 
lean_dec(v___x_2776_);
v___x_2778_ = lean_unsigned_to_nat(0u);
v___y_2765_ = v___x_2778_;
goto v___jp_2764_;
}
v___jp_2764_:
{
lean_object* v___x_2767_; 
lean_inc(v_recvIdx_2753_);
lean_inc(v___y_2765_);
lean_inc(v___x_2763_);
lean_inc_ref(v_buf_2750_);
lean_inc(v_capacity_2749_);
lean_inc_ref(v_consumers_2748_);
lean_inc_ref(v_producers_2747_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 5, v___y_2765_);
lean_ctor_set(v___x_2756_, 4, v___x_2763_);
v___x_2767_ = v___x_2756_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_producers_2747_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_consumers_2748_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_capacity_2749_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_buf_2750_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v___x_2763_);
lean_ctor_set(v_reuseFailAlloc_2775_, 5, v___y_2765_);
lean_ctor_set(v_reuseFailAlloc_2775_, 6, v_recvIdx_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2775_, sizeof(void*)*7, v_closed_2754_);
v___x_2767_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_2748_);
if (lean_obj_tag(v___x_2768_) == 1)
{
lean_object* v_val_2769_; lean_object* v_fst_2770_; lean_object* v_snd_2771_; uint8_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_dec_ref(v___x_2767_);
v_val_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_val_2769_);
lean_dec_ref_known(v___x_2768_, 1);
v_fst_2770_ = lean_ctor_get(v_val_2769_, 0);
lean_inc(v_fst_2770_);
v_snd_2771_ = lean_ctor_get(v_val_2769_, 1);
lean_inc(v_snd_2771_);
lean_dec(v_val_2769_);
v___x_2772_ = 1;
v___x_2773_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_2770_, v___x_2772_);
lean_dec(v_fst_2770_);
v___x_2774_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2774_, 0, v_producers_2747_);
lean_ctor_set(v___x_2774_, 1, v_snd_2771_);
lean_ctor_set(v___x_2774_, 2, v_capacity_2749_);
lean_ctor_set(v___x_2774_, 3, v_buf_2750_);
lean_ctor_set(v___x_2774_, 4, v___x_2763_);
lean_ctor_set(v___x_2774_, 5, v___y_2765_);
lean_ctor_set(v___x_2774_, 6, v_recvIdx_2753_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*7, v_closed_2754_);
v_st_2742_ = v___x_2774_;
v___y_2743_ = v_a_2739_;
goto v___jp_2741_;
}
else
{
lean_dec(v___x_2768_);
lean_dec(v___y_2765_);
lean_dec(v___x_2763_);
lean_dec(v_recvIdx_2753_);
lean_dec_ref(v_buf_2750_);
lean_dec(v_capacity_2749_);
lean_dec_ref(v_producers_2747_);
v_st_2742_ = v___x_2767_;
v___y_2743_ = v_a_2739_;
goto v___jp_2741_;
}
}
}
}
else
{
uint8_t v___x_2779_; 
lean_del_object(v___x_2756_);
lean_dec(v_recvIdx_2753_);
lean_dec(v_sendIdx_2752_);
lean_dec(v_bufCount_2751_);
lean_dec_ref(v_buf_2750_);
lean_dec(v_capacity_2749_);
lean_dec_ref(v_consumers_2748_);
lean_dec_ref(v_producers_2747_);
lean_dec(v_v_2738_);
v___x_2779_ = 0;
return v___x_2779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
uint8_t v_res_2784_; lean_object* v_r_2785_; 
v_res_2784_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2781_, v_a_2782_);
lean_dec(v_a_2782_);
v_r_2785_ = lean_box(v_res_2784_);
return v_r_2785_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object* v_00_u03b1_2786_, lean_object* v_v_2787_, lean_object* v_a_2788_){
_start:
{
uint8_t v___x_2790_; 
v___x_2790_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2787_, v_a_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_2791_, lean_object* v_v_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
uint8_t v_res_2795_; lean_object* v_r_2796_; 
v_res_2795_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(v_00_u03b1_2791_, v_v_2792_, v_a_2793_);
lean_dec(v_a_2793_);
v_r_2796_ = lean_box(v_res_2795_);
return v_r_2796_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object* v_v_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; uint8_t v_closed_2801_; 
v___x_2800_ = lean_st_ref_get(v___y_2798_);
v_closed_2801_ = lean_ctor_get_uint8(v___x_2800_, sizeof(void*)*7);
lean_dec(v___x_2800_);
if (v_closed_2801_ == 0)
{
uint8_t v___x_2802_; 
v___x_2802_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2797_, v___y_2798_);
return v___x_2802_;
}
else
{
uint8_t v___x_2803_; 
lean_dec(v_v_2797_);
v___x_2803_ = 0;
return v___x_2803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
uint8_t v_res_2807_; lean_object* v_r_2808_; 
v_res_2807_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2804_, v___y_2805_);
lean_dec(v___y_2805_);
v_r_2808_ = lean_box(v_res_2807_);
return v_r_2808_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object* v_ch_2809_, lean_object* v_v_2810_){
_start:
{
lean_object* v___f_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___f_2812_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2812_, 0, v_v_2810_);
v___x_2813_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2809_, v___f_2812_);
v___x_2814_ = lean_unbox(v___x_2813_);
lean_dec(v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object* v_ch_2815_, lean_object* v_v_2816_, lean_object* v_a_2817_){
_start:
{
uint8_t v_res_2818_; lean_object* v_r_2819_; 
v_res_2818_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2815_, v_v_2816_);
v_r_2819_ = lean_box(v_res_2818_);
return v_r_2819_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object* v_00_u03b1_2820_, lean_object* v_ch_2821_, lean_object* v_v_2822_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2821_, v_v_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(lean_object* v_00_u03b1_2825_, lean_object* v_ch_2826_, lean_object* v_v_2827_, lean_object* v_a_2828_){
_start:
{
uint8_t v_res_2829_; lean_object* v_r_2830_; 
v_res_2829_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(v_00_u03b1_2825_, v_ch_2826_, v_v_2827_);
v_r_2830_ = lean_box(v_res_2829_);
return v_r_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(lean_object* v_v_2831_, lean_object* v___f_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; uint8_t v_closed_2836_; 
v___x_2835_ = lean_st_ref_get(v___y_2833_);
v_closed_2836_ = lean_ctor_get_uint8(v___x_2835_, sizeof(void*)*7);
lean_dec(v___x_2835_);
if (v_closed_2836_ == 0)
{
uint8_t v___x_2837_; 
v___x_2837_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2831_, v___y_2833_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v_producers_2840_; lean_object* v_consumers_2841_; lean_object* v_capacity_2842_; lean_object* v_buf_2843_; lean_object* v_bufCount_2844_; lean_object* v_sendIdx_2845_; lean_object* v_recvIdx_2846_; uint8_t v_closed_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2859_; 
v___x_2838_ = lean_io_promise_new();
v___x_2839_ = lean_st_ref_take(v___y_2833_);
v_producers_2840_ = lean_ctor_get(v___x_2839_, 0);
v_consumers_2841_ = lean_ctor_get(v___x_2839_, 1);
v_capacity_2842_ = lean_ctor_get(v___x_2839_, 2);
v_buf_2843_ = lean_ctor_get(v___x_2839_, 3);
v_bufCount_2844_ = lean_ctor_get(v___x_2839_, 4);
v_sendIdx_2845_ = lean_ctor_get(v___x_2839_, 5);
v_recvIdx_2846_ = lean_ctor_get(v___x_2839_, 6);
v_closed_2847_ = lean_ctor_get_uint8(v___x_2839_, sizeof(void*)*7);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2849_ = v___x_2839_;
v_isShared_2850_ = v_isSharedCheck_2859_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_recvIdx_2846_);
lean_inc(v_sendIdx_2845_);
lean_inc(v_bufCount_2844_);
lean_inc(v_buf_2843_);
lean_inc(v_capacity_2842_);
lean_inc(v_consumers_2841_);
lean_inc(v_producers_2840_);
lean_dec(v___x_2839_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2859_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2853_; 
lean_inc(v___x_2838_);
v___x_2851_ = l_Std_Queue_enqueue___redArg(v___x_2838_, v_producers_2840_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2851_);
v___x_2853_ = v___x_2849_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_consumers_2841_);
lean_ctor_set(v_reuseFailAlloc_2858_, 2, v_capacity_2842_);
lean_ctor_set(v_reuseFailAlloc_2858_, 3, v_buf_2843_);
lean_ctor_set(v_reuseFailAlloc_2858_, 4, v_bufCount_2844_);
lean_ctor_set(v_reuseFailAlloc_2858_, 5, v_sendIdx_2845_);
lean_ctor_set(v_reuseFailAlloc_2858_, 6, v_recvIdx_2846_);
lean_ctor_set_uint8(v_reuseFailAlloc_2858_, sizeof(void*)*7, v_closed_2847_);
v___x_2853_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = lean_st_ref_set(v___y_2833_, v___x_2853_);
v___x_2855_ = lean_io_promise_result_opt(v___x_2838_);
lean_dec(v___x_2838_);
v___x_2856_ = lean_unsigned_to_nat(0u);
v___x_2857_ = lean_io_bind_task(v___x_2855_, v___f_2832_, v___x_2856_, v___x_2837_);
return v___x_2857_;
}
}
}
else
{
lean_object* v___x_2860_; 
lean_dec_ref(v___f_2832_);
v___x_2860_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_2860_;
}
}
else
{
lean_object* v___x_2861_; 
lean_dec_ref(v___f_2832_);
lean_dec(v_v_2831_);
v___x_2861_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_2862_, lean_object* v___f_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(v_v_2862_, v___f_2863_, v___y_2864_);
lean_dec(v___y_2864_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(lean_object* v_ch_2867_, lean_object* v_v_2868_, lean_object* v_res_2869_){
_start:
{
if (lean_obj_tag(v_res_2869_) == 0)
{
lean_dec(v_v_2868_);
lean_dec_ref(v_ch_2867_);
goto v___jp_2871_;
}
else
{
lean_object* v_val_2873_; uint8_t v___x_2874_; 
v_val_2873_ = lean_ctor_get(v_res_2869_, 0);
v___x_2874_ = lean_unbox(v_val_2873_);
if (v___x_2874_ == 0)
{
lean_dec(v_v_2868_);
lean_dec_ref(v_ch_2867_);
goto v___jp_2871_;
}
else
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2867_, v_v_2868_);
return v___x_2875_;
}
}
v___jp_2871_:
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_2876_, lean_object* v_v_2877_, lean_object* v_res_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(v_ch_2876_, v_v_2877_, v_res_2878_);
lean_dec(v_res_2878_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(lean_object* v_ch_2881_, lean_object* v_v_2882_){
_start:
{
lean_object* v___f_2884_; lean_object* v___f_2885_; lean_object* v___x_2886_; 
lean_inc(v_v_2882_);
lean_inc_ref(v_ch_2881_);
v___f_2884_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2884_, 0, v_ch_2881_);
lean_closure_set(v___f_2884_, 1, v_v_2882_);
v___f_2885_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2885_, 0, v_v_2882_);
lean_closure_set(v___f_2885_, 1, v___f_2884_);
v___x_2886_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2881_, v___f_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(lean_object* v_ch_2887_, lean_object* v_v_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2887_, v_v_2888_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_object* v_00_u03b1_2891_, lean_object* v_ch_2892_, lean_object* v_v_2893_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2892_, v_v_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(lean_object* v_00_u03b1_2896_, lean_object* v_ch_2897_, lean_object* v_v_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(v_00_u03b1_2896_, v_ch_2897_, v_v_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t v___x_2901_, lean_object* v_as_2902_, size_t v_sz_2903_, size_t v_i_2904_, lean_object* v_b_2905_){
_start:
{
uint8_t v___x_2907_; 
v___x_2907_ = lean_usize_dec_lt(v_i_2904_, v_sz_2903_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2908_, 0, v_b_2905_);
return v___x_2908_;
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; size_t v___x_2912_; size_t v___x_2913_; 
v_a_2909_ = lean_array_uget_borrowed(v_as_2902_, v_i_2904_);
v___x_2910_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_2909_, v___x_2901_);
v___x_2911_ = lean_box(0);
v___x_2912_ = ((size_t)1ULL);
v___x_2913_ = lean_usize_add(v_i_2904_, v___x_2912_);
v_i_2904_ = v___x_2913_;
v_b_2905_ = v___x_2911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_2915_, lean_object* v_as_2916_, lean_object* v_sz_2917_, lean_object* v_i_2918_, lean_object* v_b_2919_, lean_object* v___y_2920_){
_start:
{
uint8_t v___x_1136__boxed_2921_; size_t v_sz_boxed_2922_; size_t v_i_boxed_2923_; lean_object* v_res_2924_; 
v___x_1136__boxed_2921_ = lean_unbox(v___x_2915_);
v_sz_boxed_2922_ = lean_unbox_usize(v_sz_2917_);
lean_dec(v_sz_2917_);
v_i_boxed_2923_ = lean_unbox_usize(v_i_2918_);
lean_dec(v_i_2918_);
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1136__boxed_2921_, v_as_2916_, v_sz_boxed_2922_, v_i_boxed_2923_, v_b_2919_);
lean_dec_ref(v_as_2916_);
return v_res_2924_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Std_Queue_empty(lean_box(0));
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_2926_){
_start:
{
lean_object* v___x_2928_; uint8_t v_closed_2929_; 
v___x_2928_ = lean_st_ref_get(v___y_2926_);
v_closed_2929_ = lean_ctor_get_uint8(v___x_2928_, sizeof(void*)*7);
if (v_closed_2929_ == 0)
{
lean_object* v_producers_2930_; lean_object* v_consumers_2931_; lean_object* v_capacity_2932_; lean_object* v_buf_2933_; lean_object* v_bufCount_2934_; lean_object* v_sendIdx_2935_; lean_object* v_recvIdx_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2959_; 
v_producers_2930_ = lean_ctor_get(v___x_2928_, 0);
v_consumers_2931_ = lean_ctor_get(v___x_2928_, 1);
v_capacity_2932_ = lean_ctor_get(v___x_2928_, 2);
v_buf_2933_ = lean_ctor_get(v___x_2928_, 3);
v_bufCount_2934_ = lean_ctor_get(v___x_2928_, 4);
v_sendIdx_2935_ = lean_ctor_get(v___x_2928_, 5);
v_recvIdx_2936_ = lean_ctor_get(v___x_2928_, 6);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2938_ = v___x_2928_;
v_isShared_2939_ = v_isSharedCheck_2959_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_recvIdx_2936_);
lean_inc(v_sendIdx_2935_);
lean_inc(v_bufCount_2934_);
lean_inc(v_buf_2933_);
lean_inc(v_capacity_2932_);
lean_inc(v_consumers_2931_);
lean_inc(v_producers_2930_);
lean_dec(v___x_2928_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2959_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; size_t v_sz_2942_; size_t v___x_2943_; lean_object* v___x_2944_; 
v___x_2940_ = l_Std_Queue_toArray___redArg(v_consumers_2931_);
v___x_2941_ = lean_box(0);
v_sz_2942_ = lean_array_size(v___x_2940_);
v___x_2943_ = ((size_t)0ULL);
v___x_2944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_2929_, v___x_2940_, v_sz_2942_, v___x_2943_, v___x_2941_);
lean_dec_ref(v___x_2940_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2957_; 
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v___x_2944_, 0);
lean_dec(v_unused_2958_);
v___x_2946_ = v___x_2944_;
v_isShared_2947_ = v_isSharedCheck_2957_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v___x_2944_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2957_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; uint8_t v___x_2949_; lean_object* v___x_2951_; 
v___x_2948_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0);
v___x_2949_ = 1;
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 1, v___x_2948_);
v___x_2951_ = v___x_2938_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_producers_2930_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_capacity_2932_);
lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_buf_2933_);
lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_bufCount_2934_);
lean_ctor_set(v_reuseFailAlloc_2956_, 5, v_sendIdx_2935_);
lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_recvIdx_2936_);
v___x_2951_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
lean_ctor_set_uint8(v___x_2951_, sizeof(void*)*7, v___x_2949_);
v___x_2952_ = lean_st_ref_set(v___y_2926_, v___x_2951_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2941_);
v___x_2954_ = v___x_2946_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2941_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
else
{
lean_del_object(v___x_2938_);
lean_dec(v_recvIdx_2936_);
lean_dec(v_sendIdx_2935_);
lean_dec(v_bufCount_2934_);
lean_dec_ref(v_buf_2933_);
lean_dec(v_capacity_2932_);
lean_dec_ref(v_producers_2930_);
return v___x_2944_;
}
}
}
else
{
uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_dec(v___x_2928_);
v___x_2960_ = 1;
v___x_2961_ = lean_box(v___x_2960_);
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_2963_);
lean_dec(v___y_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_2967_){
_start:
{
lean_object* v___f_2969_; lean_object* v___x_2970_; 
v___f_2969_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_2970_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_2967_, v___f_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2971_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_2974_, lean_object* v_ch_2975_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_2978_, lean_object* v_ch_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_2978_, v_ch_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_2982_, uint8_t v___x_2983_, lean_object* v_as_2984_, size_t v_sz_2985_, size_t v_i_2986_, lean_object* v_b_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_2983_, v_as_2984_, v_sz_2985_, v_i_2986_, v_b_2987_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_2991_, lean_object* v___x_2992_, lean_object* v_as_2993_, lean_object* v_sz_2994_, lean_object* v_i_2995_, lean_object* v_b_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
uint8_t v___x_1234__boxed_2999_; size_t v_sz_boxed_3000_; size_t v_i_boxed_3001_; lean_object* v_res_3002_; 
v___x_1234__boxed_2999_ = lean_unbox(v___x_2992_);
v_sz_boxed_3000_ = lean_unbox_usize(v_sz_2994_);
lean_dec(v_sz_2994_);
v_i_boxed_3001_ = lean_unbox_usize(v_i_2995_);
lean_dec(v_i_2995_);
v_res_3002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_2991_, v___x_1234__boxed_2999_, v_as_2993_, v_sz_boxed_3000_, v_i_boxed_3001_, v_b_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v_as_2993_);
return v_res_3002_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_3003_){
_start:
{
lean_object* v___x_3005_; uint8_t v_closed_3006_; 
v___x_3005_ = lean_st_ref_get(v___y_3003_);
v_closed_3006_ = lean_ctor_get_uint8(v___x_3005_, sizeof(void*)*7);
lean_dec(v___x_3005_);
return v_closed_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
uint8_t v_res_3009_; lean_object* v_r_3010_; 
v_res_3009_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_3007_);
lean_dec(v___y_3007_);
v_r_3010_ = lean_box(v_res_3009_);
return v_r_3010_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_3012_){
_start:
{
lean_object* v___f_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___f_3014_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_3015_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3012_, v___f_3014_);
v___x_3016_ = lean_unbox(v___x_3015_);
lean_dec(v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_3017_, lean_object* v_a_3018_){
_start:
{
uint8_t v_res_3019_; lean_object* v_r_3020_; 
v_res_3019_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3017_);
v_r_3020_ = lean_box(v_res_3019_);
return v_r_3020_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_3021_, lean_object* v_ch_3022_){
_start:
{
uint8_t v___x_3024_; 
v___x_3024_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3022_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_3025_, lean_object* v_ch_3026_, lean_object* v_a_3027_){
_start:
{
uint8_t v_res_3028_; lean_object* v_r_3029_; 
v_res_3028_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_3025_, v_ch_3026_);
v_r_3029_ = lean_box(v_res_3028_);
return v_r_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_toPure_3033_; lean_object* v___x_3034_; 
v_toPure_3033_ = lean_ctor_get(v_toApplicative_3030_, 1);
lean_inc(v_toPure_3033_);
lean_dec_ref(v_toApplicative_3030_);
v___x_3034_ = lean_apply_2(v_toPure_3033_, lean_box(0), v_a_3031_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_3035_, lean_object* v_toBind_3036_, lean_object* v___f_3037_, lean_object* v_____r_3038_, lean_object* v_st_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
lean_inc(v___y_3040_);
v___x_3041_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_3041_, 0, lean_box(0));
lean_closure_set(v___x_3041_, 1, lean_box(0));
lean_closure_set(v___x_3041_, 2, v___y_3040_);
lean_closure_set(v___x_3041_, 3, v_st_3039_);
v___x_3042_ = lean_apply_2(v_inst_3035_, lean_box(0), v___x_3041_);
v___x_3043_ = lean_apply_4(v_toBind_3036_, lean_box(0), lean_box(0), v___x_3042_, v___f_3037_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_inst_3044_, lean_object* v_toBind_3045_, lean_object* v___f_3046_, lean_object* v_____r_3047_, lean_object* v_st_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3044_, v_toBind_3045_, v___f_3046_, v_____r_3047_, v_st_3048_, v___y_3049_);
lean_dec(v___y_3049_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_3051_, lean_object* v_consumers_3052_, lean_object* v_capacity_3053_, lean_object* v_buf_3054_, lean_object* v___x_3055_, lean_object* v_sendIdx_3056_, lean_object* v___y_3057_, uint8_t v_closed_3058_, lean_object* v___f_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3062_, 0, v_snd_3051_);
lean_ctor_set(v___x_3062_, 1, v_consumers_3052_);
lean_ctor_set(v___x_3062_, 2, v_capacity_3053_);
lean_ctor_set(v___x_3062_, 3, v_buf_3054_);
lean_ctor_set(v___x_3062_, 4, v___x_3055_);
lean_ctor_set(v___x_3062_, 5, v_sendIdx_3056_);
lean_ctor_set(v___x_3062_, 6, v___y_3057_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*7, v_closed_3058_);
v___x_3063_ = lean_box(0);
lean_inc(v_a_3060_);
v___x_3064_ = lean_apply_3(v___f_3059_, v___x_3063_, v___x_3062_, v_a_3060_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_3065_, lean_object* v_consumers_3066_, lean_object* v_capacity_3067_, lean_object* v_buf_3068_, lean_object* v___x_3069_, lean_object* v_sendIdx_3070_, lean_object* v___y_3071_, lean_object* v_closed_3072_, lean_object* v___f_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
uint8_t v_closed_boxed_3076_; lean_object* v_res_3077_; 
v_closed_boxed_3076_ = lean_unbox(v_closed_3072_);
v_res_3077_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3065_, v_consumers_3066_, v_capacity_3067_, v_buf_3068_, v___x_3069_, v_sendIdx_3070_, v___y_3071_, v_closed_boxed_3076_, v___f_3073_, v_a_3074_, v_a_3075_);
lean_dec(v_a_3074_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3078_, lean_object* v_inst_3079_, lean_object* v_toBind_3080_, lean_object* v_bufCount_3081_, lean_object* v_producers_3082_, lean_object* v_consumers_3083_, lean_object* v_capacity_3084_, lean_object* v_buf_3085_, lean_object* v_sendIdx_3086_, uint8_t v_closed_3087_, lean_object* v_a_3088_, uint8_t v___x_3089_, lean_object* v_inst_3090_, lean_object* v_recvIdx_3091_, lean_object* v___x_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v___f_3094_; lean_object* v___f_3095_; lean_object* v___y_3097_; lean_object* v___x_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v___f_3094_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3094_, 0, v_toApplicative_3078_);
lean_closure_set(v___f_3094_, 1, v_a_3093_);
lean_inc_ref(v___f_3094_);
lean_inc(v_toBind_3080_);
lean_inc(v_inst_3079_);
v___f_3095_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3095_, 0, v_inst_3079_);
lean_closure_set(v___f_3095_, 1, v_toBind_3080_);
lean_closure_set(v___f_3095_, 2, v___f_3094_);
v___x_3113_ = lean_unsigned_to_nat(1u);
v___x_3114_ = lean_nat_add(v_recvIdx_3091_, v___x_3113_);
v___x_3115_ = lean_nat_dec_eq(v___x_3114_, v_capacity_3084_);
if (v___x_3115_ == 0)
{
lean_dec(v___x_3092_);
v___y_3097_ = v___x_3114_;
goto v___jp_3096_;
}
else
{
lean_dec(v___x_3114_);
v___y_3097_ = v___x_3092_;
goto v___jp_3096_;
}
v___jp_3096_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3098_ = lean_unsigned_to_nat(1u);
v___x_3099_ = lean_nat_sub(v_bufCount_3081_, v___x_3098_);
lean_inc(v___y_3097_);
lean_inc(v_sendIdx_3086_);
lean_inc(v___x_3099_);
lean_inc_ref(v_buf_3085_);
lean_inc(v_capacity_3084_);
lean_inc_ref(v_consumers_3083_);
lean_inc_ref(v_producers_3082_);
v___x_3100_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3100_, 0, v_producers_3082_);
lean_ctor_set(v___x_3100_, 1, v_consumers_3083_);
lean_ctor_set(v___x_3100_, 2, v_capacity_3084_);
lean_ctor_set(v___x_3100_, 3, v_buf_3085_);
lean_ctor_set(v___x_3100_, 4, v___x_3099_);
lean_ctor_set(v___x_3100_, 5, v_sendIdx_3086_);
lean_ctor_set(v___x_3100_, 6, v___y_3097_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*7, v_closed_3087_);
v___x_3101_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3082_);
if (lean_obj_tag(v___x_3101_) == 1)
{
lean_object* v_val_3102_; lean_object* v_fst_3103_; lean_object* v_snd_3104_; lean_object* v___x_3105_; lean_object* v___f_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_dec_ref_known(v___x_3100_, 7);
lean_dec_ref(v___f_3094_);
lean_dec(v_inst_3079_);
v_val_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_val_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v_fst_3103_ = lean_ctor_get(v_val_3102_, 0);
lean_inc(v_fst_3103_);
v_snd_3104_ = lean_ctor_get(v_val_3102_, 1);
lean_inc(v_snd_3104_);
lean_dec(v_val_3102_);
v___x_3105_ = lean_box(v_closed_3087_);
lean_inc(v_a_3088_);
v___f_3106_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3106_, 0, v_snd_3104_);
lean_closure_set(v___f_3106_, 1, v_consumers_3083_);
lean_closure_set(v___f_3106_, 2, v_capacity_3084_);
lean_closure_set(v___f_3106_, 3, v_buf_3085_);
lean_closure_set(v___f_3106_, 4, v___x_3099_);
lean_closure_set(v___f_3106_, 5, v_sendIdx_3086_);
lean_closure_set(v___f_3106_, 6, v___y_3097_);
lean_closure_set(v___f_3106_, 7, v___x_3105_);
lean_closure_set(v___f_3106_, 8, v___f_3095_);
lean_closure_set(v___f_3106_, 9, v_a_3088_);
v___x_3107_ = lean_box(v___x_3089_);
v___x_3108_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3108_, 0, lean_box(0));
lean_closure_set(v___x_3108_, 1, v___x_3107_);
lean_closure_set(v___x_3108_, 2, v_fst_3103_);
v___x_3109_ = lean_apply_2(v_inst_3090_, lean_box(0), v___x_3108_);
v___x_3110_ = lean_apply_4(v_toBind_3080_, lean_box(0), lean_box(0), v___x_3109_, v___f_3106_);
return v___x_3110_;
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec(v___x_3101_);
lean_dec(v___x_3099_);
lean_dec(v___y_3097_);
lean_dec_ref(v___f_3095_);
lean_dec(v_inst_3090_);
lean_dec(v_sendIdx_3086_);
lean_dec_ref(v_buf_3085_);
lean_dec(v_capacity_3084_);
lean_dec_ref(v_consumers_3083_);
v___x_3111_ = lean_box(0);
v___x_3112_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3079_, v_toBind_3080_, v___f_3094_, v___x_3111_, v___x_3100_, v_a_3088_);
return v___x_3112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3116_, lean_object* v_inst_3117_, lean_object* v_toBind_3118_, lean_object* v_bufCount_3119_, lean_object* v_producers_3120_, lean_object* v_consumers_3121_, lean_object* v_capacity_3122_, lean_object* v_buf_3123_, lean_object* v_sendIdx_3124_, lean_object* v_closed_3125_, lean_object* v_a_3126_, lean_object* v___x_3127_, lean_object* v_inst_3128_, lean_object* v_recvIdx_3129_, lean_object* v___x_3130_, lean_object* v_a_3131_){
_start:
{
uint8_t v_closed_boxed_3132_; uint8_t v___x_679__boxed_3133_; lean_object* v_res_3134_; 
v_closed_boxed_3132_ = lean_unbox(v_closed_3125_);
v___x_679__boxed_3133_ = lean_unbox(v___x_3127_);
v_res_3134_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3116_, v_inst_3117_, v_toBind_3118_, v_bufCount_3119_, v_producers_3120_, v_consumers_3121_, v_capacity_3122_, v_buf_3123_, v_sendIdx_3124_, v_closed_boxed_3132_, v_a_3126_, v___x_679__boxed_3133_, v_inst_3128_, v_recvIdx_3129_, v___x_3130_, v_a_3131_);
lean_dec(v_recvIdx_3129_);
lean_dec(v_a_3126_);
lean_dec(v_bufCount_3119_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3135_, lean_object* v_inst_3136_, lean_object* v_toBind_3137_, lean_object* v_a_3138_, lean_object* v_inst_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_producers_3141_; lean_object* v_consumers_3142_; lean_object* v_capacity_3143_; lean_object* v_buf_3144_; lean_object* v_bufCount_3145_; lean_object* v_sendIdx_3146_; lean_object* v_recvIdx_3147_; uint8_t v_closed_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v_producers_3141_ = lean_ctor_get(v_a_3140_, 0);
lean_inc_ref(v_producers_3141_);
v_consumers_3142_ = lean_ctor_get(v_a_3140_, 1);
lean_inc_ref(v_consumers_3142_);
v_capacity_3143_ = lean_ctor_get(v_a_3140_, 2);
lean_inc(v_capacity_3143_);
v_buf_3144_ = lean_ctor_get(v_a_3140_, 3);
lean_inc_ref(v_buf_3144_);
v_bufCount_3145_ = lean_ctor_get(v_a_3140_, 4);
lean_inc(v_bufCount_3145_);
v_sendIdx_3146_ = lean_ctor_get(v_a_3140_, 5);
lean_inc(v_sendIdx_3146_);
v_recvIdx_3147_ = lean_ctor_get(v_a_3140_, 6);
lean_inc(v_recvIdx_3147_);
v_closed_3148_ = lean_ctor_get_uint8(v_a_3140_, sizeof(void*)*7);
lean_dec_ref(v_a_3140_);
v___x_3149_ = lean_unsigned_to_nat(0u);
v___x_3150_ = lean_nat_dec_eq(v_bufCount_3145_, v___x_3149_);
if (v___x_3150_ == 0)
{
uint8_t v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3151_ = 1;
v___x_3152_ = lean_box(v_closed_3148_);
v___x_3153_ = lean_box(v___x_3151_);
lean_inc(v_recvIdx_3147_);
lean_inc(v_a_3138_);
lean_inc_ref(v_buf_3144_);
lean_inc(v_toBind_3137_);
lean_inc(v_inst_3136_);
v___f_3154_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3154_, 0, v_toApplicative_3135_);
lean_closure_set(v___f_3154_, 1, v_inst_3136_);
lean_closure_set(v___f_3154_, 2, v_toBind_3137_);
lean_closure_set(v___f_3154_, 3, v_bufCount_3145_);
lean_closure_set(v___f_3154_, 4, v_producers_3141_);
lean_closure_set(v___f_3154_, 5, v_consumers_3142_);
lean_closure_set(v___f_3154_, 6, v_capacity_3143_);
lean_closure_set(v___f_3154_, 7, v_buf_3144_);
lean_closure_set(v___f_3154_, 8, v_sendIdx_3146_);
lean_closure_set(v___f_3154_, 9, v___x_3152_);
lean_closure_set(v___f_3154_, 10, v_a_3138_);
lean_closure_set(v___f_3154_, 11, v___x_3153_);
lean_closure_set(v___f_3154_, 12, v_inst_3139_);
lean_closure_set(v___f_3154_, 13, v_recvIdx_3147_);
lean_closure_set(v___f_3154_, 14, v___x_3149_);
v___x_3155_ = lean_array_fget(v_buf_3144_, v_recvIdx_3147_);
lean_dec(v_recvIdx_3147_);
lean_dec_ref(v_buf_3144_);
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3157_, 0, lean_box(0));
lean_closure_set(v___x_3157_, 1, lean_box(0));
lean_closure_set(v___x_3157_, 2, v___x_3155_);
lean_closure_set(v___x_3157_, 3, v___x_3156_);
v___x_3158_ = lean_apply_2(v_inst_3136_, lean_box(0), v___x_3157_);
v___x_3159_ = lean_apply_4(v_toBind_3137_, lean_box(0), lean_box(0), v___x_3158_, v___f_3154_);
return v___x_3159_;
}
else
{
lean_object* v_toPure_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_dec(v_recvIdx_3147_);
lean_dec(v_sendIdx_3146_);
lean_dec(v_bufCount_3145_);
lean_dec_ref(v_buf_3144_);
lean_dec(v_capacity_3143_);
lean_dec_ref(v_consumers_3142_);
lean_dec_ref(v_producers_3141_);
lean_dec(v_inst_3139_);
lean_dec(v_toBind_3137_);
lean_dec(v_inst_3136_);
v_toPure_3160_ = lean_ctor_get(v_toApplicative_3135_, 1);
lean_inc(v_toPure_3160_);
lean_dec_ref(v_toApplicative_3135_);
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_apply_2(v_toPure_3160_, lean_box(0), v___x_3161_);
return v___x_3162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_3163_, lean_object* v_inst_3164_, lean_object* v_toBind_3165_, lean_object* v_a_3166_, lean_object* v_inst_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(v_toApplicative_3163_, v_inst_3164_, v_toBind_3165_, v_a_3166_, v_inst_3167_, v_a_3168_);
lean_dec(v_a_3166_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_toApplicative_3174_; lean_object* v_toBind_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_toApplicative_3174_ = lean_ctor_get(v_inst_3170_, 0);
lean_inc_ref(v_toApplicative_3174_);
v_toBind_3175_ = lean_ctor_get(v_inst_3170_, 1);
lean_inc_n(v_toBind_3175_, 2);
lean_dec_ref(v_inst_3170_);
lean_inc_n(v_a_3173_, 2);
lean_inc(v_inst_3171_);
v___f_3176_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_3176_, 0, v_toApplicative_3174_);
lean_closure_set(v___f_3176_, 1, v_inst_3171_);
lean_closure_set(v___f_3176_, 2, v_toBind_3175_);
lean_closure_set(v___f_3176_, 3, v_a_3173_);
lean_closure_set(v___f_3176_, 4, v_inst_3172_);
v___x_3177_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3177_, 0, lean_box(0));
lean_closure_set(v___x_3177_, 1, lean_box(0));
lean_closure_set(v___x_3177_, 2, v_a_3173_);
v___x_3178_ = lean_apply_2(v_inst_3171_, lean_box(0), v___x_3177_);
v___x_3179_ = lean_apply_4(v_toBind_3175_, lean_box(0), lean_box(0), v___x_3178_, v___f_3176_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_3180_, lean_object* v_inst_3181_, lean_object* v_inst_3182_, lean_object* v_a_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3180_, v_inst_3181_, v_inst_3182_, v_a_3183_);
lean_dec(v_a_3183_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3185_, lean_object* v_00_u03b1_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_inst_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3187_, v_inst_3188_, v_inst_3189_, v_a_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object* v_m_3192_, lean_object* v_00_u03b1_3193_, lean_object* v_inst_3194_, lean_object* v_inst_3195_, lean_object* v_inst_3196_, lean_object* v_a_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(v_m_3192_, v_00_u03b1_3193_, v_inst_3194_, v_inst_3195_, v_inst_3196_, v_a_3197_);
lean_dec(v_a_3197_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3199_){
_start:
{
lean_object* v___x_3201_; lean_object* v_producers_3202_; lean_object* v_consumers_3203_; lean_object* v_capacity_3204_; lean_object* v_buf_3205_; lean_object* v_bufCount_3206_; lean_object* v_sendIdx_3207_; lean_object* v_recvIdx_3208_; uint8_t v_closed_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3241_; 
v___x_3201_ = lean_st_ref_get(v_a_3199_);
v_producers_3202_ = lean_ctor_get(v___x_3201_, 0);
v_consumers_3203_ = lean_ctor_get(v___x_3201_, 1);
v_capacity_3204_ = lean_ctor_get(v___x_3201_, 2);
v_buf_3205_ = lean_ctor_get(v___x_3201_, 3);
v_bufCount_3206_ = lean_ctor_get(v___x_3201_, 4);
v_sendIdx_3207_ = lean_ctor_get(v___x_3201_, 5);
v_recvIdx_3208_ = lean_ctor_get(v___x_3201_, 6);
v_closed_3209_ = lean_ctor_get_uint8(v___x_3201_, sizeof(void*)*7);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3211_ = v___x_3201_;
v_isShared_3212_ = v_isSharedCheck_3241_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_recvIdx_3208_);
lean_inc(v_sendIdx_3207_);
lean_inc(v_bufCount_3206_);
lean_inc(v_buf_3205_);
lean_inc(v_capacity_3204_);
lean_inc(v_consumers_3203_);
lean_inc(v_producers_3202_);
lean_dec(v___x_3201_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3241_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = lean_unsigned_to_nat(0u);
v___x_3214_ = lean_nat_dec_eq(v_bufCount_3206_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v_st_3219_; lean_object* v___y_3220_; uint8_t v___x_3222_; lean_object* v___y_3224_; lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3215_ = lean_array_fget_borrowed(v_buf_3205_, v_recvIdx_3208_);
v___x_3216_ = lean_box(0);
v___x_3217_ = lean_st_ref_swap(v___x_3215_, v___x_3216_);
v___x_3222_ = 1;
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_nat_add(v_recvIdx_3208_, v___x_3237_);
lean_dec(v_recvIdx_3208_);
v___x_3239_ = lean_nat_dec_eq(v___x_3238_, v_capacity_3204_);
if (v___x_3239_ == 0)
{
v___y_3224_ = v___x_3238_;
goto v___jp_3223_;
}
else
{
lean_dec(v___x_3238_);
v___y_3224_ = v___x_3213_;
goto v___jp_3223_;
}
v___jp_3218_:
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_st_ref_set(v___y_3220_, v_st_3219_);
return v___x_3217_;
}
v___jp_3223_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3225_ = lean_unsigned_to_nat(1u);
v___x_3226_ = lean_nat_sub(v_bufCount_3206_, v___x_3225_);
lean_dec(v_bufCount_3206_);
lean_inc(v___y_3224_);
lean_inc(v_sendIdx_3207_);
lean_inc(v___x_3226_);
lean_inc_ref(v_buf_3205_);
lean_inc(v_capacity_3204_);
lean_inc_ref(v_consumers_3203_);
lean_inc_ref(v_producers_3202_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 6, v___y_3224_);
lean_ctor_set(v___x_3211_, 4, v___x_3226_);
v___x_3228_ = v___x_3211_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_producers_3202_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_consumers_3203_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_capacity_3204_);
lean_ctor_set(v_reuseFailAlloc_3236_, 3, v_buf_3205_);
lean_ctor_set(v_reuseFailAlloc_3236_, 4, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3236_, 5, v_sendIdx_3207_);
lean_ctor_set(v_reuseFailAlloc_3236_, 6, v___y_3224_);
lean_ctor_set_uint8(v_reuseFailAlloc_3236_, sizeof(void*)*7, v_closed_3209_);
v___x_3228_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3202_);
if (lean_obj_tag(v___x_3229_) == 1)
{
lean_object* v_val_3230_; lean_object* v_fst_3231_; lean_object* v_snd_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_dec_ref(v___x_3228_);
v_val_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_val_3230_);
lean_dec_ref_known(v___x_3229_, 1);
v_fst_3231_ = lean_ctor_get(v_val_3230_, 0);
lean_inc(v_fst_3231_);
v_snd_3232_ = lean_ctor_get(v_val_3230_, 1);
lean_inc(v_snd_3232_);
lean_dec(v_val_3230_);
v___x_3233_ = lean_box(v___x_3222_);
v___x_3234_ = lean_io_promise_resolve(v___x_3233_, v_fst_3231_);
lean_dec(v_fst_3231_);
v___x_3235_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3235_, 0, v_snd_3232_);
lean_ctor_set(v___x_3235_, 1, v_consumers_3203_);
lean_ctor_set(v___x_3235_, 2, v_capacity_3204_);
lean_ctor_set(v___x_3235_, 3, v_buf_3205_);
lean_ctor_set(v___x_3235_, 4, v___x_3226_);
lean_ctor_set(v___x_3235_, 5, v_sendIdx_3207_);
lean_ctor_set(v___x_3235_, 6, v___y_3224_);
lean_ctor_set_uint8(v___x_3235_, sizeof(void*)*7, v_closed_3209_);
v_st_3219_ = v___x_3235_;
v___y_3220_ = v_a_3199_;
goto v___jp_3218_;
}
else
{
lean_dec(v___x_3229_);
lean_dec(v___x_3226_);
lean_dec(v___y_3224_);
lean_dec(v_sendIdx_3207_);
lean_dec_ref(v_buf_3205_);
lean_dec(v_capacity_3204_);
lean_dec_ref(v_consumers_3203_);
v_st_3219_ = v___x_3228_;
v___y_3220_ = v_a_3199_;
goto v___jp_3218_;
}
}
}
}
else
{
lean_object* v___x_3240_; 
lean_del_object(v___x_3211_);
lean_dec(v_recvIdx_3208_);
lean_dec(v_sendIdx_3207_);
lean_dec(v_bufCount_3206_);
lean_dec_ref(v_buf_3205_);
lean_dec(v_capacity_3204_);
lean_dec_ref(v_consumers_3203_);
lean_dec_ref(v_producers_3202_);
v___x_3240_ = lean_box(0);
return v___x_3240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3242_);
lean_dec(v_a_3242_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3246_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3249_, lean_object* v_a_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3249_, v_a_3250_);
lean_dec(v_a_3250_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3254_){
_start:
{
lean_object* v___f_3256_; lean_object* v___x_3257_; 
v___f_3256_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3257_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3254_, v___f_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3258_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3261_, lean_object* v_ch_3262_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3265_, lean_object* v_ch_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3265_, v_ch_3266_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3270_);
if (lean_obj_tag(v___x_3272_) == 1)
{
lean_object* v___x_3273_; 
lean_dec_ref(v___f_3269_);
v___x_3273_ = lean_task_pure(v___x_3272_);
return v___x_3273_;
}
else
{
lean_object* v___x_3274_; uint8_t v_closed_3275_; 
lean_dec(v___x_3272_);
v___x_3274_ = lean_st_ref_get(v___y_3270_);
v_closed_3275_ = lean_ctor_get_uint8(v___x_3274_, sizeof(void*)*7);
lean_dec(v___x_3274_);
if (v_closed_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v_producers_3278_; lean_object* v_consumers_3279_; lean_object* v_capacity_3280_; lean_object* v_buf_3281_; lean_object* v_bufCount_3282_; lean_object* v_sendIdx_3283_; lean_object* v_recvIdx_3284_; uint8_t v_closed_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3299_; 
v___x_3276_ = lean_io_promise_new();
v___x_3277_ = lean_st_ref_take(v___y_3270_);
v_producers_3278_ = lean_ctor_get(v___x_3277_, 0);
v_consumers_3279_ = lean_ctor_get(v___x_3277_, 1);
v_capacity_3280_ = lean_ctor_get(v___x_3277_, 2);
v_buf_3281_ = lean_ctor_get(v___x_3277_, 3);
v_bufCount_3282_ = lean_ctor_get(v___x_3277_, 4);
v_sendIdx_3283_ = lean_ctor_get(v___x_3277_, 5);
v_recvIdx_3284_ = lean_ctor_get(v___x_3277_, 6);
v_closed_3285_ = lean_ctor_get_uint8(v___x_3277_, sizeof(void*)*7);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3287_ = v___x_3277_;
v_isShared_3288_ = v_isSharedCheck_3299_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_recvIdx_3284_);
lean_inc(v_sendIdx_3283_);
lean_inc(v_bufCount_3282_);
lean_inc(v_buf_3281_);
lean_inc(v_capacity_3280_);
lean_inc(v_consumers_3279_);
lean_inc(v_producers_3278_);
lean_dec(v___x_3277_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3299_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3289_ = lean_box(0);
lean_inc(v___x_3276_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3276_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_Std_Queue_enqueue___redArg(v___x_3290_, v_consumers_3279_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 1, v___x_3291_);
v___x_3293_ = v___x_3287_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_producers_3278_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v_capacity_3280_);
lean_ctor_set(v_reuseFailAlloc_3298_, 3, v_buf_3281_);
lean_ctor_set(v_reuseFailAlloc_3298_, 4, v_bufCount_3282_);
lean_ctor_set(v_reuseFailAlloc_3298_, 5, v_sendIdx_3283_);
lean_ctor_set(v_reuseFailAlloc_3298_, 6, v_recvIdx_3284_);
lean_ctor_set_uint8(v_reuseFailAlloc_3298_, sizeof(void*)*7, v_closed_3285_);
v___x_3293_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3294_ = lean_st_ref_set(v___y_3270_, v___x_3293_);
v___x_3295_ = lean_io_promise_result_opt(v___x_3276_);
lean_dec(v___x_3276_);
v___x_3296_ = lean_unsigned_to_nat(0u);
v___x_3297_ = lean_io_bind_task(v___x_3295_, v___f_3269_, v___x_3296_, v_closed_3275_);
return v___x_3297_;
}
}
}
else
{
lean_object* v___x_3300_; 
lean_dec_ref(v___f_3269_);
v___x_3300_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3301_, v___y_3302_);
lean_dec(v___y_3302_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3305_, lean_object* v_res_3306_){
_start:
{
if (lean_obj_tag(v_res_3306_) == 0)
{
lean_dec_ref(v_ch_3305_);
goto v___jp_3308_;
}
else
{
lean_object* v_val_3310_; uint8_t v___x_3311_; 
v_val_3310_ = lean_ctor_get(v_res_3306_, 0);
v___x_3311_ = lean_unbox(v_val_3310_);
if (v___x_3311_ == 0)
{
lean_dec_ref(v_ch_3305_);
goto v___jp_3308_;
}
else
{
lean_object* v___x_3312_; 
v___x_3312_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3305_);
return v___x_3312_;
}
}
v___jp_3308_:
{
lean_object* v___x_3309_; 
v___x_3309_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3313_, lean_object* v_res_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3313_, v_res_3314_);
lean_dec(v_res_3314_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3317_){
_start:
{
lean_object* v___f_3319_; lean_object* v___f_3320_; lean_object* v___x_3321_; 
lean_inc_ref(v_ch_3317_);
v___f_3319_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3319_, 0, v_ch_3317_);
v___f_3320_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3320_, 0, v___f_3319_);
v___x_3321_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3317_, v___f_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3325_, lean_object* v_ch_3326_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3326_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3329_, lean_object* v_ch_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3329_, v_ch_3330_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3333_, lean_object* v_a_3334_){
_start:
{
uint8_t v___y_3336_; lean_object* v_bufCount_3340_; uint8_t v_closed_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; 
v_bufCount_3340_ = lean_ctor_get(v_a_3334_, 4);
v_closed_3341_ = lean_ctor_get_uint8(v_a_3334_, sizeof(void*)*7);
v___x_3342_ = lean_unsigned_to_nat(0u);
v___x_3343_ = lean_nat_dec_eq(v_bufCount_3340_, v___x_3342_);
if (v___x_3343_ == 0)
{
uint8_t v___x_3344_; 
v___x_3344_ = 1;
v___y_3336_ = v___x_3344_;
goto v___jp_3335_;
}
else
{
v___y_3336_ = v_closed_3341_;
goto v___jp_3335_;
}
v___jp_3335_:
{
lean_object* v_toPure_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_toPure_3337_ = lean_ctor_get(v_toApplicative_3333_, 1);
lean_inc(v_toPure_3337_);
lean_dec_ref(v_toApplicative_3333_);
v___x_3338_ = lean_box(v___y_3336_);
v___x_3339_ = lean_apply_2(v_toPure_3337_, lean_box(0), v___x_3338_);
return v___x_3339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3345_, lean_object* v_a_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3345_, v_a_3346_);
lean_dec_ref(v_a_3346_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3348_, lean_object* v_inst_3349_, lean_object* v_a_3350_){
_start:
{
lean_object* v_toApplicative_3351_; lean_object* v_toBind_3352_; lean_object* v___f_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_toApplicative_3351_ = lean_ctor_get(v_inst_3348_, 0);
lean_inc_ref(v_toApplicative_3351_);
v_toBind_3352_ = lean_ctor_get(v_inst_3348_, 1);
lean_inc(v_toBind_3352_);
lean_dec_ref(v_inst_3348_);
v___f_3353_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3353_, 0, v_toApplicative_3351_);
lean_inc(v_a_3350_);
v___x_3354_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3354_, 0, lean_box(0));
lean_closure_set(v___x_3354_, 1, lean_box(0));
lean_closure_set(v___x_3354_, 2, v_a_3350_);
v___x_3355_ = lean_apply_2(v_inst_3349_, lean_box(0), v___x_3354_);
v___x_3356_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3355_, v___f_3353_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object* v_inst_3357_, lean_object* v_inst_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(v_inst_3357_, v_inst_3358_, v_a_3359_);
lean_dec(v_a_3359_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3361_, lean_object* v_00_u03b1_3362_, lean_object* v_inst_3363_, lean_object* v_inst_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v_toApplicative_3366_; lean_object* v_toBind_3367_; lean_object* v___f_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_toApplicative_3366_ = lean_ctor_get(v_inst_3363_, 0);
lean_inc_ref(v_toApplicative_3366_);
v_toBind_3367_ = lean_ctor_get(v_inst_3363_, 1);
lean_inc(v_toBind_3367_);
lean_dec_ref(v_inst_3363_);
v___f_3368_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3368_, 0, v_toApplicative_3366_);
lean_inc(v_a_3365_);
v___x_3369_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3369_, 0, lean_box(0));
lean_closure_set(v___x_3369_, 1, lean_box(0));
lean_closure_set(v___x_3369_, 2, v_a_3365_);
v___x_3370_ = lean_apply_2(v_inst_3364_, lean_box(0), v___x_3369_);
v___x_3371_ = lean_apply_4(v_toBind_3367_, lean_box(0), lean_box(0), v___x_3370_, v___f_3368_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object* v_m_3372_, lean_object* v_00_u03b1_3373_, lean_object* v_inst_3374_, lean_object* v_inst_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(v_m_3372_, v_00_u03b1_3373_, v_inst_3374_, v_inst_3375_, v_a_3376_);
lean_dec(v_a_3376_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3378_){
_start:
{
lean_object* v___x_3380_; lean_object* v_producers_3381_; lean_object* v_consumers_3382_; lean_object* v_capacity_3383_; lean_object* v_buf_3384_; lean_object* v_bufCount_3385_; lean_object* v_sendIdx_3386_; lean_object* v_recvIdx_3387_; uint8_t v_closed_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3422_; 
v___x_3380_ = lean_st_ref_get(v_a_3378_);
v_producers_3381_ = lean_ctor_get(v___x_3380_, 0);
v_consumers_3382_ = lean_ctor_get(v___x_3380_, 1);
v_capacity_3383_ = lean_ctor_get(v___x_3380_, 2);
v_buf_3384_ = lean_ctor_get(v___x_3380_, 3);
v_bufCount_3385_ = lean_ctor_get(v___x_3380_, 4);
v_sendIdx_3386_ = lean_ctor_get(v___x_3380_, 5);
v_recvIdx_3387_ = lean_ctor_get(v___x_3380_, 6);
v_closed_3388_ = lean_ctor_get_uint8(v___x_3380_, sizeof(void*)*7);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3390_ = v___x_3380_;
v_isShared_3391_ = v_isSharedCheck_3422_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_recvIdx_3387_);
lean_inc(v_sendIdx_3386_);
lean_inc(v_bufCount_3385_);
lean_inc(v_buf_3384_);
lean_inc(v_capacity_3383_);
lean_inc(v_consumers_3382_);
lean_inc(v_producers_3381_);
lean_dec(v___x_3380_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3422_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3392_ = lean_unsigned_to_nat(0u);
v___x_3393_ = lean_nat_dec_eq(v_bufCount_3385_, v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v_st_3398_; lean_object* v___y_3399_; uint8_t v___x_3402_; lean_object* v___y_3404_; lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3394_ = lean_array_fget_borrowed(v_buf_3384_, v_recvIdx_3387_);
v___x_3395_ = lean_box(0);
v___x_3396_ = lean_st_ref_swap(v___x_3394_, v___x_3395_);
v___x_3402_ = 1;
v___x_3417_ = lean_unsigned_to_nat(1u);
v___x_3418_ = lean_nat_add(v_recvIdx_3387_, v___x_3417_);
lean_dec(v_recvIdx_3387_);
v___x_3419_ = lean_nat_dec_eq(v___x_3418_, v_capacity_3383_);
if (v___x_3419_ == 0)
{
v___y_3404_ = v___x_3418_;
goto v___jp_3403_;
}
else
{
lean_dec(v___x_3418_);
v___y_3404_ = v___x_3392_;
goto v___jp_3403_;
}
v___jp_3397_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_st_ref_set(v___y_3399_, v_st_3398_);
v___x_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3396_);
return v___x_3401_;
}
v___jp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3405_ = lean_unsigned_to_nat(1u);
v___x_3406_ = lean_nat_sub(v_bufCount_3385_, v___x_3405_);
lean_dec(v_bufCount_3385_);
lean_inc(v___y_3404_);
lean_inc(v_sendIdx_3386_);
lean_inc(v___x_3406_);
lean_inc_ref(v_buf_3384_);
lean_inc(v_capacity_3383_);
lean_inc_ref(v_consumers_3382_);
lean_inc_ref(v_producers_3381_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 6, v___y_3404_);
lean_ctor_set(v___x_3390_, 4, v___x_3406_);
v___x_3408_ = v___x_3390_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_producers_3381_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_consumers_3382_);
lean_ctor_set(v_reuseFailAlloc_3416_, 2, v_capacity_3383_);
lean_ctor_set(v_reuseFailAlloc_3416_, 3, v_buf_3384_);
lean_ctor_set(v_reuseFailAlloc_3416_, 4, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3416_, 5, v_sendIdx_3386_);
lean_ctor_set(v_reuseFailAlloc_3416_, 6, v___y_3404_);
lean_ctor_set_uint8(v_reuseFailAlloc_3416_, sizeof(void*)*7, v_closed_3388_);
v___x_3408_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3381_);
if (lean_obj_tag(v___x_3409_) == 1)
{
lean_object* v_val_3410_; lean_object* v_fst_3411_; lean_object* v_snd_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec_ref(v___x_3408_);
v_val_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_val_3410_);
lean_dec_ref_known(v___x_3409_, 1);
v_fst_3411_ = lean_ctor_get(v_val_3410_, 0);
lean_inc(v_fst_3411_);
v_snd_3412_ = lean_ctor_get(v_val_3410_, 1);
lean_inc(v_snd_3412_);
lean_dec(v_val_3410_);
v___x_3413_ = lean_box(v___x_3402_);
v___x_3414_ = lean_io_promise_resolve(v___x_3413_, v_fst_3411_);
lean_dec(v_fst_3411_);
v___x_3415_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3415_, 0, v_snd_3412_);
lean_ctor_set(v___x_3415_, 1, v_consumers_3382_);
lean_ctor_set(v___x_3415_, 2, v_capacity_3383_);
lean_ctor_set(v___x_3415_, 3, v_buf_3384_);
lean_ctor_set(v___x_3415_, 4, v___x_3406_);
lean_ctor_set(v___x_3415_, 5, v_sendIdx_3386_);
lean_ctor_set(v___x_3415_, 6, v___y_3404_);
lean_ctor_set_uint8(v___x_3415_, sizeof(void*)*7, v_closed_3388_);
v_st_3398_ = v___x_3415_;
v___y_3399_ = v_a_3378_;
goto v___jp_3397_;
}
else
{
lean_dec(v___x_3409_);
lean_dec(v___x_3406_);
lean_dec(v___y_3404_);
lean_dec(v_sendIdx_3386_);
lean_dec_ref(v_buf_3384_);
lean_dec(v_capacity_3383_);
lean_dec_ref(v_consumers_3382_);
v_st_3398_ = v___x_3408_;
v___y_3399_ = v_a_3378_;
goto v___jp_3397_;
}
}
}
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_del_object(v___x_3390_);
lean_dec(v_recvIdx_3387_);
lean_dec(v_sendIdx_3386_);
lean_dec(v_bufCount_3385_);
lean_dec_ref(v_buf_3384_);
lean_dec(v_capacity_3383_);
lean_dec_ref(v_consumers_3382_);
lean_dec_ref(v_producers_3381_);
v___x_3420_ = lean_box(0);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3423_);
lean_dec(v_a_3423_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3430_, lean_object* v_a_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3430_, v_a_3431_);
lean_dec(v_a_3431_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3434_, lean_object* v_lose_3435_){
_start:
{
lean_object* v_finished_3437_; lean_object* v_promise_3438_; lean_object* v___x_3439_; uint8_t v___y_3441_; uint8_t v___x_3449_; 
v_finished_3437_ = lean_ctor_get(v_w_3434_, 0);
v_promise_3438_ = lean_ctor_get(v_w_3434_, 1);
v___x_3439_ = lean_st_ref_take(v_finished_3437_);
v___x_3449_ = lean_unbox(v___x_3439_);
lean_dec(v___x_3439_);
if (v___x_3449_ == 0)
{
uint8_t v___x_3450_; 
v___x_3450_ = 1;
v___y_3441_ = v___x_3450_;
goto v___jp_3440_;
}
else
{
uint8_t v___x_3451_; 
v___x_3451_ = 0;
v___y_3441_ = v___x_3451_;
goto v___jp_3440_;
}
v___jp_3440_:
{
uint8_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = 1;
v___x_3443_ = lean_box(v___x_3442_);
v___x_3444_ = lean_st_ref_set(v_finished_3437_, v___x_3443_);
if (v___y_3441_ == 0)
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_apply_1(v_lose_3435_, lean_box(0));
return v___x_3445_;
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec_ref(v_lose_3435_);
v___x_3446_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0));
v___x_3447_ = lean_io_promise_resolve(v___x_3446_, v_promise_3438_);
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
return v___x_3448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3452_, lean_object* v_lose_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3452_, v_lose_3453_);
lean_dec_ref(v_w_3452_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3456_, lean_object* v_w_3457_, lean_object* v_lose_3458_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3457_, v_lose_3458_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3461_, lean_object* v_w_3462_, lean_object* v_lose_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3461_, v_w_3462_, v_lose_3463_);
lean_dec_ref(v_w_3462_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3466_, lean_object* v_lose_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v_finished_3470_; lean_object* v_promise_3471_; lean_object* v___x_3472_; uint8_t v___y_3474_; uint8_t v___x_3490_; 
v_finished_3470_ = lean_ctor_get(v_w_3466_, 0);
v_promise_3471_ = lean_ctor_get(v_w_3466_, 1);
v___x_3472_ = lean_st_ref_take(v_finished_3470_);
v___x_3490_ = lean_unbox(v___x_3472_);
lean_dec(v___x_3472_);
if (v___x_3490_ == 0)
{
uint8_t v___x_3491_; 
v___x_3491_ = 1;
v___y_3474_ = v___x_3491_;
goto v___jp_3473_;
}
else
{
uint8_t v___x_3492_; 
v___x_3492_ = 0;
v___y_3474_ = v___x_3492_;
goto v___jp_3473_;
}
v___jp_3473_:
{
uint8_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = 1;
v___x_3476_ = lean_box(v___x_3475_);
v___x_3477_ = lean_st_ref_set(v_finished_3470_, v___x_3476_);
if (v___y_3474_ == 0)
{
lean_object* v___x_3478_; 
lean_inc(v___y_3468_);
v___x_3478_ = lean_apply_2(v_lose_3467_, v___y_3468_, lean_box(0));
return v___x_3478_;
}
else
{
lean_object* v___x_3479_; lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_lose_3467_);
v___x_3479_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3468_);
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3489_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3489_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_a_3480_);
v___x_3485_ = lean_io_promise_resolve(v___x_3484_, v_promise_3471_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3485_);
v___x_3487_ = v___x_3482_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
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
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3493_, lean_object* v_lose_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3493_, v_lose_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v_w_3493_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3498_, lean_object* v_w_3499_, lean_object* v_lose_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3499_, v_lose_3500_, v___y_3501_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3504_, lean_object* v_w_3505_, lean_object* v_lose_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3504_, v_w_3505_, v_lose_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v_w_3505_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3510_, lean_object* v_k_3511_){
_start:
{
lean_object* v_ref_3513_; lean_object* v_mutex_3514_; lean_object* v___x_3515_; lean_object* v_r_3516_; 
v_ref_3513_ = lean_ctor_get(v_mutex_3510_, 0);
lean_inc(v_ref_3513_);
v_mutex_3514_ = lean_ctor_get(v_mutex_3510_, 1);
lean_inc(v_mutex_3514_);
lean_dec_ref(v_mutex_3510_);
v___x_3515_ = lean_io_basemutex_lock(v_mutex_3514_);
v_r_3516_ = lean_apply_2(v_k_3511_, v_ref_3513_, lean_box(0));
if (lean_obj_tag(v_r_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3525_; 
v_a_3517_ = lean_ctor_get(v_r_3516_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_r_3516_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3519_ = v_r_3516_;
v_isShared_3520_ = v_isSharedCheck_3525_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v_r_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3525_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3521_ = lean_io_basemutex_unlock(v_mutex_3514_);
lean_dec(v_mutex_3514_);
if (v_isShared_3520_ == 0)
{
v___x_3523_ = v___x_3519_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3517_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3534_; 
v_a_3526_ = lean_ctor_get(v_r_3516_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_r_3516_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3528_ = v_r_3516_;
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v_r_3516_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3530_ = lean_io_basemutex_unlock(v_mutex_3514_);
lean_dec(v_mutex_3514_);
if (v_isShared_3529_ == 0)
{
v___x_3532_ = v___x_3528_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3526_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3535_, lean_object* v_k_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3535_, v_k_3536_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3539_, lean_object* v_00_u03b2_3540_, lean_object* v_mutex_3541_, lean_object* v_k_3542_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3541_, v_k_3542_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3545_, lean_object* v_00_u03b2_3546_, lean_object* v_mutex_3547_, lean_object* v_k_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3545_, v_00_u03b2_3546_, v_mutex_3547_, v_k_3548_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3551_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3554_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; lean_object* v_producers_3561_; lean_object* v_consumers_3562_; lean_object* v_capacity_3563_; lean_object* v_buf_3564_; lean_object* v_bufCount_3565_; lean_object* v_sendIdx_3566_; lean_object* v_recvIdx_3567_; uint8_t v_closed_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3590_; 
v___x_3560_ = lean_st_ref_get(v___y_3558_);
v_producers_3561_ = lean_ctor_get(v___x_3560_, 0);
v_consumers_3562_ = lean_ctor_get(v___x_3560_, 1);
v_capacity_3563_ = lean_ctor_get(v___x_3560_, 2);
v_buf_3564_ = lean_ctor_get(v___x_3560_, 3);
v_bufCount_3565_ = lean_ctor_get(v___x_3560_, 4);
v_sendIdx_3566_ = lean_ctor_get(v___x_3560_, 5);
v_recvIdx_3567_ = lean_ctor_get(v___x_3560_, 6);
v_closed_3568_ = lean_ctor_get_uint8(v___x_3560_, sizeof(void*)*7);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3570_ = v___x_3560_;
v_isShared_3571_ = v_isSharedCheck_3590_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_recvIdx_3567_);
lean_inc(v_sendIdx_3566_);
lean_inc(v_bufCount_3565_);
lean_inc(v_buf_3564_);
lean_inc(v_capacity_3563_);
lean_inc(v_consumers_3562_);
lean_inc(v_producers_3561_);
lean_dec(v___x_3560_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3590_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3562_);
if (lean_obj_tag(v___x_3572_) == 1)
{
lean_object* v_val_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3587_; 
v_val_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3587_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_val_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3587_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v_fst_3577_; lean_object* v_snd_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v_fst_3577_ = lean_ctor_get(v_val_3573_, 0);
lean_inc(v_fst_3577_);
v_snd_3578_ = lean_ctor_get(v_val_3573_, 1);
lean_inc(v_snd_3578_);
lean_dec(v_val_3573_);
v___x_3579_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3577_, v_____do__lift_3557_);
lean_dec(v_fst_3577_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 1, v_snd_3578_);
v___x_3581_ = v___x_3570_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_producers_3561_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_snd_3578_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_capacity_3563_);
lean_ctor_set(v_reuseFailAlloc_3586_, 3, v_buf_3564_);
lean_ctor_set(v_reuseFailAlloc_3586_, 4, v_bufCount_3565_);
lean_ctor_set(v_reuseFailAlloc_3586_, 5, v_sendIdx_3566_);
lean_ctor_set(v_reuseFailAlloc_3586_, 6, v_recvIdx_3567_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, sizeof(void*)*7, v_closed_3568_);
v___x_3581_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3582_ = lean_st_ref_set(v___y_3558_, v___x_3581_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set_tag(v___x_3575_, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3582_);
v___x_3584_ = v___x_3575_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_dec(v___x_3572_);
lean_del_object(v___x_3570_);
lean_dec(v_recvIdx_3567_);
lean_dec(v_sendIdx_3566_);
lean_dec(v_bufCount_3565_);
lean_dec_ref(v_buf_3564_);
lean_dec(v_capacity_3563_);
lean_dec_ref(v_producers_3561_);
v___x_3588_ = lean_box(0);
v___x_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
return v___x_3589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
uint8_t v_____do__lift_3921__boxed_3594_; lean_object* v_res_3595_; 
v_____do__lift_3921__boxed_3594_ = lean_unbox(v_____do__lift_3591_);
v_res_3595_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3921__boxed_3594_, v___y_3592_);
lean_dec(v___y_3592_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3596_, lean_object* v___f_3597_, uint8_t v_____do__lift_3598_, lean_object* v___y_3599_){
_start:
{
if (v_____do__lift_3598_ == 0)
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v_producers_3603_; lean_object* v_consumers_3604_; lean_object* v_capacity_3605_; lean_object* v_buf_3606_; lean_object* v_bufCount_3607_; lean_object* v_sendIdx_3608_; lean_object* v_recvIdx_3609_; uint8_t v_closed_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3624_; 
v___x_3601_ = lean_io_promise_new();
v___x_3602_ = lean_st_ref_take(v___y_3599_);
v_producers_3603_ = lean_ctor_get(v___x_3602_, 0);
v_consumers_3604_ = lean_ctor_get(v___x_3602_, 1);
v_capacity_3605_ = lean_ctor_get(v___x_3602_, 2);
v_buf_3606_ = lean_ctor_get(v___x_3602_, 3);
v_bufCount_3607_ = lean_ctor_get(v___x_3602_, 4);
v_sendIdx_3608_ = lean_ctor_get(v___x_3602_, 5);
v_recvIdx_3609_ = lean_ctor_get(v___x_3602_, 6);
v_closed_3610_ = lean_ctor_get_uint8(v___x_3602_, sizeof(void*)*7);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3612_ = v___x_3602_;
v_isShared_3613_ = v_isSharedCheck_3624_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_recvIdx_3609_);
lean_inc(v_sendIdx_3608_);
lean_inc(v_bufCount_3607_);
lean_inc(v_buf_3606_);
lean_inc(v_capacity_3605_);
lean_inc(v_consumers_3604_);
lean_inc(v_producers_3603_);
lean_dec(v___x_3602_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3624_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3614_, 0, v_waiter_3596_);
lean_inc(v___x_3601_);
v___x_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3601_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l_Std_Queue_enqueue___redArg(v___x_3615_, v_consumers_3604_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v___x_3616_);
v___x_3618_ = v___x_3612_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_producers_3603_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3623_, 2, v_capacity_3605_);
lean_ctor_set(v_reuseFailAlloc_3623_, 3, v_buf_3606_);
lean_ctor_set(v_reuseFailAlloc_3623_, 4, v_bufCount_3607_);
lean_ctor_set(v_reuseFailAlloc_3623_, 5, v_sendIdx_3608_);
lean_ctor_set(v_reuseFailAlloc_3623_, 6, v_recvIdx_3609_);
lean_ctor_set_uint8(v_reuseFailAlloc_3623_, sizeof(void*)*7, v_closed_3610_);
v___x_3618_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3619_ = lean_st_ref_set(v___y_3599_, v___x_3618_);
v___x_3620_ = lean_io_promise_result_opt(v___x_3601_);
lean_dec(v___x_3601_);
v___x_3621_ = lean_unsigned_to_nat(0u);
v___x_3622_ = l_EIO_chainTask___redArg(v___x_3620_, v___f_3597_, v___x_3621_, v_____do__lift_3598_);
return v___x_3622_;
}
}
}
else
{
lean_object* v___x_3625_; lean_object* v_lose_3626_; lean_object* v___x_3627_; 
lean_dec_ref(v___f_3597_);
v___x_3625_ = lean_box(v_____do__lift_3598_);
v_lose_3626_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3626_, 0, v___x_3625_);
v___x_3627_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3596_, v_lose_3626_, v___y_3599_);
lean_dec_ref(v_waiter_3596_);
return v___x_3627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3628_, lean_object* v___f_3629_, lean_object* v_____do__lift_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
uint8_t v_____do__lift_3977__boxed_3633_; lean_object* v_res_3634_; 
v_____do__lift_3977__boxed_3633_ = lean_unbox(v_____do__lift_3630_);
v_res_3634_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3628_, v___f_3629_, v_____do__lift_3977__boxed_3633_, v___y_3631_);
lean_dec(v___y_3631_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v___x_3638_; lean_object* v_bufCount_3639_; uint8_t v_closed_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3638_ = lean_st_ref_get(v___y_3636_);
v_bufCount_3639_ = lean_ctor_get(v___x_3638_, 4);
lean_inc(v_bufCount_3639_);
v_closed_3640_ = lean_ctor_get_uint8(v___x_3638_, sizeof(void*)*7);
lean_dec(v___x_3638_);
v___x_3641_ = lean_unsigned_to_nat(0u);
v___x_3642_ = lean_nat_dec_eq(v_bufCount_3639_, v___x_3641_);
lean_dec(v_bufCount_3639_);
if (v___x_3642_ == 0)
{
uint8_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = 1;
v___x_3644_ = lean_box(v___x_3643_);
lean_inc(v___y_3636_);
v___x_3645_ = lean_apply_3(v___f_3635_, v___x_3644_, v___y_3636_, lean_box(0));
return v___x_3645_;
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_box(v_closed_3640_);
lean_inc(v___y_3636_);
v___x_3647_ = lean_apply_3(v___f_3635_, v___x_3646_, v___y_3636_, lean_box(0));
return v___x_3647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3648_, v___y_3649_);
lean_dec(v___y_3649_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3654_, lean_object* v_ch_3655_, lean_object* v_x_3656_){
_start:
{
if (lean_obj_tag(v_x_3656_) == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_dec_ref(v_ch_3655_);
lean_dec_ref(v_waiter_3654_);
v___x_3658_ = lean_box(0);
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
return v___x_3659_;
}
else
{
lean_object* v_val_3660_; uint8_t v___x_3661_; 
v_val_3660_ = lean_ctor_get(v_x_3656_, 0);
v___x_3661_ = lean_unbox(v_val_3660_);
if (v___x_3661_ == 0)
{
lean_object* v___f_3662_; lean_object* v___x_3663_; 
lean_dec_ref(v_ch_3655_);
v___f_3662_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3663_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3654_, v___f_3662_);
lean_dec_ref(v_waiter_3654_);
return v___x_3663_;
}
else
{
lean_object* v___x_3664_; 
v___x_3664_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3655_, v_waiter_3654_);
return v___x_3664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3665_, lean_object* v_ch_3666_, lean_object* v_x_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3665_, v_ch_3666_, v_x_3667_);
lean_dec(v_x_3667_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3670_, lean_object* v_waiter_3671_){
_start:
{
lean_object* v___f_3673_; lean_object* v___f_3674_; lean_object* v___f_3675_; lean_object* v___x_3676_; 
lean_inc_ref(v_ch_3670_);
lean_inc_ref(v_waiter_3671_);
v___f_3673_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3673_, 0, v_waiter_3671_);
lean_closure_set(v___f_3673_, 1, v_ch_3670_);
v___f_3674_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3674_, 0, v_waiter_3671_);
lean_closure_set(v___f_3674_, 1, v___f_3673_);
v___f_3675_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3675_, 0, v___f_3674_);
v___x_3676_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3670_, v___f_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3677_, lean_object* v_waiter_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3677_, v_waiter_3678_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3681_, lean_object* v_ch_3682_, lean_object* v_waiter_3683_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3682_, v_waiter_3683_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3686_, lean_object* v_ch_3687_, lean_object* v_waiter_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3686_, v_ch_3687_, v_waiter_3688_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3691_, lean_object* v_x_3692_){
_start:
{
if (lean_obj_tag(v_x_3692_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3702_; 
lean_dec_ref(v_x_3691_);
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
lean_object* v___x_3703_; 
lean_dec_ref_known(v_x_3692_, 1);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v_x_3691_);
return v___x_3703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3704_, lean_object* v_x_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3704_, v_x_3705_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3708_, uint8_t v___x_3709_, lean_object* v___f_3710_, lean_object* v_____r_3711_, lean_object* v_st_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3715_ = lean_st_ref_set(v___y_3713_, v_st_3712_);
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
v___x_3718_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3708_, v___x_3709_, v___x_3717_, v___f_3710_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3719_, lean_object* v___x_3720_, lean_object* v___f_3721_, lean_object* v_____r_3722_, lean_object* v_st_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
uint8_t v___x_6388__boxed_3726_; lean_object* v_res_3727_; 
v___x_6388__boxed_3726_ = lean_unbox(v___x_3720_);
v_res_3727_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3719_, v___x_6388__boxed_3726_, v___f_3721_, v_____r_3722_, v_st_3723_, v___y_3724_);
lean_dec(v___y_3724_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3728_, lean_object* v_consumers_3729_, lean_object* v_capacity_3730_, lean_object* v_buf_3731_, lean_object* v___x_3732_, lean_object* v_sendIdx_3733_, lean_object* v___y_3734_, uint8_t v_closed_3735_, lean_object* v___f_3736_, lean_object* v_a_3737_, lean_object* v_x_3738_){
_start:
{
if (lean_obj_tag(v_x_3738_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v___f_3736_);
lean_dec(v___y_3734_);
lean_dec(v_sendIdx_3733_);
lean_dec(v___x_3732_);
lean_dec_ref(v_buf_3731_);
lean_dec(v_capacity_3730_);
lean_dec_ref(v_consumers_3729_);
lean_dec_ref(v_snd_3728_);
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
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_dec_ref_known(v_x_3738_, 1);
v___x_3749_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3749_, 0, v_snd_3728_);
lean_ctor_set(v___x_3749_, 1, v_consumers_3729_);
lean_ctor_set(v___x_3749_, 2, v_capacity_3730_);
lean_ctor_set(v___x_3749_, 3, v_buf_3731_);
lean_ctor_set(v___x_3749_, 4, v___x_3732_);
lean_ctor_set(v___x_3749_, 5, v_sendIdx_3733_);
lean_ctor_set(v___x_3749_, 6, v___y_3734_);
lean_ctor_set_uint8(v___x_3749_, sizeof(void*)*7, v_closed_3735_);
v___x_3750_ = lean_box(0);
lean_inc(v_a_3737_);
v___x_3751_ = lean_apply_4(v___f_3736_, v___x_3750_, v___x_3749_, v_a_3737_, lean_box(0));
return v___x_3751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3752_, lean_object* v_consumers_3753_, lean_object* v_capacity_3754_, lean_object* v_buf_3755_, lean_object* v___x_3756_, lean_object* v_sendIdx_3757_, lean_object* v___y_3758_, lean_object* v_closed_3759_, lean_object* v___f_3760_, lean_object* v_a_3761_, lean_object* v_x_3762_, lean_object* v___y_3763_){
_start:
{
uint8_t v_closed_boxed_3764_; lean_object* v_res_3765_; 
v_closed_boxed_3764_ = lean_unbox(v_closed_3759_);
v_res_3765_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3752_, v_consumers_3753_, v_capacity_3754_, v_buf_3755_, v___x_3756_, v_sendIdx_3757_, v___y_3758_, v_closed_boxed_3764_, v___f_3760_, v_a_3761_, v_x_3762_);
lean_dec(v_a_3761_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3766_, uint8_t v___x_3767_, lean_object* v_bufCount_3768_, lean_object* v_producers_3769_, lean_object* v_consumers_3770_, lean_object* v_capacity_3771_, lean_object* v_buf_3772_, lean_object* v_sendIdx_3773_, uint8_t v_closed_3774_, uint8_t v___x_3775_, lean_object* v_a_3776_, lean_object* v_recvIdx_3777_, lean_object* v_x_3778_){
_start:
{
if (lean_obj_tag(v_x_3778_) == 0)
{
lean_object* v___x_3780_; 
lean_dec(v_sendIdx_3773_);
lean_dec_ref(v_buf_3772_);
lean_dec(v_capacity_3771_);
lean_dec_ref(v_consumers_3770_);
lean_dec_ref(v_producers_3769_);
lean_dec(v___x_3766_);
v___x_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3780_, 0, v_x_3778_);
return v___x_3780_;
}
else
{
lean_object* v___f_3781_; lean_object* v___x_3782_; lean_object* v___f_3783_; lean_object* v___y_3785_; lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___f_3781_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3781_, 0, v_x_3778_);
v___x_3782_ = lean_box(v___x_3767_);
lean_inc_ref(v___f_3781_);
lean_inc(v___x_3766_);
v___f_3783_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3783_, 0, v___x_3766_);
lean_closure_set(v___f_3783_, 1, v___x_3782_);
lean_closure_set(v___f_3783_, 2, v___f_3781_);
v___x_3808_ = lean_unsigned_to_nat(1u);
v___x_3809_ = lean_nat_add(v_recvIdx_3777_, v___x_3808_);
v___x_3810_ = lean_nat_dec_eq(v___x_3809_, v_capacity_3771_);
if (v___x_3810_ == 0)
{
v___y_3785_ = v___x_3809_;
goto v___jp_3784_;
}
else
{
lean_dec(v___x_3809_);
lean_inc(v___x_3766_);
v___y_3785_ = v___x_3766_;
goto v___jp_3784_;
}
v___jp_3784_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3786_ = lean_unsigned_to_nat(1u);
v___x_3787_ = lean_nat_sub(v_bufCount_3768_, v___x_3786_);
lean_inc(v___y_3785_);
lean_inc(v_sendIdx_3773_);
lean_inc(v___x_3787_);
lean_inc_ref(v_buf_3772_);
lean_inc(v_capacity_3771_);
lean_inc_ref(v_consumers_3770_);
lean_inc_ref(v_producers_3769_);
v___x_3788_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3788_, 0, v_producers_3769_);
lean_ctor_set(v___x_3788_, 1, v_consumers_3770_);
lean_ctor_set(v___x_3788_, 2, v_capacity_3771_);
lean_ctor_set(v___x_3788_, 3, v_buf_3772_);
lean_ctor_set(v___x_3788_, 4, v___x_3787_);
lean_ctor_set(v___x_3788_, 5, v_sendIdx_3773_);
lean_ctor_set(v___x_3788_, 6, v___y_3785_);
lean_ctor_set_uint8(v___x_3788_, sizeof(void*)*7, v_closed_3774_);
v___x_3789_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3769_);
if (lean_obj_tag(v___x_3789_) == 1)
{
lean_object* v_val_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3805_; 
lean_dec_ref_known(v___x_3788_, 7);
lean_dec_ref(v___f_3781_);
v_val_3790_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3792_ = v___x_3789_;
v_isShared_3793_ = v_isSharedCheck_3805_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_val_3790_);
lean_dec(v___x_3789_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3805_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_fst_3794_; lean_object* v_snd_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___f_3799_; lean_object* v___x_3801_; 
v_fst_3794_ = lean_ctor_get(v_val_3790_, 0);
lean_inc(v_fst_3794_);
v_snd_3795_ = lean_ctor_get(v_val_3790_, 1);
lean_inc(v_snd_3795_);
lean_dec(v_val_3790_);
v___x_3796_ = lean_box(v___x_3775_);
v___x_3797_ = lean_io_promise_resolve(v___x_3796_, v_fst_3794_);
lean_dec(v_fst_3794_);
v___x_3798_ = lean_box(v_closed_3774_);
lean_inc(v_a_3776_);
v___f_3799_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3799_, 0, v_snd_3795_);
lean_closure_set(v___f_3799_, 1, v_consumers_3770_);
lean_closure_set(v___f_3799_, 2, v_capacity_3771_);
lean_closure_set(v___f_3799_, 3, v_buf_3772_);
lean_closure_set(v___f_3799_, 4, v___x_3787_);
lean_closure_set(v___f_3799_, 5, v_sendIdx_3773_);
lean_closure_set(v___f_3799_, 6, v___y_3785_);
lean_closure_set(v___f_3799_, 7, v___x_3798_);
lean_closure_set(v___f_3799_, 8, v___f_3783_);
lean_closure_set(v___f_3799_, 9, v_a_3776_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3797_);
v___x_3801_ = v___x_3792_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3797_);
v___x_3801_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
v___x_3803_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3766_, v___x_3767_, v___x_3802_, v___f_3799_);
return v___x_3803_;
}
}
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
lean_dec(v___x_3789_);
lean_dec(v___x_3787_);
lean_dec(v___y_3785_);
lean_dec_ref(v___f_3783_);
lean_dec(v_sendIdx_3773_);
lean_dec_ref(v_buf_3772_);
lean_dec(v_capacity_3771_);
lean_dec_ref(v_consumers_3770_);
v___x_3806_ = lean_box(0);
v___x_3807_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3766_, v___x_3767_, v___f_3781_, v___x_3806_, v___x_3788_, v_a_3776_);
return v___x_3807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3811_, lean_object* v___x_3812_, lean_object* v_bufCount_3813_, lean_object* v_producers_3814_, lean_object* v_consumers_3815_, lean_object* v_capacity_3816_, lean_object* v_buf_3817_, lean_object* v_sendIdx_3818_, lean_object* v_closed_3819_, lean_object* v___x_3820_, lean_object* v_a_3821_, lean_object* v_recvIdx_3822_, lean_object* v_x_3823_, lean_object* v___y_3824_){
_start:
{
uint8_t v___x_6457__boxed_3825_; uint8_t v_closed_boxed_3826_; uint8_t v___x_6458__boxed_3827_; lean_object* v_res_3828_; 
v___x_6457__boxed_3825_ = lean_unbox(v___x_3812_);
v_closed_boxed_3826_ = lean_unbox(v_closed_3819_);
v___x_6458__boxed_3827_ = lean_unbox(v___x_3820_);
v_res_3828_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3811_, v___x_6457__boxed_3825_, v_bufCount_3813_, v_producers_3814_, v_consumers_3815_, v_capacity_3816_, v_buf_3817_, v_sendIdx_3818_, v_closed_boxed_3826_, v___x_6458__boxed_3827_, v_a_3821_, v_recvIdx_3822_, v_x_3823_);
lean_dec(v_recvIdx_3822_);
lean_dec(v_a_3821_);
lean_dec(v_bufCount_3813_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3829_, lean_object* v_x_3830_){
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
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3869_; 
v_a_3841_ = lean_ctor_get(v_x_3830_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_x_3830_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3843_ = v_x_3830_;
v_isShared_3844_ = v_isSharedCheck_3869_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v_x_3830_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3869_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v_producers_3845_; lean_object* v_consumers_3846_; lean_object* v_capacity_3847_; lean_object* v_buf_3848_; lean_object* v_bufCount_3849_; lean_object* v_sendIdx_3850_; lean_object* v_recvIdx_3851_; uint8_t v_closed_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; 
v_producers_3845_ = lean_ctor_get(v_a_3841_, 0);
lean_inc_ref(v_producers_3845_);
v_consumers_3846_ = lean_ctor_get(v_a_3841_, 1);
lean_inc_ref(v_consumers_3846_);
v_capacity_3847_ = lean_ctor_get(v_a_3841_, 2);
lean_inc(v_capacity_3847_);
v_buf_3848_ = lean_ctor_get(v_a_3841_, 3);
lean_inc_ref(v_buf_3848_);
v_bufCount_3849_ = lean_ctor_get(v_a_3841_, 4);
lean_inc(v_bufCount_3849_);
v_sendIdx_3850_ = lean_ctor_get(v_a_3841_, 5);
lean_inc(v_sendIdx_3850_);
v_recvIdx_3851_ = lean_ctor_get(v_a_3841_, 6);
lean_inc(v_recvIdx_3851_);
v_closed_3852_ = lean_ctor_get_uint8(v_a_3841_, sizeof(void*)*7);
lean_dec(v_a_3841_);
v___x_3853_ = lean_unsigned_to_nat(0u);
v___x_3854_ = lean_nat_dec_eq(v_bufCount_3849_, v___x_3853_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___f_3862_; lean_object* v___x_3864_; 
v___x_3855_ = lean_array_fget_borrowed(v_buf_3848_, v_recvIdx_3851_);
v___x_3856_ = lean_box(0);
v___x_3857_ = lean_st_ref_swap(v___x_3855_, v___x_3856_);
v___x_3858_ = 1;
v___x_3859_ = lean_box(v___x_3854_);
v___x_3860_ = lean_box(v_closed_3852_);
v___x_3861_ = lean_box(v___x_3858_);
lean_inc(v_a_3829_);
v___f_3862_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_3862_, 0, v___x_3853_);
lean_closure_set(v___f_3862_, 1, v___x_3859_);
lean_closure_set(v___f_3862_, 2, v_bufCount_3849_);
lean_closure_set(v___f_3862_, 3, v_producers_3845_);
lean_closure_set(v___f_3862_, 4, v_consumers_3846_);
lean_closure_set(v___f_3862_, 5, v_capacity_3847_);
lean_closure_set(v___f_3862_, 6, v_buf_3848_);
lean_closure_set(v___f_3862_, 7, v_sendIdx_3850_);
lean_closure_set(v___f_3862_, 8, v___x_3860_);
lean_closure_set(v___f_3862_, 9, v___x_3861_);
lean_closure_set(v___f_3862_, 10, v_a_3829_);
lean_closure_set(v___f_3862_, 11, v_recvIdx_3851_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3857_);
v___x_3864_ = v___x_3843_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3857_);
v___x_3864_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
v___x_3866_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3853_, v___x_3854_, v___x_3865_, v___f_3862_);
return v___x_3866_;
}
}
else
{
lean_object* v___x_3868_; 
lean_dec(v_recvIdx_3851_);
lean_dec(v_sendIdx_3850_);
lean_dec(v_bufCount_3849_);
lean_dec_ref(v_buf_3848_);
lean_dec(v_capacity_3847_);
lean_dec_ref(v_consumers_3846_);
lean_dec_ref(v_producers_3845_);
lean_del_object(v___x_3843_);
v___x_3868_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_3868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_3870_, lean_object* v_x_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3870_, v_x_3871_);
lean_dec(v_a_3870_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_3874_){
_start:
{
lean_object* v___x_3876_; lean_object* v___f_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; lean_object* v___x_3882_; 
v___x_3876_ = lean_st_ref_get(v_a_3874_);
lean_inc(v_a_3874_);
v___f_3877_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3877_, 0, v_a_3874_);
v___x_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3876_);
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
v___x_3880_ = lean_unsigned_to_nat(0u);
v___x_3881_ = 0;
v___x_3882_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3880_, v___x_3881_, v___x_3879_, v___f_3877_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3883_);
lean_dec(v_a_3883_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_3890_, lean_object* v_a_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_3890_, v_a_3891_);
lean_dec(v_a_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_3894_, lean_object* v_x_3895_){
_start:
{
lean_object* v_val_3898_; lean_object* v___x_3900_; 
v___x_3900_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3894_, v_x_3895_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3900_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
lean_ctor_set_tag(v___x_3903_, 1);
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
v_val_3898_ = v___x_3906_;
goto v___jp_3897_;
}
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
v_a_3909_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3900_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3900_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
lean_ctor_set_tag(v___x_3911_, 0);
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
v_val_3898_ = v___x_3914_;
goto v___jp_3897_;
}
}
}
v___jp_3897_:
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v_val_3898_);
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_3917_, lean_object* v_x_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_3917_, v_x_3918_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v_x_3921_){
_start:
{
uint8_t v___y_3924_; 
if (lean_obj_tag(v_x_3921_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3936_; 
v_a_3928_ = lean_ctor_get(v_x_3921_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_x_3921_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3930_ = v_x_3921_;
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v_x_3921_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
return v___x_3934_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v_bufCount_3938_; uint8_t v_closed_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; 
v_a_3937_ = lean_ctor_get(v_x_3921_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v_x_3921_, 1);
v_bufCount_3938_ = lean_ctor_get(v_a_3937_, 4);
lean_inc(v_bufCount_3938_);
v_closed_3939_ = lean_ctor_get_uint8(v_a_3937_, sizeof(void*)*7);
lean_dec(v_a_3937_);
v___x_3940_ = lean_unsigned_to_nat(0u);
v___x_3941_ = lean_nat_dec_eq(v_bufCount_3938_, v___x_3940_);
lean_dec(v_bufCount_3938_);
if (v___x_3941_ == 0)
{
uint8_t v___x_3942_; 
v___x_3942_ = 1;
v___y_3924_ = v___x_3942_;
goto v___jp_3923_;
}
else
{
v___y_3924_ = v_closed_3939_;
goto v___jp_3923_;
}
}
v___jp_3923_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3925_ = lean_box(v___y_3924_);
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v_x_3943_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___y_3946_, lean_object* v___f_3947_, lean_object* v_x_3948_){
_start:
{
if (lean_obj_tag(v_x_3948_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3958_; 
lean_dec_ref(v___f_3947_);
v_a_3950_ = lean_ctor_get(v_x_3948_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_x_3948_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3952_ = v_x_3948_;
v_isShared_3953_ = v_isSharedCheck_3958_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v_x_3948_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3958_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3956_; 
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
return v___x_3956_;
}
}
}
else
{
lean_object* v_a_3959_; uint8_t v___x_3960_; 
v_a_3959_ = lean_ctor_get(v_x_3948_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v_x_3948_, 1);
v___x_3960_ = lean_unbox(v_a_3959_);
lean_dec(v_a_3959_);
if (v___x_3960_ == 0)
{
lean_object* v___x_3961_; 
lean_dec_ref(v___f_3947_);
v___x_3961_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_3961_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; lean_object* v___x_3965_; 
v___x_3962_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_3946_);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = 0;
v___x_3965_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3963_, v___x_3964_, v___x_3962_, v___f_3947_);
return v___x_3965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___y_3966_, lean_object* v___f_3967_, lean_object* v_x_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___y_3966_, v___f_3967_, v_x_3968_);
lean_dec(v___y_3966_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_3971_, lean_object* v___f_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; lean_object* v___x_3980_; lean_object* v___f_3981_; lean_object* v___x_3982_; 
v___x_3975_ = lean_st_ref_get(v___y_3973_);
v___x_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
v___x_3978_ = lean_unsigned_to_nat(0u);
v___x_3979_ = 0;
v___x_3980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3978_, v___x_3979_, v___x_3977_, v___f_3971_);
lean_inc(v___y_3973_);
v___f_3981_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3981_, 0, v___y_3973_);
lean_closure_set(v___f_3981_, 1, v___f_3972_);
v___x_3982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3978_, v___x_3979_, v___x_3980_, v___f_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_3983_, lean_object* v___f_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_3983_, v___f_3984_, v___y_3985_);
lean_dec(v___y_3985_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_3988_, lean_object* v_capacity_3989_, lean_object* v_buf_3990_, lean_object* v_bufCount_3991_, lean_object* v_sendIdx_3992_, lean_object* v_recvIdx_3993_, uint8_t v_closed_3994_, lean_object* v___y_3995_, lean_object* v_x_3996_){
_start:
{
if (lean_obj_tag(v_x_3996_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4006_; 
lean_dec(v_recvIdx_3993_);
lean_dec(v_sendIdx_3992_);
lean_dec(v_bufCount_3991_);
lean_dec_ref(v_buf_3990_);
lean_dec(v_capacity_3989_);
lean_dec_ref(v_producers_3988_);
v_a_3998_ = lean_ctor_get(v_x_3996_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_x_3996_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4000_ = v_x_3996_;
v_isShared_4001_ = v_isSharedCheck_4006_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v_x_3996_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4006_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
return v___x_4004_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4017_; 
v_a_4007_ = lean_ctor_get(v_x_3996_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_x_3996_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4009_ = v_x_3996_;
v_isShared_4010_ = v_isSharedCheck_4017_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v_x_3996_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4017_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4014_; 
v___x_4011_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_4011_, 0, v_producers_3988_);
lean_ctor_set(v___x_4011_, 1, v_a_4007_);
lean_ctor_set(v___x_4011_, 2, v_capacity_3989_);
lean_ctor_set(v___x_4011_, 3, v_buf_3990_);
lean_ctor_set(v___x_4011_, 4, v_bufCount_3991_);
lean_ctor_set(v___x_4011_, 5, v_sendIdx_3992_);
lean_ctor_set(v___x_4011_, 6, v_recvIdx_3993_);
lean_ctor_set_uint8(v___x_4011_, sizeof(void*)*7, v_closed_3994_);
v___x_4012_ = lean_st_ref_set(v___y_3995_, v___x_4011_);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 0, v___x_4012_);
v___x_4014_ = v___x_4009_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
return v___x_4015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_4018_, lean_object* v_capacity_4019_, lean_object* v_buf_4020_, lean_object* v_bufCount_4021_, lean_object* v_sendIdx_4022_, lean_object* v_recvIdx_4023_, lean_object* v_closed_4024_, lean_object* v___y_4025_, lean_object* v_x_4026_, lean_object* v___y_4027_){
_start:
{
uint8_t v_closed_boxed_4028_; lean_object* v_res_4029_; 
v_closed_boxed_4028_ = lean_unbox(v_closed_4024_);
v_res_4029_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_4018_, v_capacity_4019_, v_buf_4020_, v_bufCount_4021_, v_sendIdx_4022_, v_recvIdx_4023_, v_closed_boxed_4028_, v___y_4025_, v_x_4026_);
lean_dec(v___y_4025_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_4030_, lean_object* v_x_4031_, lean_object* v_head_4032_, lean_object* v_x_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_4030_, v_x_4031_, v_head_4032_, v_x_4033_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_4036_, lean_object* v_x_4037_){
_start:
{
if (lean_obj_tag(v_x_4036_) == 0)
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4039_, 0, v_x_4037_);
v___x_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4039_);
return v___x_4040_;
}
else
{
lean_object* v_head_4041_; lean_object* v_tail_4042_; lean_object* v_waiter_4043_; lean_object* v___f_4044_; lean_object* v_val_4046_; 
v_head_4041_ = lean_ctor_get(v_x_4036_, 0);
lean_inc(v_head_4041_);
v_tail_4042_ = lean_ctor_get(v_x_4036_, 1);
lean_inc(v_tail_4042_);
lean_dec_ref_known(v_x_4036_, 2);
v_waiter_4043_ = lean_ctor_get(v_head_4041_, 1);
lean_inc(v_waiter_4043_);
v___f_4044_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4044_, 0, v_tail_4042_);
lean_closure_set(v___f_4044_, 1, v_x_4037_);
lean_closure_set(v___f_4044_, 2, v_head_4041_);
if (lean_obj_tag(v_waiter_4043_) == 0)
{
lean_object* v___x_4050_; 
v___x_4050_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_4046_ = v___x_4050_;
goto v___jp_4045_;
}
else
{
lean_object* v_val_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4065_; 
v_val_4051_ = lean_ctor_get(v_waiter_4043_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_waiter_4043_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4053_ = v_waiter_4043_;
v_isShared_4054_ = v_isSharedCheck_4065_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_val_4051_);
lean_dec(v_waiter_4043_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4065_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v_finished_4055_; lean_object* v___x_4056_; lean_object* v___f_4057_; lean_object* v___x_4059_; 
v_finished_4055_ = lean_ctor_get(v_val_4051_, 0);
lean_inc(v_finished_4055_);
lean_dec(v_val_4051_);
v___x_4056_ = lean_st_ref_get(v_finished_4055_);
lean_dec(v_finished_4055_);
v___f_4057_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4056_);
v___x_4059_ = v___x_4053_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4056_);
v___x_4059_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; 
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
v___x_4061_ = lean_unsigned_to_nat(0u);
v___x_4062_ = 0;
v___x_4063_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4061_, v___x_4062_, v___x_4060_, v___f_4057_);
v_val_4046_ = v___x_4063_;
goto v___jp_4045_;
}
}
}
v___jp_4045_:
{
lean_object* v___x_4047_; uint8_t v___x_4048_; lean_object* v___x_4049_; 
v___x_4047_ = lean_unsigned_to_nat(0u);
v___x_4048_ = 0;
v___x_4049_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4047_, v___x_4048_, v_val_4046_, v___f_4044_);
return v___x_4049_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_4066_, lean_object* v_x_4067_, lean_object* v_head_4068_, lean_object* v_x_4069_){
_start:
{
if (lean_obj_tag(v_x_4069_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4079_; 
lean_dec_ref(v_head_4068_);
lean_dec(v_x_4067_);
lean_dec(v_tail_4066_);
v_a_4071_ = lean_ctor_get(v_x_4069_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_x_4069_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4073_ = v_x_4069_;
v_isShared_4074_ = v_isSharedCheck_4079_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v_x_4069_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4079_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
}
}
else
{
lean_object* v_a_4080_; uint8_t v___x_4081_; 
v_a_4080_ = lean_ctor_get(v_x_4069_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v_x_4069_, 1);
v___x_4081_ = lean_unbox(v_a_4080_);
lean_dec(v_a_4080_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; 
lean_dec_ref(v_head_4068_);
v___x_4082_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4066_, v_x_4067_);
return v___x_4082_;
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4083_, 0, v_head_4068_);
lean_ctor_set(v___x_4083_, 1, v_x_4067_);
v___x_4084_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4066_, v___x_4083_);
return v___x_4084_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_4085_, lean_object* v_x_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4085_, v_x_4086_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_4089_){
_start:
{
if (lean_obj_tag(v_x_4089_) == 0)
{
lean_object* v___x_4091_; 
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v_x_4089_);
return v___x_4091_;
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4101_; 
v_a_4092_ = lean_ctor_get(v_x_4089_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_x_4089_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4094_ = v_x_4089_;
v_isShared_4095_ = v_isSharedCheck_4101_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v_x_4089_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4101_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4096_; lean_object* v___x_4098_; 
v___x_4096_ = l_List_reverse___redArg(v_a_4092_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 0, v___x_4096_);
v___x_4098_ = v___x_4094_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4096_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4102_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4105_, lean_object* v___x_4106_, lean_object* v_x_4107_){
_start:
{
if (lean_obj_tag(v_x_4107_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4117_; 
lean_dec(v___x_4106_);
lean_dec(v_a_4105_);
v_a_4109_ = lean_ctor_get(v_x_4107_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v_x_4107_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4111_ = v_x_4107_;
v_isShared_4112_ = v_isSharedCheck_4117_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v_x_4107_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4117_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; 
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
return v___x_4115_;
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4134_; 
v_a_4118_ = lean_ctor_get(v_x_4107_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_x_4107_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4120_ = v_x_4107_;
v_isShared_4121_ = v_isSharedCheck_4134_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v_x_4107_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4134_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
uint8_t v___x_4122_; 
v___x_4122_ = l_List_isEmpty___redArg(v_a_4105_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; lean_object* v___x_4125_; 
lean_dec(v___x_4106_);
v___x_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4123_, 0, v_a_4118_);
lean_ctor_set(v___x_4123_, 1, v_a_4105_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v___x_4123_);
v___x_4125_ = v___x_4120_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
return v___x_4126_;
}
}
else
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; 
lean_dec(v_a_4105_);
v___x_4128_ = l_List_reverse___redArg(v_a_4118_);
v___x_4129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4106_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v___x_4129_);
v___x_4131_ = v___x_4120_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4129_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4135_, lean_object* v___x_4136_, lean_object* v_x_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4135_, v___x_4136_, v_x_4137_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_eList_4140_, lean_object* v___x_4141_, lean_object* v___f_4142_, lean_object* v_x_4143_){
_start:
{
if (lean_obj_tag(v_x_4143_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4153_; 
lean_dec_ref(v___f_4142_);
lean_dec(v___x_4141_);
lean_dec(v_eList_4140_);
v_a_4145_ = lean_ctor_get(v_x_4143_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v_x_4143_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4147_ = v_x_4143_;
v_isShared_4148_ = v_isSharedCheck_4153_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v_x_4143_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4153_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
lean_object* v___x_4151_; 
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
return v___x_4151_;
}
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; lean_object* v___f_4159_; lean_object* v___x_4160_; 
v_a_4154_ = lean_ctor_get(v_x_4143_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v_x_4143_, 1);
lean_inc(v___x_4141_);
v___x_4155_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4140_, v___x_4141_);
v___x_4156_ = lean_unsigned_to_nat(0u);
v___x_4157_ = 0;
v___x_4158_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4156_, v___x_4157_, v___x_4155_, v___f_4142_);
v___f_4159_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4159_, 0, v_a_4154_);
lean_closure_set(v___f_4159_, 1, v___x_4141_);
v___x_4160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4156_, v___x_4157_, v___x_4158_, v___f_4159_);
return v___x_4160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_eList_4161_, lean_object* v___x_4162_, lean_object* v___f_4163_, lean_object* v_x_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v_eList_4161_, v___x_4162_, v___f_4163_, v_x_4164_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v_eList_4171_; lean_object* v_dList_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___f_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; lean_object* v___x_4178_; lean_object* v___f_4179_; lean_object* v___x_4180_; 
v_eList_4171_ = lean_ctor_get(v_q_4168_, 0);
lean_inc(v_eList_4171_);
v_dList_4172_ = lean_ctor_get(v_q_4168_, 1);
lean_inc(v_dList_4172_);
lean_dec_ref(v_q_4168_);
v___x_4173_ = lean_box(0);
v___x_4174_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4172_, v___x_4173_);
v___f_4175_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4176_ = lean_unsigned_to_nat(0u);
v___x_4177_ = 0;
v___x_4178_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4176_, v___x_4177_, v___x_4174_, v___f_4175_);
v___f_4179_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4179_, 0, v_eList_4171_);
lean_closure_set(v___f_4179_, 1, v___x_4173_);
lean_closure_set(v___f_4179_, 2, v___f_4175_);
v___x_4180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4176_, v___x_4177_, v___x_4178_, v___f_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4181_, v___y_4182_);
lean_dec(v___y_4182_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4185_, lean_object* v_x_4186_){
_start:
{
if (lean_obj_tag(v_x_4186_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4196_; 
v_a_4188_ = lean_ctor_get(v_x_4186_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v_x_4186_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4190_ = v_x_4186_;
v_isShared_4191_ = v_isSharedCheck_4196_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v_x_4186_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4196_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4194_; 
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
}
}
else
{
lean_object* v_a_4197_; lean_object* v_producers_4198_; lean_object* v_consumers_4199_; lean_object* v_capacity_4200_; lean_object* v_buf_4201_; lean_object* v_bufCount_4202_; lean_object* v_sendIdx_4203_; lean_object* v_recvIdx_4204_; uint8_t v_closed_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___f_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; lean_object* v___x_4211_; 
v_a_4197_ = lean_ctor_get(v_x_4186_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v_x_4186_, 1);
v_producers_4198_ = lean_ctor_get(v_a_4197_, 0);
lean_inc_ref(v_producers_4198_);
v_consumers_4199_ = lean_ctor_get(v_a_4197_, 1);
lean_inc_ref(v_consumers_4199_);
v_capacity_4200_ = lean_ctor_get(v_a_4197_, 2);
lean_inc(v_capacity_4200_);
v_buf_4201_ = lean_ctor_get(v_a_4197_, 3);
lean_inc_ref(v_buf_4201_);
v_bufCount_4202_ = lean_ctor_get(v_a_4197_, 4);
lean_inc(v_bufCount_4202_);
v_sendIdx_4203_ = lean_ctor_get(v_a_4197_, 5);
lean_inc(v_sendIdx_4203_);
v_recvIdx_4204_ = lean_ctor_get(v_a_4197_, 6);
lean_inc(v_recvIdx_4204_);
v_closed_4205_ = lean_ctor_get_uint8(v_a_4197_, sizeof(void*)*7);
lean_dec(v_a_4197_);
v___x_4206_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4199_, v___y_4185_);
v___x_4207_ = lean_box(v_closed_4205_);
lean_inc(v___y_4185_);
v___f_4208_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4208_, 0, v_producers_4198_);
lean_closure_set(v___f_4208_, 1, v_capacity_4200_);
lean_closure_set(v___f_4208_, 2, v_buf_4201_);
lean_closure_set(v___f_4208_, 3, v_bufCount_4202_);
lean_closure_set(v___f_4208_, 4, v_sendIdx_4203_);
lean_closure_set(v___f_4208_, 5, v_recvIdx_4204_);
lean_closure_set(v___f_4208_, 6, v___x_4207_);
lean_closure_set(v___f_4208_, 7, v___y_4185_);
v___x_4209_ = lean_unsigned_to_nat(0u);
v___x_4210_ = 0;
v___x_4211_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4209_, v___x_4210_, v___x_4206_, v___f_4208_);
return v___x_4211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4212_, lean_object* v_x_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4212_, v_x_4213_);
lean_dec(v___y_4212_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4216_){
_start:
{
lean_object* v___x_4218_; lean_object* v___f_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; uint8_t v___x_4223_; lean_object* v___x_4224_; 
v___x_4218_ = lean_st_ref_get(v___y_4216_);
lean_inc(v___y_4216_);
v___f_4219_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4219_, 0, v___y_4216_);
v___x_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4218_);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
v___x_4222_ = lean_unsigned_to_nat(0u);
v___x_4223_ = 0;
v___x_4224_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4222_, v___x_4223_, v___x_4221_, v___f_4219_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4225_);
lean_dec(v___y_4225_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4233_){
_start:
{
lean_object* v___f_4234_; lean_object* v___f_4235_; lean_object* v___f_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
lean_inc_ref_n(v_ch_4233_, 2);
v___f_4234_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4234_, 0, v_ch_4233_);
v___f_4235_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___f_4236_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2));
v___x_4237_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4237_, 0, lean_box(0));
lean_closure_set(v___x_4237_, 1, lean_box(0));
lean_closure_set(v___x_4237_, 2, v_ch_4233_);
lean_closure_set(v___x_4237_, 3, v___f_4235_);
v___x_4238_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4238_, 0, lean_box(0));
lean_closure_set(v___x_4238_, 1, lean_box(0));
lean_closure_set(v___x_4238_, 2, v_ch_4233_);
lean_closure_set(v___x_4238_, 3, v___f_4236_);
v___x_4239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set(v___x_4239_, 1, v___f_4234_);
lean_ctor_set(v___x_4239_, 2, v___x_4238_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4240_, lean_object* v_ch_4241_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4243_, lean_object* v_q_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4244_, v___y_4245_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4248_, lean_object* v_q_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4248_, v_q_4249_, v___y_4250_);
lean_dec(v___y_4250_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4253_, lean_object* v_x_4254_, lean_object* v_x_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4254_, v_x_4255_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4259_, lean_object* v_x_4260_, lean_object* v_x_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4259_, v_x_4260_, v_x_4261_, v___y_4262_);
lean_dec(v___y_4262_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg(lean_object* v_x_4265_){
_start:
{
switch(lean_obj_tag(v_x_4265_))
{
case 0:
{
lean_object* v___x_4266_; 
v___x_4266_ = lean_unsigned_to_nat(0u);
return v___x_4266_;
}
case 1:
{
lean_object* v___x_4267_; 
v___x_4267_ = lean_unsigned_to_nat(1u);
return v___x_4267_;
}
default: 
{
lean_object* v___x_4268_; 
v___x_4268_ = lean_unsigned_to_nat(2u);
return v___x_4268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(lean_object* v_x_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4269_);
lean_dec_ref(v_x_4269_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx(lean_object* v_00_u03b1_4271_, lean_object* v_x_4272_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___boxed(lean_object* v_00_u03b1_4274_, lean_object* v_x_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Std_CloseableChannel_Flavors_ctorIdx(v_00_u03b1_4274_, v_x_4275_);
lean_dec_ref(v_x_4275_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4277_, lean_object* v_k_4278_){
_start:
{
lean_object* v_ch_4279_; lean_object* v___x_4280_; 
v_ch_4279_ = lean_ctor_get(v_t_4277_, 0);
lean_inc_ref(v_ch_4279_);
lean_dec_ref(v_t_4277_);
v___x_4280_ = lean_apply_1(v_k_4278_, v_ch_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4281_, lean_object* v_motive_4282_, lean_object* v_ctorIdx_4283_, lean_object* v_t_4284_, lean_object* v_h_4285_, lean_object* v_k_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4284_, v_k_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4288_, lean_object* v_motive_4289_, lean_object* v_ctorIdx_4290_, lean_object* v_t_4291_, lean_object* v_h_4292_, lean_object* v_k_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4288_, v_motive_4289_, v_ctorIdx_4290_, v_t_4291_, v_h_4292_, v_k_4293_);
lean_dec(v_ctorIdx_4290_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4295_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4296_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4295_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4298_, lean_object* v_motive_4299_, lean_object* v_t_4300_, lean_object* v_h_4301_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4302_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4300_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4302_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4304_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4305_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4304_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4307_, lean_object* v_motive_4308_, lean_object* v_t_4309_, lean_object* v_h_4310_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4311_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4309_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4311_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4313_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4313_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4316_, lean_object* v_motive_4317_, lean_object* v_t_4318_, lean_object* v_h_4319_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4320_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4318_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4322_){
_start:
{
if (lean_obj_tag(v_capacity_4322_) == 0)
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
return v___x_4325_;
}
else
{
lean_object* v_val_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4343_; 
v_val_4326_ = lean_ctor_get(v_capacity_4322_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v_capacity_4322_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4328_ = v_capacity_4322_;
v_isShared_4329_ = v_isSharedCheck_4343_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_val_4326_);
lean_dec(v_capacity_4322_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4343_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v_zero_4330_; uint8_t v_isZero_4331_; 
v_zero_4330_ = lean_unsigned_to_nat(0u);
v_isZero_4331_ = lean_nat_dec_eq(v_val_4326_, v_zero_4330_);
if (v_isZero_4331_ == 1)
{
lean_object* v___x_4332_; lean_object* v___x_4334_; 
lean_dec(v_val_4326_);
v___x_4332_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4332_);
v___x_4334_ = v___x_4328_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
else
{
lean_object* v_one_4336_; lean_object* v_n_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4341_; 
v_one_4336_ = lean_unsigned_to_nat(1u);
v_n_4337_ = lean_nat_sub(v_val_4326_, v_one_4336_);
lean_dec(v_val_4326_);
v___x_4338_ = lean_nat_add(v_n_4337_, v_one_4336_);
lean_dec(v_n_4337_);
v___x_4339_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4338_);
if (v_isShared_4329_ == 0)
{
lean_ctor_set_tag(v___x_4328_, 2);
lean_ctor_set(v___x_4328_, 0, v___x_4339_);
v___x_4341_ = v___x_4328_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4339_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Std_CloseableChannel_new___redArg(v_capacity_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4347_, lean_object* v_capacity_4348_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = l_Std_CloseableChannel_new___redArg(v_capacity_4348_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4351_, lean_object* v_capacity_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Std_CloseableChannel_new(v_00_u03b1_4351_, v_capacity_4352_);
return v_res_4354_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4355_, lean_object* v_v_4356_){
_start:
{
switch(lean_obj_tag(v_ch_4355_))
{
case 0:
{
lean_object* v_ch_4358_; uint8_t v___x_4359_; 
v_ch_4358_ = lean_ctor_get(v_ch_4355_, 0);
lean_inc_ref(v_ch_4358_);
lean_dec_ref_known(v_ch_4355_, 1);
v___x_4359_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4358_, v_v_4356_);
return v___x_4359_;
}
case 1:
{
lean_object* v_ch_4360_; uint8_t v___x_4361_; 
v_ch_4360_ = lean_ctor_get(v_ch_4355_, 0);
lean_inc_ref(v_ch_4360_);
lean_dec_ref_known(v_ch_4355_, 1);
v___x_4361_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4360_, v_v_4356_);
return v___x_4361_;
}
default: 
{
lean_object* v_ch_4362_; uint8_t v___x_4363_; 
v_ch_4362_ = lean_ctor_get(v_ch_4355_, 0);
lean_inc_ref(v_ch_4362_);
lean_dec_ref_known(v_ch_4355_, 1);
v___x_4363_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4362_, v_v_4356_);
return v___x_4363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4364_, lean_object* v_v_4365_, lean_object* v_a_4366_){
_start:
{
uint8_t v_res_4367_; lean_object* v_r_4368_; 
v_res_4367_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4364_, v_v_4365_);
v_r_4368_ = lean_box(v_res_4367_);
return v_r_4368_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4369_, lean_object* v_ch_4370_, lean_object* v_v_4371_){
_start:
{
uint8_t v___x_4373_; 
v___x_4373_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4370_, v_v_4371_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4374_, lean_object* v_ch_4375_, lean_object* v_v_4376_, lean_object* v_a_4377_){
_start:
{
uint8_t v_res_4378_; lean_object* v_r_4379_; 
v_res_4378_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4374_, v_ch_4375_, v_v_4376_);
v_r_4379_ = lean_box(v_res_4378_);
return v_r_4379_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4380_, lean_object* v_v_4381_){
_start:
{
switch(lean_obj_tag(v_ch_4380_))
{
case 0:
{
lean_object* v_ch_4383_; lean_object* v___x_4384_; 
v_ch_4383_ = lean_ctor_get(v_ch_4380_, 0);
lean_inc_ref(v_ch_4383_);
lean_dec_ref_known(v_ch_4380_, 1);
v___x_4384_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4383_, v_v_4381_);
return v___x_4384_;
}
case 1:
{
lean_object* v_ch_4385_; lean_object* v___x_4386_; 
v_ch_4385_ = lean_ctor_get(v_ch_4380_, 0);
lean_inc_ref(v_ch_4385_);
lean_dec_ref_known(v_ch_4380_, 1);
v___x_4386_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4385_, v_v_4381_);
return v___x_4386_;
}
default: 
{
lean_object* v_ch_4387_; lean_object* v___x_4388_; 
v_ch_4387_ = lean_ctor_get(v_ch_4380_, 0);
lean_inc_ref(v_ch_4387_);
lean_dec_ref_known(v_ch_4380_, 1);
v___x_4388_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4387_, v_v_4381_);
return v___x_4388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4389_, lean_object* v_v_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Std_CloseableChannel_send___redArg(v_ch_4389_, v_v_4390_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4393_, lean_object* v_ch_4394_, lean_object* v_v_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Std_CloseableChannel_send___redArg(v_ch_4394_, v_v_4395_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4398_, lean_object* v_ch_4399_, lean_object* v_v_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Std_CloseableChannel_send(v_00_u03b1_4398_, v_ch_4399_, v_v_4400_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4403_){
_start:
{
switch(lean_obj_tag(v_ch_4403_))
{
case 0:
{
lean_object* v_ch_4405_; lean_object* v___x_4406_; 
v_ch_4405_ = lean_ctor_get(v_ch_4403_, 0);
lean_inc_ref(v_ch_4405_);
lean_dec_ref_known(v_ch_4403_, 1);
v___x_4406_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4405_);
return v___x_4406_;
}
case 1:
{
lean_object* v_ch_4407_; lean_object* v___x_4408_; 
v_ch_4407_ = lean_ctor_get(v_ch_4403_, 0);
lean_inc_ref(v_ch_4407_);
lean_dec_ref_known(v_ch_4403_, 1);
v___x_4408_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4407_);
return v___x_4408_;
}
default: 
{
lean_object* v_ch_4409_; lean_object* v___x_4410_; 
v_ch_4409_ = lean_ctor_get(v_ch_4403_, 0);
lean_inc_ref(v_ch_4409_);
lean_dec_ref_known(v_ch_4403_, 1);
v___x_4410_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4409_);
return v___x_4410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Std_CloseableChannel_close___redArg(v_ch_4411_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4414_, lean_object* v_ch_4415_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l_Std_CloseableChannel_close___redArg(v_ch_4415_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4418_, lean_object* v_ch_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Std_CloseableChannel_close(v_00_u03b1_4418_, v_ch_4419_);
return v_res_4421_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4422_){
_start:
{
switch(lean_obj_tag(v_ch_4422_))
{
case 0:
{
lean_object* v_ch_4424_; uint8_t v___x_4425_; 
v_ch_4424_ = lean_ctor_get(v_ch_4422_, 0);
lean_inc_ref(v_ch_4424_);
lean_dec_ref_known(v_ch_4422_, 1);
v___x_4425_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4424_);
return v___x_4425_;
}
case 1:
{
lean_object* v_ch_4426_; uint8_t v___x_4427_; 
v_ch_4426_ = lean_ctor_get(v_ch_4422_, 0);
lean_inc_ref(v_ch_4426_);
lean_dec_ref_known(v_ch_4422_, 1);
v___x_4427_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4426_);
return v___x_4427_;
}
default: 
{
lean_object* v_ch_4428_; uint8_t v___x_4429_; 
v_ch_4428_ = lean_ctor_get(v_ch_4422_, 0);
lean_inc_ref(v_ch_4428_);
lean_dec_ref_known(v_ch_4422_, 1);
v___x_4429_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4428_);
return v___x_4429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4430_, lean_object* v_a_4431_){
_start:
{
uint8_t v_res_4432_; lean_object* v_r_4433_; 
v_res_4432_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4430_);
v_r_4433_ = lean_box(v_res_4432_);
return v_r_4433_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4434_, lean_object* v_ch_4435_){
_start:
{
uint8_t v___x_4437_; 
v___x_4437_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4435_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4438_, lean_object* v_ch_4439_, lean_object* v_a_4440_){
_start:
{
uint8_t v_res_4441_; lean_object* v_r_4442_; 
v_res_4441_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4438_, v_ch_4439_);
v_r_4442_ = lean_box(v_res_4441_);
return v_r_4442_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4443_){
_start:
{
switch(lean_obj_tag(v_ch_4443_))
{
case 0:
{
lean_object* v_ch_4445_; lean_object* v___x_4446_; 
v_ch_4445_ = lean_ctor_get(v_ch_4443_, 0);
lean_inc_ref(v_ch_4445_);
lean_dec_ref_known(v_ch_4443_, 1);
v___x_4446_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4445_);
return v___x_4446_;
}
case 1:
{
lean_object* v_ch_4447_; lean_object* v___x_4448_; 
v_ch_4447_ = lean_ctor_get(v_ch_4443_, 0);
lean_inc_ref(v_ch_4447_);
lean_dec_ref_known(v_ch_4443_, 1);
v___x_4448_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4447_);
return v___x_4448_;
}
default: 
{
lean_object* v_ch_4449_; lean_object* v___x_4450_; 
v_ch_4449_ = lean_ctor_get(v_ch_4443_, 0);
lean_inc_ref(v_ch_4449_);
lean_dec_ref_known(v_ch_4443_, 1);
v___x_4450_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4449_);
return v___x_4450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4451_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4454_, lean_object* v_ch_4455_){
_start:
{
lean_object* v___x_4457_; 
v___x_4457_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4455_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4458_, lean_object* v_ch_4459_, lean_object* v_a_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4458_, v_ch_4459_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4462_){
_start:
{
switch(lean_obj_tag(v_ch_4462_))
{
case 0:
{
lean_object* v_ch_4464_; lean_object* v___x_4465_; 
v_ch_4464_ = lean_ctor_get(v_ch_4462_, 0);
lean_inc_ref(v_ch_4464_);
lean_dec_ref_known(v_ch_4462_, 1);
v___x_4465_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4464_);
return v___x_4465_;
}
case 1:
{
lean_object* v_ch_4466_; lean_object* v___x_4467_; 
v_ch_4466_ = lean_ctor_get(v_ch_4462_, 0);
lean_inc_ref(v_ch_4466_);
lean_dec_ref_known(v_ch_4462_, 1);
v___x_4467_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4466_);
return v___x_4467_;
}
default: 
{
lean_object* v_ch_4468_; lean_object* v___x_4469_; 
v_ch_4468_ = lean_ctor_get(v_ch_4462_, 0);
lean_inc_ref(v_ch_4468_);
lean_dec_ref_known(v_ch_4462_, 1);
v___x_4469_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4468_);
return v___x_4469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Std_CloseableChannel_recv___redArg(v_ch_4470_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4473_, lean_object* v_ch_4474_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_Std_CloseableChannel_recv___redArg(v_ch_4474_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4477_, lean_object* v_ch_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Std_CloseableChannel_recv(v_00_u03b1_4477_, v_ch_4478_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4481_){
_start:
{
switch(lean_obj_tag(v_ch_4481_))
{
case 0:
{
lean_object* v_ch_4482_; lean_object* v___x_4483_; 
v_ch_4482_ = lean_ctor_get(v_ch_4481_, 0);
lean_inc_ref(v_ch_4482_);
lean_dec_ref_known(v_ch_4481_, 1);
v___x_4483_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4482_);
return v___x_4483_;
}
case 1:
{
lean_object* v_ch_4484_; lean_object* v___x_4485_; 
v_ch_4484_ = lean_ctor_get(v_ch_4481_, 0);
lean_inc_ref(v_ch_4484_);
lean_dec_ref_known(v_ch_4481_, 1);
v___x_4485_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4484_);
return v___x_4485_;
}
default: 
{
lean_object* v_ch_4486_; lean_object* v___x_4487_; 
v_ch_4486_ = lean_ctor_get(v_ch_4481_, 0);
lean_inc_ref(v_ch_4486_);
lean_dec_ref_known(v_ch_4481_, 1);
v___x_4487_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4486_);
return v___x_4487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4488_, lean_object* v_ch_4489_){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4489_);
return v___x_4490_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4491_ = lean_box(0);
v___x_4492_ = lean_task_pure(v___x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4493_, lean_object* v_ch_4494_, lean_object* v_prio_4495_, lean_object* v_x_4496_){
_start:
{
if (lean_obj_tag(v_x_4496_) == 0)
{
lean_object* v___x_4498_; 
lean_dec(v_prio_4495_);
lean_dec_ref(v_ch_4494_);
lean_dec_ref(v_f_4493_);
v___x_4498_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4498_;
}
else
{
lean_object* v_val_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_val_4499_ = lean_ctor_get(v_x_4496_, 0);
lean_inc(v_val_4499_);
lean_dec_ref_known(v_x_4496_, 1);
lean_inc_ref(v_f_4493_);
v___x_4500_ = lean_apply_2(v_f_4493_, v_val_4499_, lean_box(0));
v___x_4501_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4493_, v_ch_4494_, v_prio_4495_);
return v___x_4501_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4502_, lean_object* v_ch_4503_, lean_object* v_prio_4504_, lean_object* v_x_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4502_, v_ch_4503_, v_prio_4504_, v_x_4505_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4508_, lean_object* v_ch_4509_, lean_object* v_prio_4510_){
_start:
{
lean_object* v___x_4512_; lean_object* v___f_4513_; uint8_t v___x_4514_; lean_object* v___x_4515_; 
lean_inc_ref(v_ch_4509_);
v___x_4512_ = l_Std_CloseableChannel_recv___redArg(v_ch_4509_);
lean_inc(v_prio_4510_);
v___f_4513_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4513_, 0, v_f_4508_);
lean_closure_set(v___f_4513_, 1, v_ch_4509_);
lean_closure_set(v___f_4513_, 2, v_prio_4510_);
v___x_4514_ = 0;
v___x_4515_ = lean_io_bind_task(v___x_4512_, v___f_4513_, v_prio_4510_, v___x_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4516_, lean_object* v_ch_4517_, lean_object* v_prio_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4516_, v_ch_4517_, v_prio_4518_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4521_, lean_object* v_f_4522_, lean_object* v_ch_4523_, lean_object* v_prio_4524_){
_start:
{
lean_object* v___x_4526_; 
v___x_4526_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4522_, v_ch_4523_, v_prio_4524_);
return v___x_4526_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4527_, lean_object* v_f_4528_, lean_object* v_ch_4529_, lean_object* v_prio_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4527_, v_f_4528_, v_ch_4529_, v_prio_4530_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(lean_object* v_x_4533_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = lean_box(0);
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed(lean_object* v_x_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(v_x_4537_);
lean_dec_ref(v_x_4537_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4545_, lean_object* v_inst_4546_){
_start:
{
lean_object* v___x_4547_; 
v___x_4547_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4548_, lean_object* v_inst_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4548_, v_inst_4549_);
lean_dec(v_inst_4549_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_4551_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4552_, 0, v_a_4551_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_4553_, lean_object* v_x_4554_){
_start:
{
if (lean_obj_tag(v_x_4554_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4564_; 
lean_dec_ref(v___f_4553_);
v_a_4556_ = lean_ctor_get(v_x_4554_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v_x_4554_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4558_ = v_x_4554_;
v_isShared_4559_ = v_isSharedCheck_4564_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v_x_4554_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4564_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4562_; 
v___x_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
return v___x_4562_;
}
}
}
else
{
lean_object* v_a_4565_; 
v_a_4565_ = lean_ctor_get(v_x_4554_, 0);
lean_inc(v_a_4565_);
lean_dec_ref_known(v_x_4554_, 1);
if (lean_obj_tag(v_a_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4574_; 
lean_dec_ref(v___f_4553_);
v_a_4566_ = lean_ctor_get(v_a_4565_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v_a_4565_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4568_ = v_a_4565_;
v_isShared_4569_ = v_isSharedCheck_4574_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v_a_4565_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4574_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
lean_object* v___x_4572_; 
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
return v___x_4572_;
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4576_; uint8_t v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v_a_4575_ = lean_ctor_get(v_a_4565_, 0);
lean_inc(v_a_4575_);
lean_dec_ref_known(v_a_4565_, 1);
v___x_4576_ = lean_unsigned_to_nat(0u);
v___x_4577_ = 0;
v___x_4578_ = lean_task_map(v___f_4553_, v_a_4575_, v___x_4576_, v___x_4577_);
v___x_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
return v___x_4579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_4580_, lean_object* v_x_4581_, lean_object* v___y_4582_){
_start:
{
lean_object* v_res_4583_; 
v_res_4583_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(v___f_4580_, v_x_4581_);
return v_res_4583_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_4584_, lean_object* v_receiver_4585_){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; uint8_t v___x_4592_; lean_object* v___x_4593_; 
v___x_4587_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4585_);
v___x_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
v___x_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
v___x_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
v___x_4591_ = lean_unsigned_to_nat(0u);
v___x_4592_ = 0;
v___x_4593_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4591_, v___x_4592_, v___x_4590_, v___f_4584_);
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_4594_, lean_object* v_receiver_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(v___f_4594_, v_receiver_4595_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4603_, lean_object* v_inst_4604_){
_start:
{
lean_object* v___f_4605_; 
v___f_4605_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2));
return v___f_4605_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4606_, lean_object* v_inst_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4606_, v_inst_4607_);
lean_dec(v_inst_4607_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_4610_, lean_object* v_x_4611_){
_start:
{
if (lean_obj_tag(v_x_4611_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4621_; 
lean_dec_ref(v___f_4610_);
v_a_4613_ = lean_ctor_get(v_x_4611_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v_x_4611_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4615_ = v_x_4611_;
v_isShared_4616_ = v_isSharedCheck_4621_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v_x_4611_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4621_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; 
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
return v___x_4619_;
}
}
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; uint8_t v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v_a_4622_ = lean_ctor_get(v_x_4611_, 0);
lean_inc(v_a_4622_);
lean_dec_ref_known(v_x_4611_, 1);
v___x_4623_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0));
v___x_4624_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4624_, 0, lean_box(0));
lean_closure_set(v___x_4624_, 1, lean_box(0));
lean_closure_set(v___x_4624_, 2, lean_box(0));
lean_closure_set(v___x_4624_, 3, v___x_4623_);
lean_closure_set(v___x_4624_, 4, v___f_4610_);
v___x_4625_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4625_, 0, lean_box(0));
lean_closure_set(v___x_4625_, 1, lean_box(0));
lean_closure_set(v___x_4625_, 2, lean_box(0));
lean_closure_set(v___x_4625_, 3, v___x_4624_);
v___x_4626_ = lean_unsigned_to_nat(0u);
v___x_4627_ = 0;
v___x_4628_ = lean_task_map(v___x_4625_, v_a_4622_, v___x_4626_, v___x_4627_);
v___x_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4628_);
return v___x_4629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_4630_, lean_object* v_x_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(v___f_4630_, v_x_4631_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_4634_, lean_object* v_receiver_4635_, lean_object* v_x_4636_){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; uint8_t v___x_4642_; lean_object* v___x_4643_; 
v___x_4638_ = l_Std_CloseableChannel_send___redArg(v_receiver_4635_, v_x_4636_);
v___x_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4638_);
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
v___x_4641_ = lean_unsigned_to_nat(0u);
v___x_4642_ = 0;
v___x_4643_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4641_, v___x_4642_, v___x_4640_, v___f_4634_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_4644_, lean_object* v_receiver_4645_, lean_object* v_x_4646_, lean_object* v___y_4647_){
_start:
{
lean_object* v_res_4648_; 
v_res_4648_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(v___f_4644_, v_receiver_4645_, v_x_4646_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(lean_object* v_x_4649_){
_start:
{
lean_object* v___x_4651_; 
v___x_4651_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v_x_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(v_x_4652_);
lean_dec_ref(v_x_4652_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(lean_object* v___f_4655_, lean_object* v_socket_4656_, lean_object* v_x_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v___x_4660_; 
v___x_4660_ = lean_apply_3(v___f_4655_, v_socket_4656_, v___y_4658_, lean_box(0));
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v___f_4661_, lean_object* v_socket_4662_, lean_object* v_x_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(v___f_4661_, v_socket_4662_, v_x_4663_, v___y_4664_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_4667_, lean_object* v___x_4668_, lean_object* v_socket_4669_, lean_object* v_data_4670_){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; 
v___x_4672_ = lean_unsigned_to_nat(0u);
v___x_4673_ = lean_array_get_size(v_data_4670_);
v___x_4674_ = lean_box(0);
v___x_4675_ = lean_nat_dec_lt(v___x_4672_, v___x_4673_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4676_; 
lean_dec_ref(v_data_4670_);
lean_dec_ref(v_socket_4669_);
lean_dec_ref(v___x_4668_);
lean_dec_ref(v___f_4667_);
v___x_4676_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4676_;
}
else
{
lean_object* v___f_4677_; uint8_t v___x_4678_; 
v___f_4677_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4677_, 0, v___f_4667_);
lean_closure_set(v___f_4677_, 1, v_socket_4669_);
v___x_4678_ = lean_nat_dec_le(v___x_4673_, v___x_4673_);
if (v___x_4678_ == 0)
{
if (v___x_4675_ == 0)
{
lean_object* v___x_4679_; 
lean_dec_ref(v___f_4677_);
lean_dec_ref(v_data_4670_);
lean_dec_ref(v___x_4668_);
v___x_4679_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4679_;
}
else
{
size_t v___x_4680_; size_t v___x_4681_; lean_object* v___x_753__overap_4682_; lean_object* v___x_4683_; 
v___x_4680_ = ((size_t)0ULL);
v___x_4681_ = lean_usize_of_nat(v___x_4673_);
v___x_753__overap_4682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4668_, v___f_4677_, v_data_4670_, v___x_4680_, v___x_4681_, v___x_4674_);
v___x_4683_ = lean_apply_1(v___x_753__overap_4682_, lean_box(0));
return v___x_4683_;
}
}
else
{
size_t v___x_4684_; size_t v___x_4685_; lean_object* v___x_756__overap_4686_; lean_object* v___x_4687_; 
v___x_4684_ = ((size_t)0ULL);
v___x_4685_ = lean_usize_of_nat(v___x_4673_);
v___x_756__overap_4686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4668_, v___f_4677_, v_data_4670_, v___x_4684_, v___x_4685_, v___x_4674_);
v___x_4687_ = lean_apply_1(v___x_756__overap_4686_, lean_box(0));
return v___x_4687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_4688_, lean_object* v___x_4689_, lean_object* v_socket_4690_, lean_object* v_data_4691_, lean_object* v___y_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(v___f_4688_, v___x_4689_, v_socket_4690_, v_data_4691_);
return v_res_4693_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_4699_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_4700_; lean_object* v___f_4701_; lean_object* v___f_4702_; 
v___x_4700_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_4701_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___f_4702_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4702_, 0, v___f_4701_);
lean_closure_set(v___f_4702_, 1, v___x_4700_);
return v___f_4702_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___f_4703_; lean_object* v___f_4704_; lean_object* v___f_4705_; lean_object* v___x_4706_; 
v___f_4703_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_4704_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4);
v___f_4705_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___x_4706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4706_, 0, v___f_4705_);
lean_ctor_set(v___x_4706_, 1, v___f_4704_);
lean_ctor_set(v___x_4706_, 2, v___f_4703_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4707_, lean_object* v_inst_4708_){
_start:
{
lean_object* v___x_4709_; 
v___x_4709_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4710_, lean_object* v_inst_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4710_, v_inst_4711_);
lean_dec(v_inst_4711_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4713_){
_start:
{
lean_inc_ref(v_ch_4713_);
return v_ch_4713_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l_Std_CloseableChannel_sync___redArg(v_ch_4714_);
lean_dec_ref(v_ch_4714_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4716_, lean_object* v_ch_4717_){
_start:
{
lean_inc_ref(v_ch_4717_);
return v_ch_4717_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4718_, lean_object* v_ch_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l_Std_CloseableChannel_sync(v_00_u03b1_4718_, v_ch_4719_);
lean_dec_ref(v_ch_4719_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4721_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l_Std_CloseableChannel_new___redArg(v_capacity_4721_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4724_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4727_, lean_object* v_capacity_4728_){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l_Std_CloseableChannel_new___redArg(v_capacity_4728_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4731_, lean_object* v_capacity_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4731_, v_capacity_4732_);
return v_res_4734_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4735_, lean_object* v_v_4736_){
_start:
{
uint8_t v___x_4738_; 
v___x_4738_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4735_, v_v_4736_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4739_, lean_object* v_v_4740_, lean_object* v_a_4741_){
_start:
{
uint8_t v_res_4742_; lean_object* v_r_4743_; 
v_res_4742_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4739_, v_v_4740_);
v_r_4743_ = lean_box(v_res_4742_);
return v_r_4743_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4744_, lean_object* v_ch_4745_, lean_object* v_v_4746_){
_start:
{
uint8_t v___x_4748_; 
v___x_4748_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4745_, v_v_4746_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4749_, lean_object* v_ch_4750_, lean_object* v_v_4751_, lean_object* v_a_4752_){
_start:
{
uint8_t v_res_4753_; lean_object* v_r_4754_; 
v_res_4753_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4749_, v_ch_4750_, v_v_4751_);
v_r_4754_ = lean_box(v_res_4753_);
return v_r_4754_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4755_, lean_object* v_v_4756_){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4758_ = l_Std_CloseableChannel_send___redArg(v_ch_4755_, v_v_4756_);
v___x_4759_ = lean_io_wait(v___x_4758_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4759_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4759_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
lean_ctor_set_tag(v___x_4762_, 1);
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4775_; 
v_a_4768_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4770_ = v___x_4759_;
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4759_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4773_; 
if (v_isShared_4771_ == 0)
{
lean_ctor_set_tag(v___x_4770_, 0);
v___x_4773_ = v___x_4770_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_a_4768_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_4776_, lean_object* v_v_4777_, lean_object* v_a_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4776_, v_v_4777_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_4780_, lean_object* v_ch_4781_, lean_object* v_v_4782_){
_start:
{
lean_object* v___x_4784_; 
v___x_4784_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4781_, v_v_4782_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_4785_, lean_object* v_ch_4786_, lean_object* v_v_4787_, lean_object* v_a_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_4785_, v_ch_4786_, v_v_4787_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_4790_){
_start:
{
lean_object* v___x_4792_; 
v___x_4792_ = l_Std_CloseableChannel_close___redArg(v_ch_4790_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_4793_, lean_object* v_a_4794_){
_start:
{
lean_object* v_res_4795_; 
v_res_4795_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_4793_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_4796_, lean_object* v_ch_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_Std_CloseableChannel_close___redArg(v_ch_4797_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_4800_, lean_object* v_ch_4801_, lean_object* v_a_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_4800_, v_ch_4801_);
return v_res_4803_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_4804_){
_start:
{
uint8_t v___x_4806_; 
v___x_4806_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_4807_, lean_object* v_a_4808_){
_start:
{
uint8_t v_res_4809_; lean_object* v_r_4810_; 
v_res_4809_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_4807_);
v_r_4810_ = lean_box(v_res_4809_);
return v_r_4810_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_4811_, lean_object* v_ch_4812_){
_start:
{
uint8_t v___x_4814_; 
v___x_4814_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4812_);
return v___x_4814_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_4815_, lean_object* v_ch_4816_, lean_object* v_a_4817_){
_start:
{
uint8_t v_res_4818_; lean_object* v_r_4819_; 
v_res_4818_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_4815_, v_ch_4816_);
v_r_4819_ = lean_box(v_res_4818_);
return v_r_4819_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_4820_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4820_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_4823_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_4826_, lean_object* v_ch_4827_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4827_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_4830_, lean_object* v_ch_4831_, lean_object* v_a_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_4830_, v_ch_4831_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_4834_){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4836_ = l_Std_CloseableChannel_recv___redArg(v_ch_4834_);
v___x_4837_ = lean_io_wait(v___x_4836_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4838_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_4841_, lean_object* v_ch_4842_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4842_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_4845_, lean_object* v_ch_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v_res_4848_; 
v_res_4848_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_4845_, v_ch_4846_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_4849_, lean_object* v_b_4850_, lean_object* v_f_4851_, lean_object* v_toBind_4852_, lean_object* v___f_4853_, lean_object* v_____do__lift_4854_){
_start:
{
if (lean_obj_tag(v_____do__lift_4854_) == 0)
{
lean_object* v___x_4855_; 
lean_dec(v___f_4853_);
lean_dec(v_toBind_4852_);
lean_dec(v_f_4851_);
v___x_4855_ = lean_apply_2(v_toPure_4849_, lean_box(0), v_b_4850_);
return v___x_4855_;
}
else
{
lean_object* v_val_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
lean_dec(v_toPure_4849_);
v_val_4856_ = lean_ctor_get(v_____do__lift_4854_, 0);
lean_inc(v_val_4856_);
lean_dec_ref_known(v_____do__lift_4854_, 1);
v___x_4857_ = lean_apply_2(v_f_4851_, v_val_4856_, v_b_4850_);
v___x_4858_ = lean_apply_4(v_toBind_4852_, lean_box(0), lean_box(0), v___x_4857_, v___f_4853_);
return v___x_4858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_4859_, lean_object* v_inst_4860_, lean_object* v_ch_4861_, lean_object* v_f_4862_, lean_object* v_b_4863_){
_start:
{
lean_object* v_toApplicative_4864_; lean_object* v_toBind_4865_; lean_object* v_toPure_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___f_4869_; lean_object* v___f_4870_; lean_object* v___x_4871_; 
v_toApplicative_4864_ = lean_ctor_get(v_inst_4859_, 0);
v_toBind_4865_ = lean_ctor_get(v_inst_4859_, 1);
lean_inc_n(v_toBind_4865_, 2);
v_toPure_4866_ = lean_ctor_get(v_toApplicative_4864_, 1);
lean_inc_n(v_toPure_4866_, 2);
lean_inc_ref(v_ch_4861_);
v___x_4867_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_4867_, 0, lean_box(0));
lean_closure_set(v___x_4867_, 1, v_ch_4861_);
lean_inc(v_inst_4860_);
v___x_4868_ = lean_apply_2(v_inst_4860_, lean_box(0), v___x_4867_);
lean_inc(v_f_4862_);
v___f_4869_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4869_, 0, v_toPure_4866_);
lean_closure_set(v___f_4869_, 1, v_inst_4859_);
lean_closure_set(v___f_4869_, 2, v_inst_4860_);
lean_closure_set(v___f_4869_, 3, v_ch_4861_);
lean_closure_set(v___f_4869_, 4, v_f_4862_);
v___f_4870_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_4870_, 0, v_toPure_4866_);
lean_closure_set(v___f_4870_, 1, v_b_4863_);
lean_closure_set(v___f_4870_, 2, v_f_4862_);
lean_closure_set(v___f_4870_, 3, v_toBind_4865_);
lean_closure_set(v___f_4870_, 4, v___f_4869_);
v___x_4871_ = lean_apply_4(v_toBind_4865_, lean_box(0), lean_box(0), v___x_4868_, v___f_4870_);
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_4872_, lean_object* v_inst_4873_, lean_object* v_inst_4874_, lean_object* v_ch_4875_, lean_object* v_f_4876_, lean_object* v_____do__lift_4877_){
_start:
{
if (lean_obj_tag(v_____do__lift_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4879_; 
lean_dec(v_f_4876_);
lean_dec_ref(v_ch_4875_);
lean_dec(v_inst_4874_);
lean_dec_ref(v_inst_4873_);
v_a_4878_ = lean_ctor_get(v_____do__lift_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v_____do__lift_4877_, 1);
v___x_4879_ = lean_apply_2(v_toPure_4872_, lean_box(0), v_a_4878_);
return v___x_4879_;
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4881_; 
lean_dec(v_toPure_4872_);
v_a_4880_ = lean_ctor_get(v_____do__lift_4877_, 0);
lean_inc(v_a_4880_);
lean_dec_ref_known(v_____do__lift_4877_, 1);
v___x_4881_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4873_, v_inst_4874_, v_ch_4875_, v_f_4876_, v_a_4880_);
return v___x_4881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_4882_, lean_object* v_00_u03b1_4883_, lean_object* v_00_u03b2_4884_, lean_object* v_inst_4885_, lean_object* v_inst_4886_, lean_object* v_ch_4887_, lean_object* v_f_4888_, lean_object* v_b_4889_){
_start:
{
lean_object* v___x_4890_; 
v___x_4890_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4885_, v_inst_4886_, v_ch_4887_, v_f_4888_, v_b_4889_);
return v___x_4890_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_4891_, lean_object* v_inst_4892_, lean_object* v_ch_4893_, lean_object* v_b_4894_, lean_object* v_f_4895_){
_start:
{
lean_object* v___x_4896_; 
v___x_4896_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4891_, v_inst_4892_, v_ch_4893_, v_f_4895_, v_b_4894_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_4897_, lean_object* v_00_u03b1_4898_, lean_object* v_inst_4899_, lean_object* v_inst_4900_, lean_object* v_00_u03b2_4901_, lean_object* v_ch_4902_, lean_object* v_b_4903_, lean_object* v_f_4904_){
_start:
{
lean_object* v___x_4905_; 
v___x_4905_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4899_, v_inst_4900_, v_ch_4902_, v_f_4904_, v_b_4903_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_4906_, lean_object* v_inst_4907_, lean_object* v_00_u03b2_4908_, lean_object* v_ch_4909_, lean_object* v_b_4910_, lean_object* v_f_4911_){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4906_, v_inst_4907_, v_ch_4909_, v_f_4911_, v_b_4910_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_4913_, lean_object* v_inst_4914_){
_start:
{
lean_object* v___f_4915_; 
v___f_4915_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4915_, 0, v_inst_4913_);
lean_closure_set(v___f_4915_, 1, v_inst_4914_);
return v___f_4915_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_4916_, lean_object* v_00_u03b1_4917_, lean_object* v_inst_4918_, lean_object* v_inst_4919_){
_start:
{
lean_object* v___f_4920_; 
v___f_4920_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4920_, 0, v_inst_4918_);
lean_closure_set(v___f_4920_, 1, v_inst_4919_);
return v___f_4920_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_4921_){
_start:
{
lean_object* v___x_4923_; 
v___x_4923_ = l_Std_CloseableChannel_new___redArg(v_capacity_4921_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Std_Channel_new___redArg(v_capacity_4924_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_4927_, lean_object* v_capacity_4928_){
_start:
{
lean_object* v___x_4930_; 
v___x_4930_ = l_Std_CloseableChannel_new___redArg(v_capacity_4928_);
return v___x_4930_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_4931_, lean_object* v_capacity_4932_, lean_object* v_a_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l_Std_Channel_new(v_00_u03b1_4931_, v_capacity_4932_);
return v_res_4934_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_4935_, lean_object* v_v_4936_){
_start:
{
uint8_t v___x_4938_; 
v___x_4938_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4935_, v_v_4936_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_4939_, lean_object* v_v_4940_, lean_object* v_a_4941_){
_start:
{
uint8_t v_res_4942_; lean_object* v_r_4943_; 
v_res_4942_ = l_Std_Channel_trySend___redArg(v_ch_4939_, v_v_4940_);
v_r_4943_ = lean_box(v_res_4942_);
return v_r_4943_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_4944_, lean_object* v_ch_4945_, lean_object* v_v_4946_){
_start:
{
uint8_t v___x_4948_; 
v___x_4948_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4945_, v_v_4946_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_4949_, lean_object* v_ch_4950_, lean_object* v_v_4951_, lean_object* v_a_4952_){
_start:
{
uint8_t v_res_4953_; lean_object* v_r_4954_; 
v_res_4953_ = l_Std_Channel_trySend(v_00_u03b1_4949_, v_ch_4950_, v_v_4951_);
v_r_4954_ = lean_box(v_res_4953_);
return v_r_4954_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4955_ = lean_box(0);
v___x_4956_ = lean_task_pure(v___x_4955_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_4957_){
_start:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_142__overap_4962_; lean_object* v___x_4963_; 
v___x_4959_ = l_instMonadBaseIO;
v___x_4960_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4961_ = l_instInhabitedOfMonad___redArg(v___x_4959_, v___x_4960_);
v___x_142__overap_4962_ = lean_panic_fn_borrowed(v___x_4961_, v_msg_4957_);
lean_dec(v___x_4961_);
v___x_4963_ = lean_apply_1(v___x_142__overap_4962_, lean_box(0));
return v___x_4963_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_4964_);
return v_res_4966_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4970_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4971_ = lean_unsigned_to_nat(21u);
v___x_4972_ = lean_unsigned_to_nat(869u);
v___x_4973_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_4974_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4975_ = l_mkPanicMessageWithDecl(v___x_4974_, v___x_4973_, v___x_4972_, v___x_4971_, v___x_4970_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_4976_){
_start:
{
if (lean_obj_tag(v_x_4976_) == 0)
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_4979_ = l_panic___at___00Std_Channel_send_spec__0(v___x_4978_);
return v___x_4979_;
}
else
{
lean_object* v___x_4980_; 
v___x_4980_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4980_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Std_Channel_send___redArg___lam__0(v_x_4981_);
lean_dec_ref(v_x_4981_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_4985_, lean_object* v_v_4986_){
_start:
{
lean_object* v___x_4988_; lean_object* v___f_4989_; lean_object* v___x_4990_; uint8_t v___x_4991_; lean_object* v___x_4992_; 
v___x_4988_ = l_Std_CloseableChannel_send___redArg(v_ch_4985_, v_v_4986_);
v___f_4989_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_4990_ = lean_unsigned_to_nat(0u);
v___x_4991_ = 1;
v___x_4992_ = lean_io_bind_task(v___x_4988_, v___f_4989_, v___x_4990_, v___x_4991_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_4993_, lean_object* v_v_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Std_Channel_send___redArg(v_ch_4993_, v_v_4994_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_4997_, lean_object* v_ch_4998_, lean_object* v_v_4999_){
_start:
{
lean_object* v___x_5001_; 
v___x_5001_ = l_Std_Channel_send___redArg(v_ch_4998_, v_v_4999_);
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_5002_, lean_object* v_ch_5003_, lean_object* v_v_5004_, lean_object* v_a_5005_){
_start:
{
lean_object* v_res_5006_; 
v_res_5006_ = l_Std_Channel_send(v_00_u03b1_5002_, v_ch_5003_, v_v_5004_);
return v_res_5006_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_5007_){
_start:
{
lean_object* v___x_5009_; 
v___x_5009_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5007_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_5010_, lean_object* v_a_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Std_Channel_tryRecv___redArg(v_ch_5010_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_5013_, lean_object* v_ch_5014_){
_start:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5014_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_5017_, lean_object* v_ch_5018_, lean_object* v_a_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Std_Channel_tryRecv(v_00_u03b1_5017_, v_ch_5018_);
return v_res_5020_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5022_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_5023_ = lean_unsigned_to_nat(16u);
v___x_5024_ = lean_unsigned_to_nat(880u);
v___x_5025_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_5026_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_5027_ = l_mkPanicMessageWithDecl(v___x_5026_, v___x_5025_, v___x_5024_, v___x_5023_, v___x_5022_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_5028_, lean_object* v_x_5029_){
_start:
{
if (lean_obj_tag(v_x_5029_) == 0)
{
lean_object* v___x_5031_; lean_object* v___x_140__overap_5032_; lean_object* v___x_5033_; 
v___x_5031_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_140__overap_5032_ = l_panic___redArg(v___x_5028_, v___x_5031_);
v___x_5033_ = lean_apply_1(v___x_140__overap_5032_, lean_box(0));
return v___x_5033_;
}
else
{
lean_object* v_val_5034_; lean_object* v___x_5035_; 
v_val_5034_ = lean_ctor_get(v_x_5029_, 0);
lean_inc(v_val_5034_);
lean_dec_ref_known(v_x_5029_, 1);
v___x_5035_ = lean_task_pure(v_val_5034_);
return v___x_5035_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_5036_, lean_object* v_x_5037_, lean_object* v___y_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l_Std_Channel_recv___redArg___lam__0(v___x_5036_, v_x_5037_);
lean_dec_ref(v___x_5036_);
return v_res_5039_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_5040_, lean_object* v_ch_5041_){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___f_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; lean_object* v___x_5050_; 
v___x_5043_ = l_instMonadBaseIO;
v___x_5044_ = l_Std_CloseableChannel_recv___redArg(v_ch_5041_);
v___x_5045_ = lean_task_pure(v_inst_5040_);
v___x_5046_ = l_instInhabitedOfMonad___redArg(v___x_5043_, v___x_5045_);
v___f_5047_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5047_, 0, v___x_5046_);
v___x_5048_ = lean_unsigned_to_nat(0u);
v___x_5049_ = 1;
v___x_5050_ = lean_io_bind_task(v___x_5044_, v___f_5047_, v___x_5048_, v___x_5049_);
return v___x_5050_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_5051_, lean_object* v_ch_5052_, lean_object* v_a_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Std_Channel_recv___redArg(v_inst_5051_, v_ch_5052_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_5055_, lean_object* v_inst_5056_, lean_object* v_ch_5057_){
_start:
{
lean_object* v___x_5059_; 
v___x_5059_ = l_Std_Channel_recv___redArg(v_inst_5056_, v_ch_5057_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_5060_, lean_object* v_inst_5061_, lean_object* v_ch_5062_, lean_object* v_a_5063_){
_start:
{
lean_object* v_res_5064_; 
v_res_5064_ = l_Std_Channel_recv(v_00_u03b1_5060_, v_inst_5061_, v_ch_5062_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_5065_){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5067_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5065_);
v___x_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
v___x_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5068_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_5070_, lean_object* v___y_5071_){
_start:
{
lean_object* v_res_5072_; 
v_res_5072_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5070_);
return v_res_5072_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5076_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_5077_ = lean_unsigned_to_nat(14u);
v___x_5078_ = lean_unsigned_to_nat(22u);
v___x_5079_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_5080_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_5081_ = l_mkPanicMessageWithDecl(v___x_5080_, v___x_5079_, v___x_5078_, v___x_5077_, v___x_5076_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_5082_, lean_object* v_inst_5083_, lean_object* v_x_5084_){
_start:
{
lean_object* v___y_5087_; lean_object* v___y_5091_; 
if (lean_obj_tag(v_x_5084_) == 0)
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = lean_box(0);
v___x_5094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
return v___x_5094_;
}
else
{
lean_object* v_val_5095_; 
v_val_5095_ = lean_ctor_get(v_x_5084_, 0);
lean_inc(v_val_5095_);
lean_dec_ref_known(v_x_5084_, 1);
if (lean_obj_tag(v_val_5095_) == 0)
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
v_a_5096_ = lean_ctor_get(v_val_5095_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v_val_5095_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v_val_5095_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v_val_5095_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5103_;
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
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5096_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
v___y_5087_ = v___x_5101_;
goto v___jp_5086_;
}
}
}
else
{
lean_object* v_a_5104_; 
v_a_5104_ = lean_ctor_get(v_val_5095_, 0);
lean_inc(v_a_5104_);
lean_dec_ref_known(v_val_5095_, 1);
if (lean_obj_tag(v_a_5104_) == 0)
{
lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5105_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5106_ = l_panic___redArg(v_inst_5083_, v___x_5105_);
v___y_5091_ = v___x_5106_;
goto v___jp_5090_;
}
else
{
lean_object* v_val_5107_; 
v_val_5107_ = lean_ctor_get(v_a_5104_, 0);
lean_inc(v_val_5107_);
lean_dec_ref_known(v_a_5104_, 1);
v___y_5091_ = v_val_5107_;
goto v___jp_5090_;
}
}
}
v___jp_5086_:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5088_ = lean_io_promise_resolve(v___y_5087_, v_promise_5082_);
v___x_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5089_, 0, v___x_5088_);
return v___x_5089_;
}
v___jp_5090_:
{
lean_object* v___x_5092_; 
v___x_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5092_, 0, v___y_5091_);
v___y_5087_ = v___x_5092_;
goto v___jp_5086_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5108_, lean_object* v_inst_5109_, lean_object* v_x_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5108_, v_inst_5109_, v_x_5110_);
lean_dec(v_inst_5109_);
lean_dec(v_promise_5108_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5113_, lean_object* v___f_5114_, lean_object* v_x_5115_){
_start:
{
lean_object* v_val_5118_; 
if (lean_obj_tag(v_x_5115_) == 0)
{
lean_object* v___x_5120_; 
lean_dec_ref(v___f_5114_);
v___x_5120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5120_, 0, v_x_5115_);
return v___x_5120_;
}
else
{
lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5136_; 
v_isSharedCheck_5136_ = !lean_is_exclusive(v_x_5115_);
if (v_isSharedCheck_5136_ == 0)
{
lean_object* v_unused_5137_; 
v_unused_5137_ = lean_ctor_get(v_x_5115_, 0);
lean_dec(v_unused_5137_);
v___x_5122_ = v_x_5115_;
v_isShared_5123_ = v_isSharedCheck_5136_;
goto v_resetjp_5121_;
}
else
{
lean_dec(v_x_5115_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5136_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5124_; lean_object* v___x_5125_; uint8_t v___x_5126_; lean_object* v___x_5127_; 
v___x_5124_ = lean_io_promise_result_opt(v_a_5113_);
v___x_5125_ = lean_unsigned_to_nat(0u);
v___x_5126_ = 1;
v___x_5127_ = l_EIO_chainTask___redArg(v___x_5124_, v___f_5114_, v___x_5125_, v___x_5126_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v___x_5130_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5128_);
lean_dec_ref_known(v___x_5127_, 1);
if (v_isShared_5123_ == 0)
{
lean_ctor_set(v___x_5122_, 0, v_a_5128_);
v___x_5130_ = v___x_5122_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5128_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
v_val_5118_ = v___x_5130_;
goto v___jp_5117_;
}
}
else
{
lean_object* v_a_5132_; lean_object* v___x_5134_; 
v_a_5132_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5132_);
lean_dec_ref_known(v___x_5127_, 1);
if (v_isShared_5123_ == 0)
{
lean_ctor_set_tag(v___x_5122_, 0);
lean_ctor_set(v___x_5122_, 0, v_a_5132_);
v___x_5134_ = v___x_5122_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5132_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
v_val_5118_ = v___x_5134_;
goto v___jp_5117_;
}
}
}
}
v___jp_5117_:
{
lean_object* v___x_5119_; 
v___x_5119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5119_, 0, v_val_5118_);
return v___x_5119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5138_, lean_object* v___f_5139_, lean_object* v_x_5140_, lean_object* v___y_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5138_, v___f_5139_, v_x_5140_);
lean_dec(v_a_5138_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5143_, lean_object* v_finished_5144_, lean_object* v___f_5145_, lean_object* v_x_5146_){
_start:
{
if (lean_obj_tag(v_x_5146_) == 0)
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5156_; 
lean_dec_ref(v___f_5145_);
lean_dec(v_finished_5144_);
lean_dec_ref(v_sel_5143_);
v_a_5148_ = lean_ctor_get(v_x_5146_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v_x_5146_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5150_ = v_x_5146_;
v_isShared_5151_ = v_isSharedCheck_5156_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v_x_5146_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5156_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5148_);
v___x_5153_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
lean_object* v___x_5154_; 
v___x_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5154_, 0, v___x_5153_);
return v___x_5154_;
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v_registerFn_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___f_5161_; lean_object* v___x_5162_; uint8_t v___x_5163_; lean_object* v___x_5164_; 
v_a_5157_ = lean_ctor_get(v_x_5146_, 0);
lean_inc_n(v_a_5157_, 2);
lean_dec_ref_known(v_x_5146_, 1);
v_registerFn_5158_ = lean_ctor_get(v_sel_5143_, 1);
lean_inc_ref(v_registerFn_5158_);
lean_dec_ref(v_sel_5143_);
v___x_5159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5159_, 0, v_finished_5144_);
lean_ctor_set(v___x_5159_, 1, v_a_5157_);
v___x_5160_ = lean_apply_2(v_registerFn_5158_, v___x_5159_, lean_box(0));
v___f_5161_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5161_, 0, v_a_5157_);
lean_closure_set(v___f_5161_, 1, v___f_5145_);
v___x_5162_ = lean_unsigned_to_nat(0u);
v___x_5163_ = 0;
v___x_5164_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5162_, v___x_5163_, v___x_5160_, v___f_5161_);
return v___x_5164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5165_, lean_object* v_finished_5166_, lean_object* v___f_5167_, lean_object* v_x_5168_, lean_object* v___y_5169_){
_start:
{
lean_object* v_res_5170_; 
v_res_5170_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5165_, v_finished_5166_, v___f_5167_, v_x_5168_);
return v_res_5170_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5171_, lean_object* v_sel_5172_, lean_object* v_waiter_5173_){
_start:
{
lean_object* v___x_5175_; lean_object* v_finished_5176_; lean_object* v_promise_5177_; lean_object* v___f_5178_; lean_object* v___f_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; lean_object* v___x_5184_; 
v___x_5175_ = lean_io_promise_new();
v_finished_5176_ = lean_ctor_get(v_waiter_5173_, 0);
lean_inc(v_finished_5176_);
v_promise_5177_ = lean_ctor_get(v_waiter_5173_, 1);
lean_inc(v_promise_5177_);
lean_dec_ref(v_waiter_5173_);
v___f_5178_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5178_, 0, v_promise_5177_);
lean_closure_set(v___f_5178_, 1, v_inst_5171_);
v___f_5179_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5179_, 0, v_sel_5172_);
lean_closure_set(v___f_5179_, 1, v_finished_5176_);
lean_closure_set(v___f_5179_, 2, v___f_5178_);
v___x_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5175_);
v___x_5181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5180_);
v___x_5182_ = lean_unsigned_to_nat(0u);
v___x_5183_ = 0;
v___x_5184_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5182_, v___x_5183_, v___x_5181_, v___f_5179_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5185_, lean_object* v_sel_5186_, lean_object* v_waiter_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5185_, v_sel_5186_, v_waiter_5187_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5190_, lean_object* v_ch_5191_){
_start:
{
lean_object* v_sel_5192_; lean_object* v_unregisterFn_5193_; lean_object* v___f_5194_; lean_object* v___f_5195_; lean_object* v___x_5196_; 
lean_inc_ref(v_ch_5191_);
v_sel_5192_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5191_);
v_unregisterFn_5193_ = lean_ctor_get(v_sel_5192_, 2);
lean_inc_ref(v_unregisterFn_5193_);
v___f_5194_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5194_, 0, v_ch_5191_);
v___f_5195_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5195_, 0, v_inst_5190_);
lean_closure_set(v___f_5195_, 1, v_sel_5192_);
v___x_5196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5196_, 0, v___f_5194_);
lean_ctor_set(v___x_5196_, 1, v___f_5195_);
lean_ctor_set(v___x_5196_, 2, v_unregisterFn_5193_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5197_, lean_object* v_inst_5198_, lean_object* v_ch_5199_){
_start:
{
lean_object* v___x_5200_; 
v___x_5200_ = l_Std_Channel_recvSelector___redArg(v_inst_5198_, v_ch_5199_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5201_, lean_object* v_inst_5202_, lean_object* v_ch_5203_, lean_object* v_prio_5204_, lean_object* v_v_5205_, lean_object* v___y_5206_){
_start:
{
lean_object* v_res_5207_; 
v_res_5207_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5201_, v_inst_5202_, v_ch_5203_, v_prio_5204_, v_v_5205_);
return v_res_5207_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5208_, lean_object* v_f_5209_, lean_object* v_ch_5210_, lean_object* v_prio_5211_){
_start:
{
lean_object* v___x_5213_; lean_object* v___f_5214_; uint8_t v___x_5215_; lean_object* v___x_5216_; 
lean_inc_ref(v_ch_5210_);
lean_inc(v_inst_5208_);
v___x_5213_ = l_Std_Channel_recv___redArg(v_inst_5208_, v_ch_5210_);
lean_inc(v_prio_5211_);
v___f_5214_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5214_, 0, v_f_5209_);
lean_closure_set(v___f_5214_, 1, v_inst_5208_);
lean_closure_set(v___f_5214_, 2, v_ch_5210_);
lean_closure_set(v___f_5214_, 3, v_prio_5211_);
v___x_5215_ = 0;
v___x_5216_ = lean_io_bind_task(v___x_5213_, v___f_5214_, v_prio_5211_, v___x_5215_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5217_, lean_object* v_inst_5218_, lean_object* v_ch_5219_, lean_object* v_prio_5220_, lean_object* v_v_5221_){
_start:
{
lean_object* v___x_5223_; lean_object* v___x_5224_; 
lean_inc_ref(v_f_5217_);
v___x_5223_ = lean_apply_2(v_f_5217_, v_v_5221_, lean_box(0));
v___x_5224_ = l_Std_Channel_forAsync___redArg(v_inst_5218_, v_f_5217_, v_ch_5219_, v_prio_5220_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5225_, lean_object* v_f_5226_, lean_object* v_ch_5227_, lean_object* v_prio_5228_, lean_object* v_a_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l_Std_Channel_forAsync___redArg(v_inst_5225_, v_f_5226_, v_ch_5227_, v_prio_5228_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5231_, lean_object* v_inst_5232_, lean_object* v_f_5233_, lean_object* v_ch_5234_, lean_object* v_prio_5235_){
_start:
{
lean_object* v___x_5237_; 
v___x_5237_ = l_Std_Channel_forAsync___redArg(v_inst_5232_, v_f_5233_, v_ch_5234_, v_prio_5235_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5238_, lean_object* v_inst_5239_, lean_object* v_f_5240_, lean_object* v_ch_5241_, lean_object* v_prio_5242_, lean_object* v_a_5243_){
_start:
{
lean_object* v_res_5244_; 
v_res_5244_ = l_Std_Channel_forAsync(v_00_u03b1_5238_, v_inst_5239_, v_f_5240_, v_ch_5241_, v_prio_5242_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5245_, lean_object* v_channel_5246_){
_start:
{
lean_object* v___x_5247_; 
v___x_5247_ = l_Std_Channel_recvSelector___redArg(v_inst_5245_, v_channel_5246_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5248_){
_start:
{
lean_object* v___f_5249_; lean_object* v___f_5250_; lean_object* v___x_5251_; 
v___f_5249_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5249_, 0, v_inst_5248_);
v___f_5250_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1));
v___x_5251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5251_, 0, v___f_5249_);
lean_ctor_set(v___x_5251_, 1, v___f_5250_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5252_, lean_object* v_inst_5253_){
_start:
{
lean_object* v___x_5254_; 
v___x_5254_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5253_);
return v___x_5254_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5255_){
_start:
{
lean_object* v___x_5256_; 
v___x_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5256_, 0, v_a_5255_);
return v___x_5256_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5257_, lean_object* v_x_5258_){
_start:
{
if (lean_obj_tag(v_x_5258_) == 0)
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5268_; 
lean_dec_ref(v___f_5257_);
v_a_5260_ = lean_ctor_get(v_x_5258_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v_x_5258_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5262_ = v_x_5258_;
v_isShared_5263_ = v_isSharedCheck_5268_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v_x_5258_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5268_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
lean_object* v___x_5266_; 
v___x_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5265_);
return v___x_5266_;
}
}
}
else
{
lean_object* v_a_5269_; 
v_a_5269_ = lean_ctor_get(v_x_5258_, 0);
lean_inc(v_a_5269_);
lean_dec_ref_known(v_x_5258_, 1);
if (lean_obj_tag(v_a_5269_) == 0)
{
lean_object* v_a_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5278_; 
lean_dec_ref(v___f_5257_);
v_a_5270_ = lean_ctor_get(v_a_5269_, 0);
v_isSharedCheck_5278_ = !lean_is_exclusive(v_a_5269_);
if (v_isSharedCheck_5278_ == 0)
{
v___x_5272_ = v_a_5269_;
v_isShared_5273_ = v_isSharedCheck_5278_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_a_5270_);
lean_dec(v_a_5269_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5278_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5275_; 
if (v_isShared_5273_ == 0)
{
v___x_5275_ = v___x_5272_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5270_);
v___x_5275_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
lean_object* v___x_5276_; 
v___x_5276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5276_, 0, v___x_5275_);
return v___x_5276_;
}
}
}
else
{
lean_object* v_a_5279_; lean_object* v___x_5280_; uint8_t v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v_a_5279_ = lean_ctor_get(v_a_5269_, 0);
lean_inc(v_a_5279_);
lean_dec_ref_known(v_a_5269_, 1);
v___x_5280_ = lean_unsigned_to_nat(0u);
v___x_5281_ = 0;
v___x_5282_ = lean_task_map(v___f_5257_, v_a_5279_, v___x_5280_, v___x_5281_);
v___x_5283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5282_);
return v___x_5283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5284_, lean_object* v_x_5285_, lean_object* v___y_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5284_, v_x_5285_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5288_, lean_object* v___f_5289_, lean_object* v_receiver_5290_){
_start:
{
lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; uint8_t v___x_5297_; lean_object* v___x_5298_; 
v___x_5292_ = l_Std_Channel_recv___redArg(v_inst_5288_, v_receiver_5290_);
v___x_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
v___x_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
v___x_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5294_);
v___x_5296_ = lean_unsigned_to_nat(0u);
v___x_5297_ = 0;
v___x_5298_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5296_, v___x_5297_, v___x_5295_, v___f_5289_);
return v___x_5298_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5299_, lean_object* v___f_5300_, lean_object* v_receiver_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5299_, v___f_5300_, v_receiver_5301_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5307_){
_start:
{
lean_object* v___f_5308_; lean_object* v___f_5309_; 
v___f_5308_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5309_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5309_, 0, v_inst_5307_);
lean_closure_set(v___f_5309_, 1, v___f_5308_);
return v___f_5309_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5310_, lean_object* v_inst_5311_){
_start:
{
lean_object* v___x_5312_; 
v___x_5312_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5311_);
return v___x_5312_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__0(lean_object* v_a_5313_){
_start:
{
lean_object* v___x_5314_; 
v___x_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5314_, 0, v_a_5313_);
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_5315_, lean_object* v_x_5316_){
_start:
{
if (lean_obj_tag(v_x_5316_) == 0)
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5326_; 
lean_dec_ref(v___f_5315_);
v_a_5318_ = lean_ctor_get(v_x_5316_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v_x_5316_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5320_ = v_x_5316_;
v_isShared_5321_ = v_isSharedCheck_5326_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v_x_5316_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5326_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5318_);
v___x_5323_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
lean_object* v___x_5324_; 
v___x_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5323_);
return v___x_5324_;
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5328_; uint8_t v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; 
v_a_5327_ = lean_ctor_get(v_x_5316_, 0);
lean_inc(v_a_5327_);
lean_dec_ref_known(v_x_5316_, 1);
v___x_5328_ = lean_unsigned_to_nat(0u);
v___x_5329_ = 0;
v___x_5330_ = lean_task_map(v___f_5315_, v_a_5327_, v___x_5328_, v___x_5329_);
v___x_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5330_);
return v___x_5331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_5332_, lean_object* v_x_5333_, lean_object* v___y_5334_){
_start:
{
lean_object* v_res_5335_; 
v_res_5335_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__1(v___f_5332_, v_x_5333_);
return v_res_5335_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5336_, lean_object* v_receiver_5337_, lean_object* v_x_5338_){
_start:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; uint8_t v___x_5344_; lean_object* v___x_5345_; 
v___x_5340_ = l_Std_Channel_send___redArg(v_receiver_5337_, v_x_5338_);
v___x_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5340_);
v___x_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5342_, 0, v___x_5341_);
v___x_5343_ = lean_unsigned_to_nat(0u);
v___x_5344_ = 0;
v___x_5345_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5343_, v___x_5344_, v___x_5342_, v___f_5336_);
return v___x_5345_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5346_, lean_object* v_receiver_5347_, lean_object* v_x_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__2(v___f_5346_, v_receiver_5347_, v_x_5348_);
return v_res_5350_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_5356_; lean_object* v___f_5357_; lean_object* v___f_5358_; 
v___x_5356_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_5357_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___f_5358_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5358_, 0, v___f_5357_);
lean_closure_set(v___f_5358_, 1, v___x_5356_);
return v___f_5358_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___f_5359_; lean_object* v___f_5360_; lean_object* v___f_5361_; lean_object* v___x_5362_; 
v___f_5359_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_5360_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3);
v___f_5361_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___x_5362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5362_, 0, v___f_5361_);
lean_ctor_set(v___x_5362_, 1, v___f_5360_);
lean_ctor_set(v___x_5362_, 2, v___f_5359_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5363_, lean_object* v_inst_5364_){
_start:
{
lean_object* v___x_5365_; 
v___x_5365_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4);
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5366_, lean_object* v_inst_5367_){
_start:
{
lean_object* v_res_5368_; 
v_res_5368_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_5366_, v_inst_5367_);
lean_dec(v_inst_5367_);
return v_res_5368_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object* v_ch_5369_){
_start:
{
lean_inc_ref(v_ch_5369_);
return v_ch_5369_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object* v_ch_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l_Std_Channel_sync___redArg(v_ch_5370_);
lean_dec_ref(v_ch_5370_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object* v_00_u03b1_5372_, lean_object* v_ch_5373_){
_start:
{
lean_inc_ref(v_ch_5373_);
return v_ch_5373_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object* v_00_u03b1_5374_, lean_object* v_ch_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Std_Channel_sync(v_00_u03b1_5374_, v_ch_5375_);
lean_dec_ref(v_ch_5375_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg(lean_object* v_capacity_5377_){
_start:
{
lean_object* v___x_5379_; 
v___x_5379_ = l_Std_CloseableChannel_new___redArg(v_capacity_5377_);
return v___x_5379_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object* v_capacity_5380_, lean_object* v_a_5381_){
_start:
{
lean_object* v_res_5382_; 
v_res_5382_ = l_Std_Channel_Sync_new___redArg(v_capacity_5380_);
return v_res_5382_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new(lean_object* v_00_u03b1_5383_, lean_object* v_capacity_5384_){
_start:
{
lean_object* v___x_5386_; 
v___x_5386_ = l_Std_CloseableChannel_new___redArg(v_capacity_5384_);
return v___x_5386_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object* v_00_u03b1_5387_, lean_object* v_capacity_5388_, lean_object* v_a_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l_Std_Channel_Sync_new(v_00_u03b1_5387_, v_capacity_5388_);
return v_res_5390_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object* v_ch_5391_, lean_object* v_v_5392_){
_start:
{
uint8_t v___x_5394_; 
v___x_5394_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5391_, v_v_5392_);
return v___x_5394_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object* v_ch_5395_, lean_object* v_v_5396_, lean_object* v_a_5397_){
_start:
{
uint8_t v_res_5398_; lean_object* v_r_5399_; 
v_res_5398_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5395_, v_v_5396_);
v_r_5399_ = lean_box(v_res_5398_);
return v_r_5399_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend(lean_object* v_00_u03b1_5400_, lean_object* v_ch_5401_, lean_object* v_v_5402_){
_start:
{
uint8_t v___x_5404_; 
v___x_5404_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5401_, v_v_5402_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object* v_00_u03b1_5405_, lean_object* v_ch_5406_, lean_object* v_v_5407_, lean_object* v_a_5408_){
_start:
{
uint8_t v_res_5409_; lean_object* v_r_5410_; 
v_res_5409_ = l_Std_Channel_Sync_trySend(v_00_u03b1_5405_, v_ch_5406_, v_v_5407_);
v_r_5410_ = lean_box(v_res_5409_);
return v_r_5410_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg(lean_object* v_ch_5411_, lean_object* v_v_5412_){
_start:
{
lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5414_ = l_Std_Channel_send___redArg(v_ch_5411_, v_v_5412_);
v___x_5415_ = lean_io_wait(v___x_5414_);
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object* v_ch_5416_, lean_object* v_v_5417_, lean_object* v_a_5418_){
_start:
{
lean_object* v_res_5419_; 
v_res_5419_ = l_Std_Channel_Sync_send___redArg(v_ch_5416_, v_v_5417_);
return v_res_5419_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send(lean_object* v_00_u03b1_5420_, lean_object* v_ch_5421_, lean_object* v_v_5422_){
_start:
{
lean_object* v___x_5424_; 
v___x_5424_ = l_Std_Channel_Sync_send___redArg(v_ch_5421_, v_v_5422_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object* v_00_u03b1_5425_, lean_object* v_ch_5426_, lean_object* v_v_5427_, lean_object* v_a_5428_){
_start:
{
lean_object* v_res_5429_; 
v_res_5429_ = l_Std_Channel_Sync_send(v_00_u03b1_5425_, v_ch_5426_, v_v_5427_);
return v_res_5429_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object* v_ch_5430_){
_start:
{
lean_object* v___x_5432_; 
v___x_5432_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5430_);
return v___x_5432_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5433_, lean_object* v_a_5434_){
_start:
{
lean_object* v_res_5435_; 
v_res_5435_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5433_);
return v_res_5435_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv(lean_object* v_00_u03b1_5436_, lean_object* v_ch_5437_){
_start:
{
lean_object* v___x_5439_; 
v___x_5439_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5437_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5440_, lean_object* v_ch_5441_, lean_object* v_a_5442_){
_start:
{
lean_object* v_res_5443_; 
v_res_5443_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_5440_, v_ch_5441_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg(lean_object* v_inst_5444_, lean_object* v_ch_5445_){
_start:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5447_ = l_Std_Channel_recv___redArg(v_inst_5444_, v_ch_5445_);
v___x_5448_ = lean_io_wait(v___x_5447_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object* v_inst_5449_, lean_object* v_ch_5450_, lean_object* v_a_5451_){
_start:
{
lean_object* v_res_5452_; 
v_res_5452_ = l_Std_Channel_Sync_recv___redArg(v_inst_5449_, v_ch_5450_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv(lean_object* v_00_u03b1_5453_, lean_object* v_inst_5454_, lean_object* v_ch_5455_){
_start:
{
lean_object* v___x_5457_; 
v___x_5457_ = l_Std_Channel_Sync_recv___redArg(v_inst_5454_, v_ch_5455_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object* v_00_u03b1_5458_, lean_object* v_inst_5459_, lean_object* v_ch_5460_, lean_object* v_a_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Std_Channel_Sync_recv(v_00_u03b1_5458_, v_inst_5459_, v_ch_5460_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object* v_f_5463_, lean_object* v_b_5464_, lean_object* v_toBind_5465_, lean_object* v___f_5466_, lean_object* v_a_5467_){
_start:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5468_ = lean_apply_2(v_f_5463_, v_a_5467_, v_b_5464_);
v___x_5469_ = lean_apply_4(v_toBind_5465_, lean_box(0), lean_box(0), v___x_5468_, v___f_5466_);
return v___x_5469_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object* v_inst_5470_, lean_object* v_inst_5471_, lean_object* v_inst_5472_, lean_object* v_ch_5473_, lean_object* v_f_5474_, lean_object* v_b_5475_){
_start:
{
lean_object* v_toApplicative_5476_; lean_object* v_toBind_5477_; lean_object* v_toPure_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___f_5481_; lean_object* v___f_5482_; lean_object* v___x_5483_; 
v_toApplicative_5476_ = lean_ctor_get(v_inst_5471_, 0);
v_toBind_5477_ = lean_ctor_get(v_inst_5471_, 1);
lean_inc_n(v_toBind_5477_, 2);
v_toPure_5478_ = lean_ctor_get(v_toApplicative_5476_, 1);
lean_inc(v_toPure_5478_);
lean_inc_ref(v_ch_5473_);
lean_inc(v_inst_5470_);
v___x_5479_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_recv___boxed), 4, 3);
lean_closure_set(v___x_5479_, 0, lean_box(0));
lean_closure_set(v___x_5479_, 1, v_inst_5470_);
lean_closure_set(v___x_5479_, 2, v_ch_5473_);
lean_inc(v_inst_5472_);
v___x_5480_ = lean_apply_2(v_inst_5472_, lean_box(0), v___x_5479_);
lean_inc(v_f_5474_);
v___f_5481_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5481_, 0, v_toPure_5478_);
lean_closure_set(v___f_5481_, 1, v_inst_5470_);
lean_closure_set(v___f_5481_, 2, v_inst_5471_);
lean_closure_set(v___f_5481_, 3, v_inst_5472_);
lean_closure_set(v___f_5481_, 4, v_ch_5473_);
lean_closure_set(v___f_5481_, 5, v_f_5474_);
v___f_5482_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1), 5, 4);
lean_closure_set(v___f_5482_, 0, v_f_5474_);
lean_closure_set(v___f_5482_, 1, v_b_5475_);
lean_closure_set(v___f_5482_, 2, v_toBind_5477_);
lean_closure_set(v___f_5482_, 3, v___f_5481_);
v___x_5483_ = lean_apply_4(v_toBind_5477_, lean_box(0), lean_box(0), v___x_5480_, v___f_5482_);
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5484_, lean_object* v_inst_5485_, lean_object* v_inst_5486_, lean_object* v_inst_5487_, lean_object* v_ch_5488_, lean_object* v_f_5489_, lean_object* v_____do__lift_5490_){
_start:
{
if (lean_obj_tag(v_____do__lift_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v___x_5492_; 
lean_dec(v_f_5489_);
lean_dec_ref(v_ch_5488_);
lean_dec(v_inst_5487_);
lean_dec_ref(v_inst_5486_);
lean_dec(v_inst_5485_);
v_a_5491_ = lean_ctor_get(v_____do__lift_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref_known(v_____do__lift_5490_, 1);
v___x_5492_ = lean_apply_2(v_toPure_5484_, lean_box(0), v_a_5491_);
return v___x_5492_;
}
else
{
lean_object* v_a_5493_; lean_object* v___x_5494_; 
lean_dec(v_toPure_5484_);
v_a_5493_ = lean_ctor_get(v_____do__lift_5490_, 0);
lean_inc(v_a_5493_);
lean_dec_ref_known(v_____do__lift_5490_, 1);
v___x_5494_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5485_, v_inst_5486_, v_inst_5487_, v_ch_5488_, v_f_5489_, v_a_5493_);
return v___x_5494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object* v_00_u03b1_5495_, lean_object* v_m_5496_, lean_object* v_00_u03b2_5497_, lean_object* v_inst_5498_, lean_object* v_inst_5499_, lean_object* v_inst_5500_, lean_object* v_ch_5501_, lean_object* v_f_5502_, lean_object* v_b_5503_){
_start:
{
lean_object* v___x_5504_; 
v___x_5504_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5498_, v_inst_5499_, v_inst_5500_, v_ch_5501_, v_f_5502_, v_b_5503_);
return v___x_5504_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5505_, lean_object* v_inst_5506_, lean_object* v_inst_5507_, lean_object* v_ch_5508_, lean_object* v_b_5509_, lean_object* v_f_5510_){
_start:
{
lean_object* v___x_5511_; 
v___x_5511_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5505_, v_inst_5506_, v_inst_5507_, v_ch_5508_, v_f_5510_, v_b_5509_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_00_u03b1_5512_, lean_object* v_m_5513_, lean_object* v_inst_5514_, lean_object* v_inst_5515_, lean_object* v_inst_5516_, lean_object* v_00_u03b2_5517_, lean_object* v_ch_5518_, lean_object* v_b_5519_, lean_object* v_f_5520_){
_start:
{
lean_object* v___x_5521_; 
v___x_5521_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5514_, v_inst_5515_, v_inst_5516_, v_ch_5518_, v_f_5520_, v_b_5519_);
return v___x_5521_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5522_, lean_object* v_inst_5523_, lean_object* v_inst_5524_, lean_object* v_00_u03b2_5525_, lean_object* v_ch_5526_, lean_object* v_b_5527_, lean_object* v_f_5528_){
_start:
{
lean_object* v___x_5529_; 
v___x_5529_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5522_, v_inst_5523_, v_inst_5524_, v_ch_5526_, v_f_5528_, v_b_5527_);
return v___x_5529_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5530_, lean_object* v_inst_5531_, lean_object* v_inst_5532_){
_start:
{
lean_object* v___f_5533_; 
v___f_5533_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5533_, 0, v_inst_5530_);
lean_closure_set(v___f_5533_, 1, v_inst_5531_);
lean_closure_set(v___f_5533_, 2, v_inst_5532_);
return v___f_5533_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5534_, lean_object* v_m_5535_, lean_object* v_inst_5536_, lean_object* v_inst_5537_, lean_object* v_inst_5538_){
_start:
{
lean_object* v___f_5539_; 
v___f_5539_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5539_, 0, v_inst_5536_);
lean_closure_set(v___f_5539_, 1, v_inst_5537_);
lean_closure_set(v___f_5539_, 2, v_inst_5538_);
return v___f_5539_;
}
}
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Channel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
